use bellman::pairing::Engine;
use bignat::hash::circuit::CircuitHasher;
use bignat::hash::Hasher;
use sapling_crypto::bellman::{
  Circuit, ConstraintSystem, SynthesisError, Variable,
};
use sapling_crypto::circuit::{boolean, ecc, num, Assignment};
use sapling_crypto::jubjub::{JubjubEngine, JubjubParams, PrimeOrder};

pub trait AllocatedMember<E: JubjubEngine>: Clone {
  fn as_vec<CS: ConstraintSystem<E>>(
    &self,
    cs: CS,
  ) -> Result<Vec<num::AllocatedNum<E>>, SynthesisError>;
}

pub trait MerkleHasher<E: JubjubEngine>: Clone {
  fn hash_to_leaf<CS: ConstraintSystem<E>>(
    &self,
    cs: CS,
    raw: Vec<num::AllocatedNum<E>>,
  ) -> Result<num::AllocatedNum<E>, SynthesisError>;

  fn hash_couple<CS: ConstraintSystem<E>>(
    &self,
    cs: CS,
    xl: &num::AllocatedNum<E>,
    xr: &num::AllocatedNum<E>,
  ) -> Result<num::AllocatedNum<E>, SynthesisError>;
}

pub struct MembershipCircuit<E, H>
where
  E: JubjubEngine,
  H: MerkleHasher<E>,
{
  hasher: H,
  leaf: num::AllocatedNum<E>,
  root: num::AllocatedNum<E>,
  witness: Vec<(num::AllocatedNum<E>, boolean::Boolean)>,
}

#[allow(dead_code)]
impl<E, H> MembershipCircuit<E, H>
where
  E: JubjubEngine,
  H: MerkleHasher<E>,
{
  // pub fn alloc<CS: ConstraintSystem<E>, M: AllocatedMember<E>>(
  pub fn alloc<CS: ConstraintSystem<E>, M: AllocatedMember<E>>(
    mut cs: CS,
    hasher: H,
    root: Option<E::Fr>,
    member: M,
    witness: Vec<Option<(E::Fr, bool)>>,
  ) -> Result<Self, SynthesisError> {
    let root = num::AllocatedNum::alloc(cs.namespace(|| "root"), || {
      let value = root.clone();
      Ok(*value.get()?)
    })?;
    root.inputize(cs.namespace(|| "root public input"))?;

    let mut allocated_witness: Vec<(num::AllocatedNum<E>, boolean::Boolean)> =
      Vec::with_capacity(witness.len());
    for (i, e) in witness.into_iter().enumerate() {
      let cs = &mut cs.namespace(|| format!("witness {}", i));
      let position = boolean::Boolean::from(boolean::AllocatedBit::alloc(
        cs.namespace(|| "position bit"),
        e.map(|e| e.1),
      )?);
      let path_element =
        num::AllocatedNum::alloc(cs.namespace(|| "path element"), || {
          Ok(e.get()?.0)
        })?;
      allocated_witness.push((path_element, position));
    }
    let ser = member.as_vec(cs.namespace(|| "raw member"))?;
    let leaf = hasher.hash_to_leaf(cs.namespace(|| "hash to leaf"), ser)?;
    Ok(Self {
      hasher,
      leaf,
      root,
      witness: allocated_witness,
    })
  }
  pub fn check_inclusion<CS: ConstraintSystem<E>>(
    &mut self,
    mut cs: CS,
  ) -> Result<(), SynthesisError> {
    // accumulator up to the root
    let mut acc = self.leaf.clone();
    // ascend the tree
    // taken from sapling circuit
    // https://github.com/zcash-hackworks/sapling-crypto/blob/49017b4e055ba4322dad1f03fe7d80dc0ed449cc/src/circuit/sapling/mod.rs#L353
    for (i, e) in self.witness.iter().enumerate() {
      let cs = &mut cs.namespace(|| format!("merkle tree hash {}", i));

      let position = e.1.clone();
      let path_element = e.0.clone();
      let (xr, xl) = num::AllocatedNum::conditionally_reverse(
        cs.namespace(|| "conditional reversal of preimage"),
        &acc,
        &path_element,
        &position,
      )?;
      acc =
        self
          .hasher
          .hash_couple(cs.namespace(|| "hash couple"), &xl, &xr)?;
    }

    cs.enforce(
      || "enforce membership",
      |lc| lc + acc.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + self.root.get_variable(),
    );
    Ok(())
  }
}

#[cfg(test)]
mod test {
  use super::{AllocatedMember, MembershipCircuit, MerkleHasher};
  use bignat::hash::Hasher;
  use rand::{Rand, SeedableRng, XorShiftRng};
  use sapling_crypto::bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key,
    verify_proof,
  };
  use sapling_crypto::bellman::pairing::ff::{
    Field, PrimeField, PrimeFieldRepr,
  };
  use sapling_crypto::bellman::pairing::Engine;
  use sapling_crypto::bellman::Circuit;
  use sapling_crypto::circuit::test::TestConstraintSystem;

  const MERKLE_DEPTH: usize = 3;

  mod single {
    use super::super::MembershipCircuit;
    use super::super::MerkleHasher;
    use sapling_crypto::bellman::{
      Circuit, ConstraintSystem, SynthesisError, Variable,
    };
    use sapling_crypto::circuit::{boolean, ecc, num, Assignment};
    use sapling_crypto::jubjub::JubjubEngine;

    #[derive(Clone)]
    pub struct SingleAllocatedMember<E: JubjubEngine> {
      m: num::AllocatedNum<E>,
    }

    impl<E> super::AllocatedMember<E> for SingleAllocatedMember<E>
    where
      E: JubjubEngine,
    {
      fn as_vec<CS: ConstraintSystem<E>>(
        &self,
        cs: CS,
      ) -> Result<Vec<num::AllocatedNum<E>>, SynthesisError> {
        Ok(vec![self.m.clone()])
      }
    }

    impl<E> SingleAllocatedMember<E>
    where
      E: JubjubEngine,
    {
      fn alloc<CS: ConstraintSystem<E>>(
        mut cs: CS,
        member: Option<E::Fr>,
      ) -> Result<Self, SynthesisError> {
        let m = num::AllocatedNum::alloc(cs.namespace(|| "root"), || {
          let value = member.clone();
          Ok(*value.get()?)
        })?;
        Ok(Self { m })
      }
    }

    #[derive(Clone)]
    pub struct MembershipInputs<E>
    where
      E: JubjubEngine,
    {
      // state root of the set
      pub root: Option<E::Fr>,
      // claimed member in the set
      pub member: Option<E::Fr>,
      // authentication path of the member
      pub witness: Vec<Option<(E::Fr, bool)>>,
    }

    #[derive(Clone)]
    pub struct MembershipSnark<E, H>
    where
      E: JubjubEngine,
      H: MerkleHasher<E>,
    {
      pub inputs: MembershipInputs<E>,
      pub hasher: H,
    }

    impl<E, H> Circuit<E> for MembershipSnark<E, H>
    where
      E: JubjubEngine,
      H: MerkleHasher<E>,
    {
      fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
      ) -> Result<(), SynthesisError> {
        let allocated_member = SingleAllocatedMember::alloc(
          cs.namespace(|| "alloc member"),
          self.inputs.member,
        )?;
        let mut membership_circuit = MembershipCircuit::alloc(
          cs.namespace(|| "alloc membership circuit"),
          self.hasher,
          self.inputs.root,
          allocated_member,
          self.inputs.witness,
        )?;
        membership_circuit
          .check_inclusion(cs.namespace(|| "check inclution"))?;
        Ok(())
      }
    }
  }

  mod bignat_hasher {

    use super::super::MerkleHasher as GenericMerkleHasher;
    use bignat::hash::circuit::CircuitHasher;
    use bignat::hash::hashes::Poseidon;
    use bignat::hash::Hasher;
    use sapling_crypto::bellman::pairing::bls12_381::Bls12;
    use sapling_crypto::bellman::pairing::bn256::Bn256;
    use sapling_crypto::bellman::{ConstraintSystem, SynthesisError};
    use sapling_crypto::circuit::{boolean, ecc, num, Assignment};
    use sapling_crypto::jubjub::JubjubEngine;

    #[derive(Clone)]
    pub struct MerkleHasher<E, H>
    where
      E: JubjubEngine,
      H: CircuitHasher<E = E> + Hasher<F = E::Fr> + Clone,
    {
      hasher: H,
    }

    use super::MerkleTree;
    impl<E, H> MerkleHasher<E, H>
    where
      E: JubjubEngine,
      H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    {
      pub fn empty(&self, depth: usize) -> MerkleTree<H> {
        MerkleTree::empty(self.hasher.clone(), depth)
      }
    }

    impl MerkleHasher<Bls12, Poseidon<Bls12>> {
      pub fn poseidon_bls12() -> Self {
        Self {
          hasher: Poseidon::<Bls12>::default(),
        }
      }
    }

    impl MerkleHasher<Bn256, Poseidon<Bn256>> {
      pub fn poseidon_bn256() -> Self {
        Self {
          hasher: Poseidon::<Bn256>::default(),
        }
      }
    }

    impl<E, H> GenericMerkleHasher<E> for MerkleHasher<E, H>
    where
      E: JubjubEngine,
      H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
    {
      fn hash_to_leaf<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        raw: Vec<num::AllocatedNum<E>>,
      ) -> Result<num::AllocatedNum<E>, SynthesisError> {
        self
          .hasher
          .allocate_hash(cs.namespace(|| "hash_to_leaf"), raw.as_slice())
      }
      fn hash_couple<CS: ConstraintSystem<E>>(
        &self,
        mut cs: CS,
        xl: &num::AllocatedNum<E>,
        xr: &num::AllocatedNum<E>,
      ) -> Result<num::AllocatedNum<E>, SynthesisError> {
        self
          .hasher
          .allocate_hash2(cs.namespace(|| "hash_to_leaf"), xl, xr)
      }
    }
  }

  #[test]
  fn test_merkle_circuit_bls12() {
    use bignat::hash::hashes::Poseidon;
    use bignat_hasher::MerkleHasher;
    use sapling_crypto::bellman::pairing::bls12_381::{Bls12, Fr};
    use single::{MembershipInputs, MembershipSnark};
    let mut rng =
      XorShiftRng::from_seed([0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let mut cs = TestConstraintSystem::<Bls12>::new();

    // let hasher = Poseidon::<Bls12>::default();
    let merkle_hasher = MerkleHasher::poseidon_bls12();
    // prepare an empty set
    let mut merkle_tree = merkle_hasher.empty(MERKLE_DEPTH);

    // insert a member
    let member = Fr::from_str("11").unwrap();
    let leaf_index = 6;
    merkle_tree.update(leaf_index, member, None);
    // take the root and the witness for this member
    let witness = merkle_tree.witness(leaf_index);
    let root = merkle_tree.root();

    let inputs = MembershipInputs {
      root: Some(root),
      member: Some(member),
      witness: witness.into_iter().map(|w| Some(w)).collect(),
    };

    let instance = MembershipSnark {
      inputs: inputs,
      hasher: merkle_hasher.clone(),
    };

    {
      let instance = instance.clone();
      instance.synthesize(&mut cs).unwrap();
      let unsatisfied = cs.which_is_unsatisfied();
      if unsatisfied.is_some() {
        panic!("unsatisfied\n{}", unsatisfied.unwrap());
      }
      let unconstrained = cs.find_unconstrained();
      if !unconstrained.is_empty() {
        panic!("unconst\n{}", unconstrained);
      }
      assert!(cs.is_satisfied());
    }

    let public_inputs = vec![root];
    let circuit_parameters = {
      let input = MembershipInputs::<Bls12> {
        root: None,
        member: None,
        witness: vec![None; MERKLE_DEPTH],
      };
      let empty_circuit = MembershipSnark {
        inputs: input,
        hasher: merkle_hasher.clone(),
      };
      generate_random_parameters(empty_circuit, &mut rng).unwrap()
    };

    let verifing_key = prepare_verifying_key(&circuit_parameters.vk);
    let proof =
      create_random_proof(instance, &circuit_parameters, &mut rng).unwrap();
    let is_valid = verify_proof(&verifing_key, &proof, &public_inputs).unwrap();
    assert!(is_valid);
  }

  #[test]
  #[ignore]
  fn test_merkle_set() {
    let zero = Some(Fr::zero());
    let data: Vec<Fr> = (0..8)
      .map(|s| Fr::from_str(&format!("{}", s)).unwrap())
      .collect();
    use bignat::hash::hashes::Poseidon;
    use sapling_crypto::bellman::pairing::bls12_381::{Bls12, Fr, FrRepr};
    let hasher = Poseidon::<Bls12>::default();
    let mut m = MerkleTree::empty(hasher.clone(), MERKLE_DEPTH);
    let leaf_index = 6;
    m.update(leaf_index, data[0], zero);
    let witness = m.witness(leaf_index);
    assert!(m.check_inclusion(witness, leaf_index, data[0]));
  }

  use std::collections::HashMap;
  pub struct MerkleTree<H>
  where
    H: Hasher,
  {
    pub hasher: H,
    pub zero: Vec<H::F>,
    pub depth: usize,
    pub nodes: HashMap<(usize, usize), H::F>,
  }

  impl<H> MerkleTree<H>
  where
    H: Hasher,
  {
    pub fn empty(hasher: H, depth: usize) -> Self {
      let mut zero: Vec<H::F> = Vec::with_capacity(depth + 1);
      zero.push(H::F::from_str("0").unwrap());
      for i in 0..depth {
        zero.push(hasher.hash(&[zero[i]; 2]));
      }
      zero.reverse();
      MerkleTree {
        hasher: hasher,
        zero: zero.clone(),
        depth: depth,
        nodes: HashMap::new(),
      }
    }

    fn get_node(&self, depth: usize, index: usize) -> H::F {
      *self
        .nodes
        .get(&(depth, index))
        .unwrap_or_else(|| &self.zero[depth])
    }

    fn hash_couple(&self, depth: usize, index: usize) -> H::F {
      let b = index & !1;
      self
        .hasher
        .hash(&[self.get_node(depth, b), self.get_node(depth, b + 1)])
    }

    fn recalculate_from(&mut self, leaf_index: usize) {
      let mut i = leaf_index;
      let mut depth = self.depth;
      loop {
        let h = self.hash_couple(depth, i);
        i >>= 1;
        depth -= 1;
        self.nodes.insert((depth, i), h);
        if depth == 0 {
          break;
        }
      }
      assert_eq!(depth, 0);
      assert_eq!(i, 0);
    }

    pub fn update(&mut self, leaf_index: usize, new: H::F, old: Option<H::F>) {
      let d = self.depth;
      {
        if old.is_some() {
          let old = old.unwrap();
          let t = self.get_node(d, leaf_index);
          if t.is_zero() {
            assert!(old.is_zero());
          } else {
            assert!(t.eq(&self.hasher.hash(&[old])));
          }
        }
      };
      self.nodes.insert((d, leaf_index), self.hasher.hash(&[new]));
      self.recalculate_from(leaf_index);
    }

    pub fn root(&self) -> H::F {
      return self.get_node(0, 0);
    }

    pub fn witness(&mut self, leaf_index: usize) -> Vec<(H::F, bool)> {
      let mut witness = Vec::<(H::F, bool)>::with_capacity(self.depth);
      let mut i = leaf_index;
      let mut depth = self.depth;
      loop {
        i ^= 1;
        witness.push((self.get_node(depth, i), (i & 1 == 1)));
        i >>= 1;
        depth -= 1;
        if depth == 0 {
          break;
        }
      }
      assert_eq!(i, 0);
      witness
    }

    pub fn check_inclusion(
      &mut self,
      witness: Vec<(H::F, bool)>,
      leaf_index: usize,
      data: H::F,
    ) -> bool {
      let mut acc = self.hasher.hash(&[data]);
      {
        assert!(self.get_node(self.depth, leaf_index).eq(&acc));
      }
      for w in witness.into_iter() {
        if w.1 {
          acc = self.hasher.hash2(acc, w.0);
        } else {
          acc = self.hasher.hash2(w.0, acc);
        }
      }
      acc.eq(&self.root())
    }
  }
}
