use bellman::pairing::Engine;
use bignat::hash::circuit::CircuitHasher;
use bignat::hash::Hasher;
use sapling_crypto::bellman::{
  Circuit, ConstraintSystem, SynthesisError, Variable,
};
use sapling_crypto::circuit::{boolean, ecc, num, Assignment};
use sapling_crypto::jubjub::{JubjubEngine, JubjubParams, PrimeOrder};

impl<E: JubjubEngine, H: Hasher<F = E::Fr>> Clone for MembershipSnark<E, H> {
  fn clone(&self) -> Self {
    MembershipSnark {
      inputs: self.inputs.clone(),
      hasher: self.hasher.clone(),
    }
  }
}

impl<E: JubjubEngine> Clone for MembershipInputs<E> {
  fn clone(&self) -> Self {
    MembershipInputs {
      root: self.root.clone(),
      member: self.member.clone(),
      witness: self.witness.clone(),
    }
  }
}

pub struct MembershipInputs<E>
where
  E: JubjubEngine,
{
  // state root of the set
  pub root: Option<E::Fr>,
  // claimed member in the set
  // TODO: member should be vector of elements 
  pub member: Option<E::Fr>,
  // authentication path of the member
  pub witness: Vec<Option<(E::Fr, bool)>>,
}

pub struct MembershipSnark<E, H>
where
  E: JubjubEngine,
  H: Hasher,
{
  // snark inputs
  pub inputs: MembershipInputs<E>,
  pub hasher: H,
  // let's simply take size of given withess as depth
  // pub merkle_depth: usize,
}

// impl<'a, E, H> Circuit<E> for MembershipSnark<'a, E, H>
// where
//   E: JubjubEngine,
//   H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
// {
impl<E, H> Circuit<E> for MembershipSnark<E, H>
where
  E: JubjubEngine,
  H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
  fn synthesize<CS: ConstraintSystem<E>>(
    self,
    cs: &mut CS,
  ) -> Result<(), SynthesisError> {
    // allocate for member element
    // which is claimed to be in the set
    // member is a private input
    let member = num::AllocatedNum::alloc(cs.namespace(|| "member"), || {
      let value = self.inputs.member.clone();
      Ok(*value.get()?)
    })?;

    // allocate for state root
    // root is a public input
    let root = num::AllocatedNum::alloc(cs.namespace(|| "root"), || {
      let value = self.inputs.root.clone();
      Ok(*value.get()?)
    })?;
    root.inputize(cs.namespace(|| "state root public input"))?;

    // calculate the leaf
    let leaf = self
      .hasher
      .allocate_hash(cs.namespace(|| "lef"), &[member])?;

    // accumulator up to the root
    let mut acc = leaf.clone();

    // ascend the tree
    // taken from sapling circuit
    // https://github.com/zcash-hackworks/sapling-crypto/blob/49017b4e055ba4322dad1f03fe7d80dc0ed449cc/src/circuit/sapling/mod.rs#L353
    for (i, e) in self.inputs.witness.into_iter().enumerate() {
      let cs = &mut cs.namespace(|| format!("merkle tree hash {}", i));

      let position = boolean::Boolean::from(boolean::AllocatedBit::alloc(
        cs.namespace(|| "position bit"),
        e.map(|e| e.1),
      )?);

      let path_element =
        num::AllocatedNum::alloc(cs.namespace(|| "path element"), || {
          Ok(e.get()?.0)
        })?;

      let (xr, xl) = num::AllocatedNum::conditionally_reverse(
        cs.namespace(|| "conditional reversal of preimage"),
        &acc,
        &path_element,
        &position,
      )?;

      // note that we don't apply hash personalization as in sapling circuit
      acc = self
        .hasher
        .allocate_hash2(cs.namespace(|| "hash"), &xl, &xr)?;
    }

    cs.enforce(
      || "enforce membership",
      |lc| lc + acc.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + root.get_variable(),
    );

    Ok(())
  }
}

use sapling_crypto::bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
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

  // pub fn check_inclusion(
  //   &mut self,
  //   witness: Vec<H::F>,
  //   leaf_index: usize,
  //   data: H::F,
  // ) -> bool {
  //   let mut acc = self.hasher.hash(&[data]);
  //   {
  //     assert!(self.get_node(self.depth, leaf_index).eq(&acc));
  //   }
  //   let mut i = leaf_index;
  //   for w in witness.into_iter() {
  //     if i & 1 == 1 {
  //       acc = self.hasher.hash2(w, acc);
  //     } else {
  //       acc = self.hasher.hash2(acc, w);
  //     }
  //     i >>= 1;
  //   }
  //   acc.eq(&self.root())
  // }
}

#[cfg(test)]
mod test {
  use super::{MembershipInputs, MembershipSnark, MerkleTree};
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

  #[test]
  fn test_merkle_circuit_bls12() {
    use bignat::hash::hashes::Poseidon;
    use sapling_crypto::bellman::pairing::bls12_381::{Bls12, Fr};
    let mut rng =
      XorShiftRng::from_seed([0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    let mut cs = TestConstraintSystem::<Bls12>::new();
    let hasher = Poseidon::<Bls12>::default();

    // prepare an empty set 
    let mut m = MerkleTree::empty(hasher.clone(), MERKLE_DEPTH);
    let member = Fr::from_str("11").unwrap();
    let leaf_index = 6;
    // insert a member
    m.update(leaf_index, member, None);

    // take the root and the witness for this member
    let root = m.root();
    let witness = m.witness(leaf_index);
    
    let inputs = MembershipInputs::<Bls12> {
      root: Some(root),
      member: Some(member),
      witness: witness.into_iter().map(|w| Some(w)).collect(),
    };

    let instance = MembershipSnark::<Bls12, Poseidon<Bls12>> {
      inputs: inputs,
      hasher: hasher.clone(),
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
      let empty_circuit = MembershipSnark::<Bls12, Poseidon<Bls12>> {
        inputs: input,
        hasher: hasher.clone(),
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
}
