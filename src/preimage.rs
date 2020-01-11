use bignat::hash::circuit::CircuitHasher;
use bignat::hash::Hasher;
use sapling_crypto::bellman::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use sapling_crypto::bellman::{Circuit, ConstraintSystem, SynthesisError, Variable};
use sapling_crypto::circuit::{boolean, ecc, num, Assignment};
use sapling_crypto::jubjub::{edwards, FixedGenerators, JubjubEngine, JubjubParams, PrimeOrder};

pub struct PreimageSnark<E, H>
where
  E: JubjubEngine,
  H: Hasher,
{
  pub preimage: Option<E::Fr>,
  pub hash: Option<E::Fr>,
  pub hasher: H,
}

impl<E, H> Circuit<E> for PreimageSnark<E, H>
where
  E: JubjubEngine,
  H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
  fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
    let preimage = num::AllocatedNum::alloc(cs.namespace(|| "preimage"), || {
      let value = self.preimage;
      Ok(*value.get()?)
    })?;
    let hash = num::AllocatedNum::alloc(cs.namespace(|| "hash"), || {
      let value = self.hash;
      Ok(*value.get()?)
    })?;
    hash.inputize(cs.namespace(|| "hash input"))?;
    let calculated = self
      .hasher
      .allocate_hash(cs.namespace(|| "inputs"), &[preimage])?;
    cs.enforce(
      || "add constraint between input and pedersen hash output",
      |lc| lc + calculated.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + hash.get_variable(),
    );
    Ok(())
  }
}

#[test]
fn test_preimage_snark_bls12_poseidon() {
  use bignat::hash::hashes::Poseidon;
  use rand::{Rand, SeedableRng, XorShiftRng};
  use sapling_crypto::bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
  };
  use sapling_crypto::bellman::pairing::bls12_381::{Bls12, Fr};
  use sapling_crypto::circuit::test::TestConstraintSystem;
  use sapling_crypto::jubjub::JubjubBls12;
  let mut rng = XorShiftRng::from_seed([0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
  let hasher = Poseidon::<Bls12>::default();
  let (public_inputs, circuit) = {
    let secret = Fr::rand(&mut rng);
    let output = hasher.hash(&[secret]);
    let instance = PreimageSnark::<Bls12, Poseidon<Bls12>> {
      preimage: Some(secret.clone()),
      hash: Some(output.clone()),
      hasher: hasher.clone(),
    };
    (vec![output.clone()], instance)
  };

  let circuit_parameters = {
    let empty_circuit = PreimageSnark::<Bls12, Poseidon<Bls12>> {
      preimage: None,
      hash: None,
      hasher: hasher.clone(),
    };
    generate_random_parameters(empty_circuit, &mut rng).unwrap()
  };

  let verifing_key = prepare_verifying_key(&circuit_parameters.vk);

  let proof = create_random_proof(circuit, &circuit_parameters, &mut rng).unwrap();

  let is_valid = verify_proof(&verifing_key, &proof, &public_inputs).unwrap();
  assert!(is_valid);
}
