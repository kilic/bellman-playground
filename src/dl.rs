use bellman_ce::{Circuit, ConstraintSystem, SynthesisError};

use sapling_crypto_ce::circuit::{boolean, ecc, num};

use sapling_crypto_ce::jubjub::{
  edwards, FixedGenerators, JubjubEngine, PrimeOrder,
};

pub struct DLSnark<'a, E: JubjubEngine> {
  pub params: &'a E::Params,
  pub priv_key: Option<E::Fs>,
  pub pub_key: Option<edwards::Point<E, PrimeOrder>>,
}

impl<'a, E: JubjubEngine + 'a> Clone for DLSnark<'a, E> {
  fn clone(&self) -> Self {
    DLSnark {
      params: self.params,
      priv_key: self.priv_key.clone(),
      pub_key: self.pub_key.clone(),
    }
  }
}

impl<'a, E: JubjubEngine> Circuit<E> for DLSnark<'a, E> {
  fn synthesize<CS: ConstraintSystem<E>>(
    self,
    cs: &mut CS,
  ) -> Result<(), SynthesisError> {
    let c_x = boolean::field_into_boolean_vec_le(
      cs.namespace(|| "private key"),
      self.priv_key,
    )?;

    let c_pub_calculated = ecc::fixed_base_multiplication(
      cs.namespace(|| "calculated public key"),
      FixedGenerators::ValueCommitmentValue,
      &c_x,
      self.params,
    )?;

    let c_pub_claimed = ecc::EdwardsPoint::witness(
      cs.namespace(|| "claimed public key"),
      self.pub_key,
      self.params,
    )?;
    c_pub_claimed.inputize(cs.namespace(|| "public input public key"))?;

    let x_eq = num::AllocatedNum::equals(
      cs.namespace(|| "compare x coord of pub key"),
      c_pub_claimed.get_x(),
      c_pub_calculated.get_x(),
    )?;
    let y_eq = num::AllocatedNum::equals(
      cs.namespace(|| "compare y coord of pub key"),
      c_pub_claimed.get_y(),
      c_pub_calculated.get_y(),
    )?;
    let xy_eq =
      boolean::Boolean::and(cs.namespace(|| "compress bools"), &x_eq, &y_eq)?;
    boolean::Boolean::enforce_equal(
      cs.namespace(|| "last check"),
      &xy_eq,
      &boolean::Boolean::constant(true),
    )?;
    Ok(())
  }
}

#[test]
fn test_dl_circuit_bls12() {
  use bellman_ce::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key,
    verify_proof,
  };
  use bellman_ce::pairing::bls12_381::Bls12;
  use rand::{Rand, SeedableRng, XorShiftRng};
  use sapling_crypto_ce::circuit::test::TestConstraintSystem;
  use sapling_crypto_ce::jubjub::{
    fs::Fs, FixedGenerators, JubjubBls12, JubjubParams,
  };

  let curve_params: &JubjubBls12 = &JubjubBls12::new();
  let mut rng =
    XorShiftRng::from_seed([0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

  let (public_inputs, circuit) = {
    let a = Fs::rand(&mut rng);
    // let r = Fs::rand(&mut rng); // use as bad input
    let generator =
      curve_params.generator(FixedGenerators::ValueCommitmentValue);
    let pub_key = generator.mul(a, curve_params);
    let instance = DLSnark::<Bls12> {
      params: curve_params,
      priv_key: Some(a.clone()),
      pub_key: Some(pub_key.clone()),
    };
    let (x, y) = pub_key.into_xy();
    (vec![x, y], instance)
  };

  {
    let mut cs = TestConstraintSystem::<Bls12>::new();
    let circuit = circuit.clone();

    circuit.synthesize(&mut cs).expect("to be synthesized");
    assert!(cs.find_unconstrained() == "");

    let unsatisfied = cs.which_is_unsatisfied();
    if unsatisfied.is_some() {
      panic!("{}", unsatisfied.unwrap());
    }
  };

  let circuit_parameters = {
    let empty_circuit = DLSnark::<Bls12> {
      params: curve_params,
      priv_key: None,
      pub_key: None,
    };
    generate_random_parameters(empty_circuit, &mut rng).unwrap()
  };

  let verifing_key = prepare_verifying_key(&circuit_parameters.vk);

  let proof =
    create_random_proof(circuit, &circuit_parameters, &mut rng).unwrap();

  let is_valid = verify_proof(&verifing_key, &proof, &public_inputs).unwrap();
  assert!(is_valid);
}
