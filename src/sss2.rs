mod sss2 {
  use bignat::hash::circuit::CircuitHasher;
  use bignat::hash::Hasher;
  use sapling_crypto::bellman::pairing::ff::{
    Field, PrimeField, PrimeFieldRepr,
  };
  use sapling_crypto::bellman::pairing::Engine;
  use sapling_crypto::bellman::{
    Circuit, ConstraintSystem, SynthesisError, Variable,
  };
  use sapling_crypto::circuit::{boolean, ecc, num, Assignment};
  use sapling_crypto::jubjub::{
    edwards, FixedGenerators, JubjubEngine, JubjubParams, PrimeOrder,
  };

  pub struct SSSInputs<E>
  where
    E: JubjubEngine,
  {
    pub share_x: Option<E::Fr>,
    pub share_y: Option<E::Fr>,
    pub aux: Option<E::Fr>,
    pub secret: Option<E::Fr>,
  }

  pub struct SSSSnark<'a, E, H>
  where
    E: JubjubEngine,
    H: Hasher<F = E::Fr>,
  {
    pub degree: u32,
    pub inputs: SSSInputs<E>,
    pub hasher: &'a H,
  }

  impl<'a, E: JubjubEngine + 'a, H: Hasher<F = E::Fr>> Clone
    for SSSSnark<'a, E, H>
  {
    fn clone(&self) -> Self {
      SSSSnark {
        degree: self.degree,
        inputs: self.inputs.clone(),
        hasher: self.hasher,
      }
    }
  }

  impl<E: JubjubEngine> Clone for SSSInputs<E> {
    fn clone(&self) -> Self {
      SSSInputs {
        share_x: self.share_x,
        share_y: self.share_y,
        aux: self.aux,
        secret: self.secret,
      }
    }
  }

  impl<'a, E, H> Circuit<E> for SSSSnark<'a, E, H>
  where
    E: JubjubEngine,
    H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
  {
    fn synthesize<CS: ConstraintSystem<E>>(
      self,
      cs: &mut CS,
    ) -> Result<(), SynthesisError> {
      let a_0 = num::AllocatedNum::alloc(cs.namespace(|| "a_0"), || {
        let value = self.inputs.secret.clone();
        Ok(*value.get()?)
      })?;

      let aux = num::AllocatedNum::alloc(cs.namespace(|| "aux"), || {
        let value = self.inputs.aux.clone();
        Ok(*value.get()?)
      })?;
      aux.inputize(cs.namespace(|| "aux public input"))?;
      let x = num::AllocatedNum::alloc(cs.namespace(|| "x"), || {
        let value = self.inputs.share_x.clone();
        Ok(*value.get()?)
      })?;
      x.inputize(cs.namespace(|| "share x public input"))?;

      let a_1 = self
        .hasher
        .allocate_hash(cs.namespace(|| "a_n"), &[aux, a_0.clone()])?;

      let mut p = num::AllocatedNum::alloc(cs.namespace(|| "p"), || {
        let value = x.get_value().clone();
        Ok(*value.get()?)
      })?;

      let mut x_n = num::AllocatedNum::alloc(cs.namespace(|| "x_1"), || {
        let value = x.get_value().clone();
        Ok(*value.get()?)
      })?;

      for i in 1..self.degree {
        x_n = x_n.mul(cs.namespace(|| format!("x_{}", i + 1)), &x)?;
        let p_prev = p.clone();
        p = num::AllocatedNum::alloc(
          cs.namespace(|| format!("p_{}", i)),
          || {
            let mut p_val = *p_prev.get_value().get()?;
            let x_n_val = *x_n.get_value().get()?;
            p_val.add_assign(&x_n_val);
            Ok(p_val)
          },
        )?;
        cs.enforce(
          || format!("enforce p_{}", i),
          |lc| lc + p_prev.get_variable() + x_n.get_variable(),
          |lc| lc + CS::one(),
          |lc| lc + p.get_variable(),
        );
      }

      let p_a_1 = p.mul(cs.namespace(|| "p*a_1"), &a_1)?;

      let y = num::AllocatedNum::alloc(cs.namespace(|| "y"), || {
        let value = self.inputs.share_y.clone();
        Ok(*value.get()?)
      })?;
      y.inputize(cs.namespace(|| "share y public input"))?;

      cs.enforce(
        || "enforce evaluation",
        |lc| lc + y.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + p_a_1.get_variable() + a_0.get_variable(),
      );
      Ok(())
    }
  }

  #[cfg(test)]
  mod test {
    use super::{SSSInputs, SSSSnark};
    use bignat::hash::hashes::Poseidon;
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

    fn evaluate_sss<E, H>(
      degree: u32,
      hasher: &H,
      aux: &E::Fr,
      x: &E::Fr,
      a_0: &E::Fr,
    ) -> E::Fr
    where
      E: Engine,
      H: Hasher<F = E::Fr>,
    {
      let mut acc = E::Fr::zero();
      let a_n = hasher.hash(&[*aux, *a_0]);
      let mut x_n = x.clone();
      for i in 0..degree {
        if i != 0 {
          x_n.mul_assign(&x);
        }
        acc.add_assign(&x_n);
      }
      acc.mul_assign(&a_n);
      acc.add_assign(a_0);
      acc
    }

    #[test]
    fn test_sss_bls12() {
      use sapling_crypto::bellman::pairing::bls12_381::{Bls12, Fr};
      let mut rng = XorShiftRng::from_seed([
        0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654,
      ]);
      let mut cs = TestConstraintSystem::<Bls12>::new();
      let hasher = Poseidon::<Bls12>::default();
      let degree = 3;
      let secret = Fr::rand(&mut rng);
      let aux = Fr::rand(&mut rng);
      let share_x = Fr::rand(&mut rng);
      let share_y: Fr = evaluate_sss::<Bls12, Poseidon<Bls12>>(
        degree, &hasher, &aux, &share_x, &secret,
      );
      let input = SSSInputs::<Bls12> {
        share_x: Some(share_x),
        share_y: Some(share_y),
        secret: Some(secret),
        aux: Some(aux),
      };
      let instance = SSSSnark::<Bls12, Poseidon<Bls12>> {
        degree: degree,
        inputs: input,
        hasher: &hasher,
      };
      {
        let instance = instance.clone();
        instance.synthesize(&mut cs).unwrap();
        let unsatisfied = cs.which_is_unsatisfied();
        if unsatisfied.is_some() {
          panic!("unsatis {}", unsatisfied.unwrap());
        }
        let unconstrained = cs.find_unconstrained();
        if !unconstrained.is_empty() {
          panic!("unconst: {}", unconstrained);
        }
        assert!(cs.is_satisfied());
      }

      let public_inputs = vec![aux, share_x, share_y];
      let circuit_parameters = {
        let input = SSSInputs::<Bls12> {
          share_x: None,
          share_y: None,
          secret: None,
          aux: None,
        };
        let empty_circuit = SSSSnark::<Bls12, Poseidon<Bls12>> {
          degree: degree,
          inputs: input,
          hasher: &hasher,
        };
        generate_random_parameters(empty_circuit, &mut rng).unwrap()
      };

      let verifing_key = prepare_verifying_key(&circuit_parameters.vk);
      let proof =
        create_random_proof(instance, &circuit_parameters, &mut rng).unwrap();
      let is_valid =
        verify_proof(&verifing_key, &proof, &public_inputs).unwrap();
      assert!(is_valid);
    }
  }
}
