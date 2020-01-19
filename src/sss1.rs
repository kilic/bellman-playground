mod sss1 {

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

  pub fn allocate_add_with_coeff<CS, E>(
    mut cs: CS,
    a1: &num::AllocatedNum<E>,
    x: &num::AllocatedNum<E>,
    a0: &num::AllocatedNum<E>,
  ) -> Result<num::AllocatedNum<E>, SynthesisError>
  where
    E: Engine,
    CS: ConstraintSystem<E>,
  {
    let ax = num::AllocatedNum::alloc(cs.namespace(|| "a1x"), || {
      let mut ax_val = *a1.get_value().get()?;
      let x_val = *x.get_value().get()?;
      ax_val.mul_assign(&x_val);
      Ok(ax_val)
    })?;

    cs.enforce(
      || "a1*x",
      |lc| lc + a1.get_variable(),
      |lc| lc + x.get_variable(),
      |lc| lc + ax.get_variable(),
    );

    let y = num::AllocatedNum::alloc(cs.namespace(|| "y"), || {
      let ax_val = *ax.get_value().get()?;
      let mut y_val = *a0.get_value().get()?;
      y_val.add_assign(&ax_val);
      Ok(y_val)
    })?;

    cs.enforce(
      || "enforce y",
      |lc| lc + ax.get_variable() + a0.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + y.get_variable(),
    );
    Ok(y)
  }

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
        .allocate_hash(cs.namespace(|| "a_1"), &[aux, a_0.clone()])?;

      let mut acc =
        allocate_add_with_coeff(cs.namespace(|| "acc_1"), &a_1, &x, &a_0)?;

      let mut x_n =
        num::AllocatedNum::alloc(cs.namespace(|| format!("base")), || {
          Ok(*x.get_value().get()?)
        })?;

      let mut a_n =
        num::AllocatedNum::alloc(cs.namespace(|| format!("coeff")), || {
          Ok(*a_1.get_value().get()?)
        })?;

      for i in 0..self.degree - 1 {
        a_n = self
          .hasher
          .allocate_hash(cs.namespace(|| format!("a_{}", i + 2)), &[a_n])?;
        x_n = x_n.mul(cs.namespace(|| format!("x_n_{}", i + 2)), &x)?;
        acc = allocate_add_with_coeff(
          cs.namespace(|| format!("acc_{}", i + 2)),
          &a_n,
          &x_n,
          &acc,
        )?;
      }

      let y = num::AllocatedNum::alloc(cs.namespace(|| "y"), || {
        let value = self.inputs.share_y.clone();
        Ok(*value.get()?)
      })?;
      y.inputize(cs.namespace(|| "share y public input"))?;

      cs.enforce(
        || "enforce evaluation",
        |lc| lc + y.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + acc.get_variable(),
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
      let mut a_n = E::Fr::zero();
      let mut x_n = E::Fr::zero();
      for i in 0..degree {
        if i == 0 {
          x_n = x.clone();
          acc = a_0.clone();
          a_n = hasher.hash(&[*aux, *a_0]);
        } else {
          a_n = hasher.hash(&[a_n]);
          x_n.mul_assign(x);
        }
        let mut t = a_n.clone();
        t.mul_assign(&x_n);
        acc.add_assign(&t);
      }
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
      let degree = 5;
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
    }
  }
}
