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

  // helper function to evaluate polynomial
  // b = a_0 + a_1 * x
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
    // x and y coord of a share
    pub share_x: Option<E::Fr>,
    pub share_y: Option<E::Fr>,
    // aux is a public auxiallary input
    // for example an epoch
    pub aux: Option<E::Fr>,
    // together with 'aux' secret will be used to construct a secret polynomial
    pub secret: Option<E::Fr>,
  }

  pub struct SSSSnark<'a, E, H>
  where
    E: JubjubEngine,
    H: Hasher<F = E::Fr>,
  {
    pub degree: usize,
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
      // allocate for a_0 coefficient
      // which is a private input
      let a_0 = num::AllocatedNum::alloc(cs.namespace(|| "a_0"), || {
        let value = self.inputs.secret.clone();
        Ok(*value.get()?)
      })?;
      // aux is public input
      // one of the input parameters for constructing the sss polynomial
      let aux = num::AllocatedNum::alloc(cs.namespace(|| "aux"), || {
        let value = self.inputs.aux.clone();
        Ok(*value.get()?)
      })?;
      aux.inputize(cs.namespace(|| "aux public input"))?;

      // x coord of the share, public input
      let x = num::AllocatedNum::alloc(cs.namespace(|| "x"), || {
        let value = self.inputs.share_x.clone();
        Ok(*value.get()?)
      })?;
      x.inputize(cs.namespace(|| "share x public input"))?;

      // a_1 coefficient
      // a_1 = h(a_0, aux)
      let a_1 = self
        .hasher
        .allocate_hash(cs.namespace(|| "a_1"), &[aux, a_0.clone()])?;

      // first we allocate for coefficients
      // a_n = h(a_(n-1)) where n > 1
      let mut coeffs = vec![a_0, a_1];

      for i in 0..self.degree - 1 {
        let a_prev = coeffs.last().unwrap().clone();
        let a_n = self
          .hasher
          .allocate_hash(cs.namespace(|| format!("a_{}", i + 2)), &[a_prev])?;
        coeffs.push(a_n);
      }

      // evaluate polynomial and make constaints for y coord of the share
      // apply horner look up
      // A(x) = a_0 + x * (a_1 + x * (a_2 + ... + x * (a_(n-2) + x * a_(n-1)) ... ))
      coeffs.reverse();
      let mut acc = allocate_add_with_coeff(
        cs.namespace(|| "acc_0"),
        &coeffs[0].clone(),
        &x,
        &coeffs[1].clone(),
      )?;
      for i in 2..self.degree + 1 {
        acc = allocate_add_with_coeff(
          cs.namespace(|| format!("acc_{}", i)),
          &acc,
          &x,
          &coeffs[i].clone(),
        )?;
      }

      // y coord of the share,
      // claimed evaluation,
      // public input
      let y = num::AllocatedNum::alloc(cs.namespace(|| "y"), || {
        let value = self.inputs.share_y.clone();
        Ok(*value.get()?)
      })?;
      y.inputize(cs.namespace(|| "share y public input"))?;

      // enforce lookup
      cs.enforce(
        || "enforce lookup",
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

    fn evaluate_sss_poly<E, H>(
      degree: usize,
      hasher: &H,
      aux: &E::Fr,
      x: &E::Fr,
      a_0: &E::Fr,
    ) -> E::Fr
    where
      E: Engine,
      H: Hasher<F = E::Fr>,
    {
      // derive coeffs
      let mut a_n = E::Fr::zero();
      let mut coeffs: Vec<E::Fr> = vec![*a_0];
      for i in 0..degree {
        if i == 0 {
          a_n = hasher.hash(&[*aux, *a_0]);
        } else {
          a_n = hasher.hash(&[a_n]);
        }
        coeffs.push(a_n);
      }
      // evaluate
      let mut acc = E::Fr::zero();
      for (i, a) in coeffs.into_iter().enumerate().rev() {
        acc.add_assign(&a);
        if i != 0 {
          acc.mul_assign(x);
        }
      }
      acc
    }

    #[test]
    fn test_xxx_bls12() {
      use sapling_crypto::bellman::pairing::bls12_381::{Bls12, Fr};
      let mut rng = XorShiftRng::from_seed([
        0x3dbe6258, 0x8d313d76, 0x3237db17, 0xe5bc0654,
      ]);
      let mut cs = TestConstraintSystem::<Bls12>::new();
      let hasher = Poseidon::<Bls12>::default();
      let degree = 5usize;
      let secret = Fr::rand(&mut rng);
      let aux = Fr::rand(&mut rng);
      let share_x = Fr::rand(&mut rng);
      let share_y: Fr = evaluate_sss_poly::<Bls12, Poseidon<Bls12>>(
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
          panic!("unsatisfied\n{}", unsatisfied.unwrap());
        }
        let unconstrained = cs.find_unconstrained();
        if !unconstrained.is_empty() {
          panic!("unconstrained\n{}", unconstrained);
        }
        assert!(cs.is_satisfied());
      }
    }
  }
}
