use crate::sss::allocate_add_with_coeff;

use bellman::pairing::Engine;
use bignat::hash::circuit::CircuitHasher;
use bignat::hash::Hasher;
use sapling_crypto::bellman::{
  Circuit, ConstraintSystem, SynthesisError, Variable,
};
use sapling_crypto::circuit::{boolean, ecc, num, Assignment};
use sapling_crypto::jubjub::{JubjubEngine, JubjubParams, PrimeOrder};

// Rate Limit Nullifier

#[derive(Clone)]
pub struct RLNInputs<E>
where
  E: JubjubEngine,
{
  // Public inputs

  // share, (x, y),
  // where x should be hash of the signal
  // and y is the evaluation
  pub share_x: Option<E::Fr>,
  pub share_y: Option<E::Fr>,

  // epoch is the external nullifier
  // we derive the line equation and the nullifier from epoch
  pub epoch: Option<E::Fr>,

  // nullifier
  pub nullifier: Option<E::Fr>,

  // root is the current state of membership set
  pub root: Option<E::Fr>,

  // Private inputs

  // together with the epoch, preimage will be
  // used to construct a secret line equation
  pub preimage: Option<E::Fr>,

  // authentication path of the member
  pub auth_path: Vec<Option<(E::Fr, bool)>>,
}

#[derive(Clone)]
// pub struct RLNCircuit<'a, E, H>
pub struct RLNCircuit<E, H>
where
  E: JubjubEngine,
  H: Hasher<F = E::Fr>,
{
  pub inputs: RLNInputs<E>,
  // pub hasher: &'a H,
  pub hasher: H,
}

impl<E, H> Circuit<E> for RLNCircuit<E, H>
where
  E: JubjubEngine,
  H: CircuitHasher<E = E> + Hasher<F = E::Fr>,
{
  fn synthesize<CS: ConstraintSystem<E>>(
    self,
    cs: &mut CS,
  ) -> Result<(), SynthesisError> {
    // 1. Part
    // Membership constraints
    // root == merkle_proof(auth_path, preimage_of_leaf)

    let root = num::AllocatedNum::alloc(cs.namespace(|| "root"), || {
      let value = self.inputs.root.clone();
      Ok(*value.get()?)
    })?;
    root.inputize(cs.namespace(|| "root is public"))?;

    let preimage =
      num::AllocatedNum::alloc(cs.namespace(|| "preimage"), || {
        let value = self.inputs.preimage;
        Ok(*value.get()?)
      })?;

    // identity is a leaf of membership tree
    let identity = self
      .hasher
      .allocate_hash(cs.namespace(|| "identity"), &[preimage.clone()])?;

    // allocate authetication path
    // fix: merke depth would be better to be constant
    let auth_path_witness = self.inputs.auth_path.clone();
    let mut auth_path: Vec<(num::AllocatedNum<E>, boolean::Boolean)> =
      Vec::with_capacity(auth_path_witness.len());
    for (i, e) in auth_path_witness.into_iter().enumerate() {
      let cs = &mut cs.namespace(|| format!("auth path {}", i));
      let position = boolean::Boolean::from(boolean::AllocatedBit::alloc(
        cs.namespace(|| "position bit"),
        e.map(|e| e.1),
      )?);
      let path_element =
        num::AllocatedNum::alloc(cs.namespace(|| "path element"), || {
          Ok(e.get()?.0)
        })?;
      auth_path.push((path_element, position));
    }

    // accumulator up to the root
    let mut acc = identity.clone();

    // ascend the tree
    // fix: could be done inside the previous iteration
    for (i, e) in auth_path.iter().enumerate() {
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
          .allocate_hash2(cs.namespace(|| "hash couple"), &xl, &xr)?;
    }

    // see if it is a member
    cs.enforce(
      || "enforce membership",
      |lc| lc + acc.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + root.get_variable(),
    );

    // 2. Part
    // Line Equation Constaints
    // a_1 = hash(a_0, epoch)
    // share_y == a_0 + a_1 * share_x

    let epoch = num::AllocatedNum::alloc(cs.namespace(|| "epoch"), || {
      let value = self.inputs.epoch.clone();
      Ok(*value.get()?)
    })?;
    epoch.inputize(cs.namespace(|| "epoch is public"))?;

    let a_0 = preimage.clone();

    // a_1 == h(a_0, aux)
    let a_1 = self
      .hasher
      .allocate_hash(cs.namespace(|| "a_1"), &[epoch, a_0.clone()])?;

    let share_x = num::AllocatedNum::alloc(cs.namespace(|| "share x"), || {
      let value = self.inputs.share_x.clone();
      Ok(*value.get()?)
    })?;
    share_x.inputize(cs.namespace(|| "share x is public"))?;

    // constaint the evaluation the line equation
    let eval =
      allocate_add_with_coeff(cs.namespace(|| "eval"), &a_1, &a_0, &share_x)?;

    let share_y = num::AllocatedNum::alloc(cs.namespace(|| "share x"), || {
      let value = self.inputs.share_y.clone();
      Ok(*value.get()?)
    })?;
    share_y.inputize(cs.namespace(|| "share x is public"))?;

    // see if share satisfies the line equation
    cs.enforce(
      || "enforce lookup",
      |lc| lc + share_y.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + eval.get_variable(),
    );

    // 3. Part
    // Nullifier constraints

    // hashing secret twice with epoch ingredient
    // a_1 == hash(a_0, epoch)
    // is already constrained

    // nullifier == hash(a_1)

    let nullifier_calculated = self
      .hasher
      .allocate_hash(cs.namespace(|| "calculated nullifier"), &[a_1.clone()])?;

    let nullifier =
      num::AllocatedNum::alloc(cs.namespace(|| "nullifier"), || {
        let value = self.inputs.root.clone();
        Ok(*value.get()?)
      })?;
    nullifier.inputize(cs.namespace(|| "nullifier is public"))?;

    // check if correct nullifier supplied
    cs.enforce(
      || "enforce nullifier",
      |lc| lc + nullifier_calculated.get_variable(),
      |lc| lc + CS::one(),
      |lc| lc + nullifier.get_variable(),
    );

    Ok(())
  }
}