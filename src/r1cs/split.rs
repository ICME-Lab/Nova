use super::{R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness};
use crate::traits::commitment::CommitmentEngineTrait;
use crate::DerandKey;
use crate::{
  errors::NovaError,
  traits::{AbsorbInROTrait, Engine},
  zip_with, Commitment, CommitmentKey, CE,
};
use ff::Field;
use ff::PrimeField;
use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelRefIterator;
use rayon::iter::ParallelIterator;
use serde::{Deserialize, Serialize};

/// A split R1CS instance.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SplitR1CSInstance<E>
where
  E: Engine,
{
  pub(crate) aux: R1CSInstance<E>,
  pub(crate) precommitted: (Commitment<E>, Commitment<E>),
}

impl<E> SplitR1CSInstance<E>
where
  E: Engine,
{
  pub fn new(
    aux: R1CSInstance<E>,
    precommitted: (Commitment<E>, Commitment<E>),
  ) -> SplitR1CSInstance<E> {
    Self { aux, precommitted }
  }

  pub fn X(&self) -> &[E::Scalar] {
    &self.aux.X
  }
}

impl<E: Engine> AbsorbInROTrait<E> for SplitR1CSInstance<E> {
  fn absorb_in_ro(&self, ro: &mut E::RO) {
    self.aux.absorb_in_ro(ro);
    self.precommitted.0.absorb_in_ro(ro);
    self.precommitted.1.absorb_in_ro(ro);
  }
}

/// A split R1CS witness.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SplitR1CSWitness<E>
where
  E: Engine,
{
  pub(crate) aux: R1CSWitness<E>,
  pub(crate) precommitted: (Vec<E::Scalar>, Vec<E::Scalar>),
}

impl<E> SplitR1CSWitness<E>
where
  E: Engine,
{
  pub fn new(
    aux: R1CSWitness<E>,
    precommitted: (Vec<E::Scalar>, Vec<E::Scalar>),
  ) -> SplitR1CSWitness<E> {
    Self { aux, precommitted }
  }

  pub fn clone_W(&self) -> Vec<E::Scalar> {
    [
      self.precommitted.0.clone(),
      self.precommitted.1.clone(),
      self.aux.W.clone(),
    ]
    .concat()
  }

  /// Get the precommitted commitments
  pub fn commit(&self, ck: &CommitmentKey<E>) -> (Commitment<E>, Commitment<E>) {
    (
      CE::<E>::commit(ck, &self.precommitted.0, &E::Scalar::ZERO),
      CE::<E>::commit_at(
        ck,
        &self.precommitted.1,
        &E::Scalar::ZERO,
        self.precommitted.0.len(),
      ),
    )
  }
}

/// A split RelaxedR1CS instance.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SplitRelaxedR1CSInstance<E>
where
  E: Engine,
{
  pub(crate) aux: RelaxedR1CSInstance<E>,
  pub(crate) precommitted: (Commitment<E>, Commitment<E>),
}

impl<E> SplitRelaxedR1CSInstance<E>
where
  E: Engine,
{
  pub fn new(aux: RelaxedR1CSInstance<E>, precommitted: (Commitment<E>, Commitment<E>)) -> Self {
    Self { aux, precommitted }
  }

  /// Create a default instance
  pub fn default(_ck: &CommitmentKey<E>, S: &R1CSShape<E>) -> Self {
    let aux = RelaxedR1CSInstance::default(_ck, S);
    let precommitted = (Commitment::<E>::default(), Commitment::<E>::default());
    Self { aux, precommitted }
  }

  /// Folds an incoming `SplitR1CSInstance` into the current one
  pub fn fold(
    &self,
    U2: &SplitR1CSInstance<E>,
    comm_T: &Commitment<E>,
    r: &E::Scalar,
  ) -> SplitRelaxedR1CSInstance<E> {
    let aux = self.aux.fold(&U2.aux, comm_T, r);
    let precommitted = (
      self.precommitted.0 + U2.precommitted.0 * *r,
      self.precommitted.1 + U2.precommitted.1 * *r,
    );
    Self { aux, precommitted }
  }

  /// Folds an incoming `SplitR1CSInstance` into the current one
  pub fn fold_relaxed(&self, U2: &Self, comm_T: &Commitment<E>, r: &E::Scalar) -> Self {
    let aux = self.aux.fold_relaxed(&U2.aux, comm_T, r);
    let precommitted = (
      self.precommitted.0 + U2.precommitted.0 * *r,
      self.precommitted.1 + U2.precommitted.1 * *r,
    );
    Self { aux, precommitted }
  }

  pub fn X(&self) -> &[E::Scalar] {
    &self.aux.X
  }

  pub fn u(&self) -> E::Scalar {
    self.aux.u
  }

  pub fn from_r1cs_instance(
    ck: &CommitmentKey<E>,
    S: &R1CSShape<E>,
    instance: &SplitR1CSInstance<E>,
  ) -> SplitRelaxedR1CSInstance<E> {
    let aux = RelaxedR1CSInstance::from_r1cs_instance(ck, S, &instance.aux);
    let precommitted = (instance.precommitted.0, instance.precommitted.1);
    Self { aux, precommitted }
  }

  pub fn derandomize(
    &self,
    dk: &DerandKey<E>,
    r_W: &E::Scalar,
    r_E: &E::Scalar,
  ) -> SplitRelaxedR1CSInstance<E> {
    let aux = self.aux.derandomize(dk, r_W, r_E);
    Self {
      aux,
      precommitted: self.precommitted,
    }
  }
}

impl<E: Engine> AbsorbInROTrait<E> for SplitRelaxedR1CSInstance<E> {
  fn absorb_in_ro(&self, ro: &mut E::RO) {
    self.aux.absorb_in_ro(ro);
    self.precommitted.0.absorb_in_ro(ro);
    self.precommitted.1.absorb_in_ro(ro);
  }
}

impl<E> From<SplitRelaxedR1CSInstance<E>> for RelaxedR1CSInstance<E>
where
  E: Engine,
{
  fn from(value: SplitRelaxedR1CSInstance<E>) -> Self {
    let comm_W = value.precommitted.0 + value.precommitted.1 + value.aux.comm_W;
    Self {
      comm_E: value.aux.comm_E,
      u: value.aux.u,
      X: value.aux.X,
      comm_W,
    }
  }
}

/// A split RelaxedR1CS witness.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SplitRelaxedR1CSWitness<E>
where
  E: Engine,
{
  pub(crate) aux: RelaxedR1CSWitness<E>,
  pub(crate) precommitted: (Vec<E::Scalar>, Vec<E::Scalar>),
}

impl<E> SplitRelaxedR1CSWitness<E>
where
  E: Engine,
{
  pub fn new(aux: RelaxedR1CSWitness<E>, precommitted: (Vec<E::Scalar>, Vec<E::Scalar>)) -> Self {
    Self { aux, precommitted }
  }

  /// Create a default witness
  pub fn default(S: &R1CSShape<E>) -> Self {
    let aux = RelaxedR1CSWitness::default(S);
    let precommitted = (
      vec![E::Scalar::ZERO; S.num_precommits.0],
      vec![E::Scalar::ZERO; S.num_precommits.1],
    );
    Self { aux, precommitted }
  }

  /// Folds an incoming `SplitR1CSWitness` into the current one
  pub fn fold(
    &self,
    W2: &SplitR1CSWitness<E>,
    T: &[E::Scalar],
    r_T: &E::Scalar,
    r: &E::Scalar,
  ) -> Result<SplitRelaxedR1CSWitness<E>, NovaError> {
    let aux = self.aux.fold(&W2.aux, T, r_T, r)?;
    let precommitted = (
      fold_witness(&self.precommitted.0, &W2.precommitted.0, *r)?,
      fold_witness(&self.precommitted.1, &W2.precommitted.1, *r)?,
    );
    Ok(Self { aux, precommitted })
  }

  /// Folds an incoming `SplitR1CSWitness` into the current one
  pub fn fold_relaxed(
    &self,
    W2: &Self,
    T: &[E::Scalar],
    r_T: &E::Scalar,
    r: &E::Scalar,
  ) -> Result<Self, NovaError> {
    let aux = self.aux.fold_relaxed(&W2.aux, T, r_T, r)?;
    let precommitted = (
      fold_witness(&self.precommitted.0, &W2.precommitted.0, *r)?,
      fold_witness(&self.precommitted.1, &W2.precommitted.1, *r)?,
    );
    Ok(Self { aux, precommitted })
  }

  pub fn clone_W(&self) -> Vec<E::Scalar> {
    [
      self.precommitted.0.clone(),
      self.precommitted.1.clone(),
      self.aux.W.clone(),
    ]
    .concat()
  }

  pub fn E(&self) -> &[E::Scalar] {
    &self.aux.E
  }

  /// Initializes a new `RelaxedR1CSWitness` from an `R1CSWitness`
  pub fn from_r1cs_witness(
    S: &R1CSShape<E>,
    witness: &SplitR1CSWitness<E>,
  ) -> SplitRelaxedR1CSWitness<E> {
    let aux = RelaxedR1CSWitness::from_r1cs_witness(S, &witness.aux);
    let precommitted = (
      witness.precommitted.0.clone(),
      witness.precommitted.1.clone(),
    );
    Self { aux, precommitted }
  }

  pub fn derandomize(&self) -> (Self, E::Scalar, E::Scalar) {
    let (aux, wit_blind, err_blind) = self.aux.derandomize();
    (
      Self {
        aux,
        precommitted: self.precommitted.clone(),
      },
      wit_blind,
      err_blind,
    )
  }
}

impl<E> From<SplitRelaxedR1CSWitness<E>> for RelaxedR1CSWitness<E>
where
  E: Engine,
{
  fn from(value: SplitRelaxedR1CSWitness<E>) -> Self {
    let W = [value.precommitted.0, value.precommitted.1, value.aux.W].concat();
    Self {
      W,
      E: value.aux.E,
      r_E: value.aux.r_E,
      r_W: value.aux.r_W,
    }
  }
}

pub fn fold_witness<F: PrimeField>(W1: &[F], W2: &[F], r: F) -> Result<Vec<F>, NovaError> {
  if W1.len() != W2.len() {
    return Err(NovaError::InvalidWitnessLength);
  }
  Ok(zip_with!((W1.par_iter(), W2), |a, b| *a + r * *b).collect::<Vec<F>>())
}
