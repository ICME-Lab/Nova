//! This module implements `CompCommitmentEngineTrait` using Spartan's SPARK compiler
//! We also provide a trivial implementation that has the verifier evaluate the sparse polynomials
use crate::{
  errors::NovaError,
  r1cs::R1CSShape,
  spartan::math::Math,
  traits::{evaluation::EvaluationEngineTrait, Engine, TranscriptReprTrait},
  CommitmentKey,
};
use core::marker::PhantomData;
use serde::{Deserialize, Serialize};

/// A trivial implementation of `ComputationCommitmentEngineTrait`
pub struct TrivialCompComputationEngine<E: Engine, EE: EvaluationEngineTrait<E>> {
  _p: PhantomData<E>,
  _p2: PhantomData<EE>,
}

/// Provides an implementation of a trivial commitment
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct TrivialCommitment<E: Engine> {
  S: R1CSShape<E>,
}

/// Provides an implementation of a trivial decommitment
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct TrivialDecommitment<G: Engine> {
  _p: PhantomData<G>,
}

/// Provides an implementation of a trivial evaluation argument
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct TrivialEvaluationArgument<G: Engine> {
  _p: PhantomData<G>,
}

impl<E: Engine> TranscriptReprTrait<E::GE> for TrivialCommitment<E> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    Vec::new()
  }
}

impl<E: Engine, EE: EvaluationEngineTrait<E>> CompCommitmentEngineTrait<E, EE>
  for TrivialCompComputationEngine<E, EE>
{
  type Decommitment = TrivialDecommitment<E>;
  type Commitment = TrivialCommitment<E>;
  type EvaluationArgument = TrivialEvaluationArgument<E>;

  /// commits to R1CS matrices
  fn commit(
    _ck: &CommitmentKey<E>,
    S: &R1CSShape<E>,
  ) -> Result<(Self::Commitment, Self::Decommitment), NovaError> {
    Ok((
      TrivialCommitment { S: S.clone() },
      TrivialDecommitment {
        _p: Default::default(),
      },
    ))
  }

  /// proves an evaluation of R1CS matrices viewed as polynomials
  fn prove(
    _ck: &CommitmentKey<E>,
    _ek: &EE::ProverKey,
    _S: &R1CSShape<E>,
    _decomm: &Self::Decommitment,
    _comm: &Self::Commitment,
    _r: &(&[E::Scalar], &[E::Scalar]),
    _transcript: &mut E::TE,
  ) -> Result<Self::EvaluationArgument, NovaError> {
    Ok(TrivialEvaluationArgument {
      _p: Default::default(),
    })
  }

  /// verifies an evaluation of R1CS matrices viewed as polynomials
  fn verify(
    _vk: &EE::VerifierKey,
    comm: &Self::Commitment,
    r: &(&[E::Scalar], &[E::Scalar]),
    _arg: &Self::EvaluationArgument,
    _transcript: &mut E::TE,
  ) -> Result<(E::Scalar, E::Scalar, E::Scalar), NovaError> {
    let (r_x, r_y) = r;
    let evals = SparsePolynomial::<E>::multi_evaluate(&[&comm.S.A, &comm.S.B, &comm.S.C], r_x, r_y);
    Ok((evals[0], evals[1], evals[2]))
  }
}

mod product;
mod sparse;

use sparse::{SparseEvaluationArgument, SparsePolynomial, SparsePolynomialCommitment};

/// A non-trivial implementation of `CompCommitmentEngineTrait` using Spartan's SPARK compiler
pub struct SparkEngine<E: Engine, EE: EvaluationEngineTrait<E>> {
  _p: PhantomData<E>,
  _p2: PhantomData<EE>,
}

/// An implementation of Spark decommitment
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SparkDecommitment<E: Engine> {
  A: SparsePolynomial<E>,
  B: SparsePolynomial<E>,
  C: SparsePolynomial<E>,
}

impl<G: Engine> SparkDecommitment<G> {
  fn new(S: &R1CSShape<G>) -> Self {
    let ell = (S.num_cons.log_2(), S.num_vars.log_2() + 1);
    let A = SparsePolynomial::new(ell, &S.A);
    let B = SparsePolynomial::new(ell, &S.B);
    let C = SparsePolynomial::new(ell, &S.C);

    Self { A, B, C }
  }

  fn commit(&self, ck: &CommitmentKey<G>) -> SparkCommitment<G> {
    let comm_A = self.A.commit(ck);
    let comm_B = self.B.commit(ck);
    let comm_C = self.C.commit(ck);

    SparkCommitment {
      comm_A,
      comm_B,
      comm_C,
    }
  }
}

/// An implementation of Spark commitment
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SparkCommitment<E: Engine> {
  comm_A: SparsePolynomialCommitment<E>,
  comm_B: SparsePolynomialCommitment<E>,
  comm_C: SparsePolynomialCommitment<E>,
}

impl<E: Engine> TranscriptReprTrait<E::GE> for SparkCommitment<E> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    let mut bytes = self.comm_A.to_transcript_bytes();
    bytes.extend(self.comm_B.to_transcript_bytes());
    bytes.extend(self.comm_C.to_transcript_bytes());
    bytes
  }
}

/// Provides an implementation of a trivial evaluation argument
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SparkEvaluationArgument<E: Engine, EE: EvaluationEngineTrait<E>> {
  arg_A: SparseEvaluationArgument<E, EE>,
  arg_B: SparseEvaluationArgument<E, EE>,
  arg_C: SparseEvaluationArgument<E, EE>,
}

impl<E: Engine, EE: EvaluationEngineTrait<E>> CompCommitmentEngineTrait<E, EE>
  for SparkEngine<E, EE>
{
  type Decommitment = SparkDecommitment<E>;
  type Commitment = SparkCommitment<E>;
  type EvaluationArgument = SparkEvaluationArgument<E, EE>;

  /// commits to R1CS matrices
  fn commit(
    ck: &CommitmentKey<E>,
    S: &R1CSShape<E>,
  ) -> Result<(Self::Commitment, Self::Decommitment), NovaError> {
    let sparse = SparkDecommitment::new(S);
    let comm = sparse.commit(ck);
    Ok((comm, sparse))
  }

  /// proves an evaluation of R1CS matrices viewed as polynomials
  fn prove(
    ck: &CommitmentKey<E>,
    pk_ee: &EE::ProverKey,
    S: &R1CSShape<E>,
    decomm: &Self::Decommitment,
    comm: &Self::Commitment,
    r: &(&[E::Scalar], &[E::Scalar]),
    transcript: &mut E::TE,
  ) -> Result<Self::EvaluationArgument, NovaError> {
    let arg_A =
      SparseEvaluationArgument::prove(ck, pk_ee, &decomm.A, &S.A, &comm.comm_A, r, transcript)?;
    let arg_B =
      SparseEvaluationArgument::prove(ck, pk_ee, &decomm.B, &S.B, &comm.comm_B, r, transcript)?;
    let arg_C =
      SparseEvaluationArgument::prove(ck, pk_ee, &decomm.C, &S.C, &comm.comm_C, r, transcript)?;

    Ok(SparkEvaluationArgument {
      arg_A,
      arg_B,
      arg_C,
    })
  }

  /// verifies an evaluation of R1CS matrices viewed as polynomials
  fn verify(
    vk_ee: &EE::VerifierKey,
    comm: &Self::Commitment,
    r: &(&[E::Scalar], &[E::Scalar]),
    arg: &Self::EvaluationArgument,
    transcript: &mut E::TE,
  ) -> Result<(E::Scalar, E::Scalar, E::Scalar), NovaError> {
    let eval_A = arg.arg_A.verify(vk_ee, &comm.comm_A, r, transcript)?;
    let eval_B = arg.arg_B.verify(vk_ee, &comm.comm_B, r, transcript)?;
    let eval_C = arg.arg_C.verify(vk_ee, &comm.comm_C, r, transcript)?;

    Ok((eval_A, eval_B, eval_C))
  }
}

/// Engine to compute the commitment and decommitment for the Spark protocol
pub trait CompCommitmentEngineTrait<E: Engine, EE: EvaluationEngineTrait<E>> {
  /// A type that holds opening hint
  type Decommitment: Clone + Send + Sync + Serialize + for<'de> Deserialize<'de>;

  /// A type that holds a commitment
  type Commitment: Clone
    + Send
    + Sync
    + TranscriptReprTrait<E::GE>
    + Serialize
    + for<'de> Deserialize<'de>;

  /// A type that holds an evaluation argument
  type EvaluationArgument: Send + Sync + Serialize + for<'de> Deserialize<'de>;

  /// commits to R1CS matrices
  fn commit(
    ck: &CommitmentKey<E>,
    S: &R1CSShape<E>,
  ) -> Result<(Self::Commitment, Self::Decommitment), NovaError>;

  /// proves an evaluation of R1CS matrices viewed as polynomials
  fn prove(
    ck: &CommitmentKey<E>,
    ek: &EE::ProverKey,
    S: &R1CSShape<E>,
    decomm: &Self::Decommitment,
    comm: &Self::Commitment,
    r: &(&[E::Scalar], &[E::Scalar]),
    transcript: &mut E::TE,
  ) -> Result<Self::EvaluationArgument, NovaError>;

  /// verifies an evaluation of R1CS matrices viewed as polynomials and returns verified evaluations
  fn verify(
    vk: &EE::VerifierKey,
    comm: &Self::Commitment,
    r: &(&[E::Scalar], &[E::Scalar]),
    arg: &Self::EvaluationArgument,
    transcript: &mut E::TE,
  ) -> Result<(E::Scalar, E::Scalar, E::Scalar), NovaError>;
}
