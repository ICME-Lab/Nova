//! This module implements `CompCommitmentEngineTrait` using Spartan's SPARK compiler
//! We also provide a trivial implementation that has the verifier evaluate the sparse polynomials
use crate::{
  errors::NovaError,
  r1cs::R1CSShape,
  spartan::{math::Math, PolyEvalInstance, PolyEvalWitness},
  traits::{evaluation::EvaluationEngineTrait, Engine, TranscriptReprTrait},
  CommitmentKey,
};
use core::marker::PhantomData;
use serde::{Deserialize, Serialize};

/// Engine to compute the commitment and decommitment for the Spark protocol
pub trait CompCommitmentEngineTrait<E: Engine> {
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
    S: &R1CSShape<E>,
    decomm: &Self::Decommitment,
    comm: &Self::Commitment,
    r: &(&[E::Scalar], &[E::Scalar]),
    transcript: &mut E::TE,
  ) -> Result<
    (
      Self::EvaluationArgument,
      Vec<(PolyEvalWitness<E>, PolyEvalInstance<E>)>,
    ),
    NovaError,
  >;

  /// verifies an evaluation of R1CS matrices viewed as polynomials and returns verified evaluations
  fn verify(
    comm: &Self::Commitment,
    r: &(&[E::Scalar], &[E::Scalar]),
    arg: &Self::EvaluationArgument,
    transcript: &mut E::TE,
  ) -> Result<(E::Scalar, E::Scalar, E::Scalar, Vec<PolyEvalInstance<E>>), NovaError>;
}

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

impl<E: Engine, EE: EvaluationEngineTrait<E>> CompCommitmentEngineTrait<E>
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
    _S: &R1CSShape<E>,
    _decomm: &Self::Decommitment,
    _comm: &Self::Commitment,
    _r: &(&[E::Scalar], &[E::Scalar]),
    _transcript: &mut E::TE,
  ) -> Result<
    (
      Self::EvaluationArgument,
      Vec<(PolyEvalWitness<E>, PolyEvalInstance<E>)>,
    ),
    NovaError,
  > {
    Ok((
      TrivialEvaluationArgument {
        _p: Default::default(),
      },
      Vec::new(),
    ))
  }

  /// verifies an evaluation of R1CS matrices viewed as polynomials
  fn verify(
    comm: &Self::Commitment,
    r: &(&[E::Scalar], &[E::Scalar]),
    _arg: &Self::EvaluationArgument,
    _transcript: &mut E::TE,
  ) -> Result<(E::Scalar, E::Scalar, E::Scalar, Vec<PolyEvalInstance<E>>), NovaError> {
    let (r_x, r_y) = r;
    let evals = SparsePolynomial::<E>::multi_evaluate(&[&comm.S.A, &comm.S.B, &comm.S.C], r_x, r_y);
    Ok((evals[0], evals[1], evals[2], Vec::new()))
  }
}

mod product;
mod sparse;

use sparse::{SparseEvaluationArgument, SparsePolynomial, SparsePolynomialCommitment};

/// A non-trivial implementation of `CompCommitmentEngineTrait` using Spartan's SPARK compiler
pub struct SparkEngine<E: Engine> {
  _p: PhantomData<E>,
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
pub struct SparkEvaluationArgument<E: Engine> {
  arg_A: SparseEvaluationArgument<E>,
  arg_B: SparseEvaluationArgument<E>,
  arg_C: SparseEvaluationArgument<E>,
}

impl<E: Engine> CompCommitmentEngineTrait<E> for SparkEngine<E> {
  type Decommitment = SparkDecommitment<E>;
  type Commitment = SparkCommitment<E>;
  type EvaluationArgument = SparkEvaluationArgument<E>;

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
    S: &R1CSShape<E>,
    decomm: &Self::Decommitment,
    comm: &Self::Commitment,
    r: &(&[E::Scalar], &[E::Scalar]),
    transcript: &mut E::TE,
  ) -> Result<
    (
      Self::EvaluationArgument,
      Vec<(PolyEvalWitness<E>, PolyEvalInstance<E>)>,
    ),
    NovaError,
  > {
    let (arg_A, u_w_vec_A) =
      SparseEvaluationArgument::prove(ck, &decomm.A, &S.A, &comm.comm_A, r, transcript)?;
    let (arg_B, u_w_vec_B) =
      SparseEvaluationArgument::prove(ck, &decomm.B, &S.B, &comm.comm_B, r, transcript)?;
    let (arg_C, u_w_vec_C) =
      SparseEvaluationArgument::prove(ck, &decomm.C, &S.C, &comm.comm_C, r, transcript)?;

    let u_w_vec = {
      let mut u_w_vec = u_w_vec_A;
      u_w_vec.extend(u_w_vec_B);
      u_w_vec.extend(u_w_vec_C);
      u_w_vec
    };

    Ok((
      SparkEvaluationArgument {
        arg_A,
        arg_B,
        arg_C,
      },
      u_w_vec,
    ))
  }

  /// verifies an evaluation of R1CS matrices viewed as polynomials
  fn verify(
    comm: &Self::Commitment,
    r: &(&[E::Scalar], &[E::Scalar]),
    arg: &Self::EvaluationArgument,
    transcript: &mut E::TE,
  ) -> Result<(E::Scalar, E::Scalar, E::Scalar, Vec<PolyEvalInstance<E>>), NovaError> {
    let (eval_A, u_vec_A) = arg.arg_A.verify(&comm.comm_A, r, transcript)?;
    let (eval_B, u_vec_B) = arg.arg_B.verify(&comm.comm_B, r, transcript)?;
    let (eval_C, u_vec_C) = arg.arg_C.verify(&comm.comm_C, r, transcript)?;

    let u_vec = {
      let mut u_vec = u_vec_A;
      u_vec.extend(u_vec_B);
      u_vec.extend(u_vec_C);
      u_vec
    };

    Ok((eval_A, eval_B, eval_C, u_vec))
  }
}
