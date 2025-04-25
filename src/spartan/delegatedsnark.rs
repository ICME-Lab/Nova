//! This module implements `RelaxedR1CSSNARK` traits using a spark-based approach to prove evaluations of
//! sparse multilinear polynomials involved in Spartan's sum-check protocol, thereby providing a preprocessing SNARK
//! The verifier in this preprocessing SNARK maintains a commitment to R1CS matrices. This is beneficial when using a
//! polynomial commitment scheme in which the verifier's costs is succinct.
//! This code includes experimental optimizations to reduce runtimes and proof sizes.
//! We have not yet proven the security of these optimizations, so this code is subject to significant changes in the future.

//! Choices done: two different transcripts are used: one for prover and one for delegated party:
//! the function in which the transcripts are defined could be thought again, for now it's at highest level
//! See L240
use crate::{
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness, SparseMatrix},
  spartan::{
    polys::{
      eq::EqPolynomial,
      multilinear::{MultilinearPolynomial, SparsePolynomial},
    },
    spark::CompCommitmentEngineTrait,
    sumcheck::SumcheckProof,
    PolyEvalInstance, PolyEvalWitness,
  },
  traits::{
    evaluation::EvaluationEngineTrait,
    snark::{DigestHelperTrait, RelaxedR1CSSNARKTrait},
    Engine, TranscriptEngineTrait,
  },
  Commitment, CommitmentKey,
};
use ff::Field;
use once_cell::sync::OnceCell;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// A type that represents the prover's key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProverKey<E: Engine, EE: EvaluationEngineTrait<E>, CC: CompCommitmentEngineTrait<E>> {
  pk_ee: EE::ProverKey,
  S: R1CSShape<E>,
  decomm: CC::Decommitment,
  comm: CC::Commitment,
}

/// A type that represents the verifier's key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct VerifierKey<E: Engine, EE: EvaluationEngineTrait<E>, CC: CompCommitmentEngineTrait<E>> {
  num_cons: usize,
  num_vars: usize,
  vk_ee: EE::VerifierKey,
  comm: CC::Commitment,
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<E::Scalar>,
}

impl<E: Engine, EE: EvaluationEngineTrait<E>, CC: CompCommitmentEngineTrait<E>>
  VerifierKey<E, EE, CC>
{
  fn new(num_cons: usize, num_vars: usize, S_comm: CC::Commitment, vk_ee: EE::VerifierKey) -> Self {
    VerifierKey {
      num_cons,
      num_vars,
      comm: S_comm,
      vk_ee,
      digest: Default::default(),
    }
  }
}
impl<E: Engine, EE: EvaluationEngineTrait<E>, CC: CompCommitmentEngineTrait<E>> DigestHelperTrait<E>
  for VerifierKey<E, EE, CC>
{
  /// Returns the digest of the verifier's key
  fn digest(&self) -> E::Scalar {
    self
      .digest
      .get_or_try_init(|| {
        let dc = DigestComputer::new(self);
        dc.digest()
      })
      .cloned()
      .expect("Failure to retrieve digest!")
  }
}

impl<E: Engine, EE: EvaluationEngineTrait<E>, CC: CompCommitmentEngineTrait<E>> SimpleDigestible
  for VerifierKey<E, EE, CC>
{
}

/// A succinct proof of knowledge of a witness to a relaxed R1CS instance
/// The proof is produced using Spartan's combination of the sum-check and
/// the commitment to a vector viewed as a polynomial commitment
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RelaxedR1CSSNARK<
  E: Engine,
  EE: EvaluationEngineTrait<E>,
  CC: CompCommitmentEngineTrait<E>,
> {
  sc_proof_outer: SumcheckProof<E>,
  claims_outer: (E::Scalar, E::Scalar, E::Scalar),
  eval_E: E::Scalar,
  sc_proof_inner: SumcheckProof<E>,
  eval_W: E::Scalar,
  sc_proof_batch_prover: SumcheckProof<E>,
  eval_arg_prover: EE::EvaluationArgument,
  evals_batch_prover: Vec<E::Scalar>,

  eval_arg_cc: CC::EvaluationArgument,
  sc_proof_batch_deleg: SumcheckProof<E>,
  eval_arg_deleg: EE::EvaluationArgument,
  evals_batch_deleg: Vec<E::Scalar>,
}

impl<E: Engine, EE: EvaluationEngineTrait<E>, CC: CompCommitmentEngineTrait<E>>
  RelaxedR1CSSNARKTrait<E> for RelaxedR1CSSNARK<E, EE, CC>
{
  type ProverKey = ProverKey<E, EE, CC>;
  type VerifierKey = VerifierKey<E, EE, CC>;

  fn ck_floor() -> Box<dyn for<'a> Fn(&'a R1CSShape<E>) -> usize> {
    Box::new(|shape: &R1CSShape<E>| -> usize {
      // the commitment key should be large enough to commit to the R1CS matrices
      shape.A.len() + shape.B.len() + shape.C.len()
    })
  }

  fn setup(
    ck: &CommitmentKey<E>,
    S: &R1CSShape<E>,
  ) -> Result<(Self::ProverKey, Self::VerifierKey), NovaError> {
    let (pk_ee, vk_ee) = EE::setup(ck);

    let S = S.pad();

    let (comm, decomm) = CC::commit(ck, &S)?;

    let vk = VerifierKey::new(S.num_cons, S.num_vars, comm.clone(), vk_ee);

    let pk = ProverKey {
      pk_ee,
      S,
      comm,
      decomm,
    };

    Ok((pk, vk))
  }

  /// produces a succinct proof of satisfiability of a RelaxedR1CS instance
  fn prove(
    ck: &CommitmentKey<E>,
    pk: &Self::ProverKey,
    _S: &R1CSShape<E>,
    U: &RelaxedR1CSInstance<E>,
    W: &RelaxedR1CSWitness<E>,
  ) -> Result<Self, NovaError> {
    let (prover_step, r) = <Self as Delegatable<E>>::prover_step(ck, pk, _S, U, W)?;

    let r: (&[E::Scalar], &[E::Scalar]) = (r.0.as_slice(), r.1.as_slice());
    let delegated_step = <Self as Delegatable<E>>::delegated_step(ck, pk, _S, r)?;

    let proof = <Self as Delegatable<E>>::combine_proofs(prover_step, delegated_step);

    Ok(proof)
  }

  /// verifies a proof of satisfiability of a RelaxedR1CS instance
  fn verify(&self, vk: &Self::VerifierKey, U: &RelaxedR1CSInstance<E>) -> Result<(), NovaError> {
    let mut transcript = E::TE::new(b"RelaxedR1CSSNARK");

    // append the commitment to R1CS matrices and the RelaxedR1CSInstance to the transcript
    transcript.absorb(b"C", &vk.comm);
    transcript.absorb(b"U", U);

    let (num_rounds_x, num_rounds_y) = (
      (vk.num_cons as f64).log2() as usize,
      ((vk.num_vars as f64).log2() as usize + 1),
    );

    // outer sum-check
    let tau = (0..num_rounds_x)
      .map(|_i| transcript.squeeze(b"t"))
      .collect::<Result<Vec<E::Scalar>, NovaError>>()?;

    let (claim_outer_final, r_x) =
      self
        .sc_proof_outer
        .verify(E::Scalar::ZERO, num_rounds_x, 3, &mut transcript)?;

    // verify claim_outer_final
    let (claim_Az, claim_Bz, claim_Cz) = self.claims_outer;
    let taus_bound_rx = EqPolynomial::new(tau).evaluate(&r_x);
    let claim_outer_final_expected =
      taus_bound_rx * (claim_Az * claim_Bz - U.u * claim_Cz - self.eval_E);
    if claim_outer_final != claim_outer_final_expected {
      return Err(NovaError::InvalidSumcheckProof);
    }

    transcript.absorb(
      b"claims_outer",
      &[
        self.claims_outer.0,
        self.claims_outer.1,
        self.claims_outer.2,
        self.eval_E,
      ]
      .as_slice(),
    );

    // inner sum-check
    let r = transcript.squeeze(b"r")?;
    let claim_inner_joint =
      self.claims_outer.0 + r * self.claims_outer.1 + r * r * self.claims_outer.2;

    let (claim_inner_final, r_y) =
      self
        .sc_proof_inner
        .verify(claim_inner_joint, num_rounds_y, 2, &mut transcript)?;

    // verify claim_inner_final
    let eval_Z = {
      let eval_X = {
        // constant term
        let mut poly_X = vec![U.u];
        //remaining inputs
        poly_X.extend((0..U.X.len()).map(|i| U.X[i]).collect::<Vec<E::Scalar>>());
        SparsePolynomial::new((vk.num_vars as f64).log2() as usize, poly_X).evaluate(&r_y[1..])
      };
      (E::Scalar::ONE - r_y[0]) * self.eval_W + r_y[0] * eval_X
    };

    let mut u_vec_prover: Vec<PolyEvalInstance<E>> = Vec::new();
    u_vec_prover.push(PolyEvalInstance {
      c: U.comm_W,
      x: r_y[1..].to_vec(),
      e: self.eval_W,
    });

    u_vec_prover.push(PolyEvalInstance {
      c: U.comm_E,
      x: r_x.clone(),
      e: self.eval_E,
    });

    let u_vec_padded_prover = PolyEvalInstance::pad(&u_vec_prover); // pad the evaluation points

    let powers = |s: &E::Scalar, n: usize| -> Vec<E::Scalar> {
      assert!(n >= 1);
      let mut powers = Vec::new();
      powers.push(E::Scalar::ONE);
      for i in 1..n {
        powers.push(powers[i - 1] * s);
      }
      powers
    };

    // generate a challenge
    let rho = transcript.squeeze(b"r")?;
    let num_claims = u_vec_prover.len();
    let powers_of_rho = powers(&rho, num_claims);
    let claim_batch_joint_prover = u_vec_prover
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(u, p)| u.e * p)
      .fold(E::Scalar::ZERO, |acc, item| acc + item);

    let num_rounds_z = u_vec_padded_prover[0].x.len();
    let (claim_batch_prover_final, r_z) = self.sc_proof_batch_prover.verify(
      claim_batch_joint_prover,
      num_rounds_z,
      2,
      &mut transcript,
    )?;

    let claim_batch_prover_final_expected = {
      let poly_rz = EqPolynomial::new(r_z.clone());
      let evals = u_vec_padded_prover
        .iter()
        .map(|u| poly_rz.evaluate(&u.x))
        .collect::<Vec<E::Scalar>>();

      evals
        .iter()
        .zip(self.evals_batch_prover.iter())
        .zip(powers_of_rho.iter())
        .map(|((e_i, p_i), rho_i)| *e_i * *p_i * rho_i)
        .fold(E::Scalar::ZERO, |acc, item| acc + item)
    };

    if claim_batch_prover_final != claim_batch_prover_final_expected {
      return Err(NovaError::InvalidSumcheckProof);
    }

    transcript.absorb(b"l", &self.evals_batch_prover.as_slice());

    // we now combine evaluation claims at the same point rz into one
    let gamma = transcript.squeeze(b"g")?;
    let powers_of_gamma: Vec<E::Scalar> = powers(&gamma, num_claims);
    let comm_joint_prover = u_vec_padded_prover
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(u, g_i)| u.c * *g_i)
      .fold(Commitment::<E>::default(), |acc, item| acc + item);
    let eval_joint_prover = self
      .evals_batch_prover
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(e, g_i)| *e * *g_i)
      .fold(E::Scalar::ZERO, |acc, item| acc + item);

    // verify
    EE::verify(
      &vk.vk_ee,
      &mut transcript,
      &comm_joint_prover,
      &r_z,
      &eval_joint_prover,
      &self.eval_arg_prover,
    )?;

    // verify evaluation argument to retrieve evaluations of R1CS matrices

    // CHANEED TO USE A DIFFERENT TRANSCRIPT
    // this second transcript is fed with r_x and r_y
    let mut transcript_delegated = E::TE::new(b"RelaxedR1CSSNARK_Delegated");
    transcript_delegated.absorb(b"r_x", &r_x.as_slice());
    transcript_delegated.absorb(b"r_y", &r_y.as_slice());
    let (eval_A, eval_B, eval_C, u_vec_deleg) = CC::verify(
      &vk.comm,
      &(&r_x, &r_y),
      &self.eval_arg_cc,
      &mut transcript_delegated,
    )?;

    let claim_inner_final_expected = (eval_A + r * eval_B + r * r * eval_C) * eval_Z;
    if claim_inner_final != claim_inner_final_expected {
      return Err(NovaError::InvalidSumcheckProof);
    }

    let u_vec_padded_deleg = PolyEvalInstance::pad(&u_vec_deleg); // pad the evaluation points

    // generate a challenge
    let rho = transcript_delegated.squeeze(b"r")?;
    let num_claims = u_vec_deleg.len();
    let powers_of_rho = powers(&rho, num_claims);
    let claim_batch_joint_deleg = u_vec_deleg
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(u, p)| u.e * p)
      .fold(E::Scalar::ZERO, |acc, item| acc + item);

    let num_rounds_z = u_vec_padded_deleg[0].x.len();
    let (claim_batch_deleg_final, r_z) = self.sc_proof_batch_deleg.verify(
      claim_batch_joint_deleg,
      num_rounds_z,
      2,
      &mut transcript_delegated,
    )?;

    let claim_batch_deleg_final_expected = {
      let poly_rz = EqPolynomial::new(r_z.clone());
      let evals = u_vec_padded_deleg
        .iter()
        .map(|u| poly_rz.evaluate(&u.x))
        .collect::<Vec<E::Scalar>>();

      evals
        .iter()
        .zip(self.evals_batch_deleg.iter())
        .zip(powers_of_rho.iter())
        .map(|((e_i, p_i), rho_i)| *e_i * *p_i * rho_i)
        .fold(E::Scalar::ZERO, |acc, item| acc + item)
    };

    if claim_batch_deleg_final != claim_batch_deleg_final_expected {
      return Err(NovaError::InvalidSumcheckProof);
    }

    transcript_delegated.absorb(b"l", &self.evals_batch_deleg.as_slice());

    // we now combine evaluation claims at the same point rz into one
    let gamma = transcript_delegated.squeeze(b"g")?;
    let powers_of_gamma: Vec<E::Scalar> = powers(&gamma, num_claims);
    let comm_joint_deleg = u_vec_padded_deleg
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(u, g_i)| u.c * *g_i)
      .fold(Commitment::<E>::default(), |acc, item| acc + item);
    let eval_joint_deleg = self
      .evals_batch_deleg
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(e, g_i)| *e * *g_i)
      .fold(E::Scalar::ZERO, |acc, item| acc + item);

    // verify
    EE::verify(
      &vk.vk_ee,
      &mut transcript_delegated,
      &comm_joint_deleg,
      &r_z,
      &eval_joint_deleg,
      &self.eval_arg_deleg,
    )?;

    Ok(())
  }
}

/// A trait that represents a delegatable SNARK
pub trait Delegatable<E: Engine>:
  RelaxedR1CSSNARKTrait<E> + Serialize + for<'de> Deserialize<'de>
{
  /// The prover's proof part
  type ProverProofPart: Send + Serialize + for<'de> Deserialize<'de>;
  /// The delegated party's proof part
  type DelegatedProofPart: Send + Serialize + for<'de> Deserialize<'de>;

  /// Computes the prover's proof part
  fn prover_step(
    ck: &CommitmentKey<E>,
    pk: &<Self as RelaxedR1CSSNARKTrait<E>>::ProverKey,
    _S: &R1CSShape<E>,
    U: &RelaxedR1CSInstance<E>,
    W: &RelaxedR1CSWitness<E>,
  ) -> Result<(Self::ProverProofPart, (Vec<E::Scalar>, Vec<E::Scalar>)), NovaError>;

  /// Computes the delegated party's proof part
  fn delegated_step(
    ck: &CommitmentKey<E>,
    pk: &<Self as RelaxedR1CSSNARKTrait<E>>::ProverKey,
    _S: &R1CSShape<E>,
    r: (&[E::Scalar], &[E::Scalar]),
  ) -> Result<Self::DelegatedProofPart, NovaError>;

  /// Combines the prover's and delegated party's proof parts
  fn combine_proofs(
    prover_proof: Self::ProverProofPart,
    delegated_proof: Self::DelegatedProofPart,
  ) -> Self;
}

/// A type that represents the witness related part of the proof
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RelaxedR1CSProver<E: Engine, EE: EvaluationEngineTrait<E>> {
  sc_proof_outer: SumcheckProof<E>,
  claims_outer: (E::Scalar, E::Scalar, E::Scalar),
  eval_E: E::Scalar,
  sc_proof_inner: SumcheckProof<E>,
  eval_W: E::Scalar,
  sc_proof_batch_prover: SumcheckProof<E>,
  eval_arg_prover: EE::EvaluationArgument,
  evals_batch_prover: Vec<E::Scalar>,
}

/// A type that represents the non-witness related part of the proof
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RelaxedR1CSDelegated<
  E: Engine,
  EE: EvaluationEngineTrait<E>,
  CC: CompCommitmentEngineTrait<E>,
> {
  eval_arg_cc: CC::EvaluationArgument,
  sc_proof_batch_deleg: SumcheckProof<E>,
  eval_arg_deleg: EE::EvaluationArgument,
  evals_batch_deleg: Vec<E::Scalar>,
}

impl<E: Engine, EE: EvaluationEngineTrait<E>, CC: CompCommitmentEngineTrait<E>> Delegatable<E>
  for RelaxedR1CSSNARK<E, EE, CC>
{
  type ProverProofPart = RelaxedR1CSProver<E, EE>;
  type DelegatedProofPart = RelaxedR1CSDelegated<E, EE, CC>;

  /// Computes the witness related part of the proof, executed by the prover
  fn prover_step(
    ck: &CommitmentKey<E>,
    pk: &<Self as RelaxedR1CSSNARKTrait<E>>::ProverKey,
    _S: &R1CSShape<E>,
    U: &RelaxedR1CSInstance<E>,
    W: &RelaxedR1CSWitness<E>,
  ) -> Result<(RelaxedR1CSProver<E, EE>, (Vec<E::Scalar>, Vec<E::Scalar>)), NovaError> {
    let W = W.pad(&pk.S); // pad the witness
    let mut transcript = E::TE::new(b"RelaxedR1CSSNARK");

    // sanity check that R1CSShape has certain size characteristics
    assert_eq!(pk.S.num_cons.next_power_of_two(), pk.S.num_cons);
    assert_eq!(pk.S.num_vars.next_power_of_two(), pk.S.num_vars);
    assert_eq!(pk.S.num_io.next_power_of_two(), pk.S.num_io);
    assert!(pk.S.num_io < pk.S.num_vars);

    // append the commitment to R1CS matrices and the RelaxedR1CSInstance to the transcript
    transcript.absorb(b"C", &pk.comm);
    transcript.absorb(b"U", U);

    // compute the full satisfying assignment by concatenating W.W, U.u, and U.X
    let mut z = [W.W.clone(), vec![U.u], U.X.clone()].concat();

    let (num_rounds_x, num_rounds_y) = (
      (pk.S.num_cons as f64).log2() as usize,
      ((pk.S.num_vars as f64).log2() as usize + 1),
    );

    // outer sum-check
    let tau = (0..num_rounds_x)
      .map(|_i| transcript.squeeze(b"t"))
      .collect::<Result<Vec<E::Scalar>, NovaError>>()?;

    let mut poly_tau = MultilinearPolynomial::new(EqPolynomial::new(tau).evals());
    let (mut poly_Az, mut poly_Bz, poly_Cz, mut poly_uCz_E) = {
      let (poly_Az, poly_Bz, poly_Cz) = pk.S.multiply_vec(&z)?;
      let poly_uCz_E = (0..pk.S.num_cons)
        .map(|i| U.u * poly_Cz[i] + W.E[i])
        .collect::<Vec<E::Scalar>>();
      (
        MultilinearPolynomial::new(poly_Az),
        MultilinearPolynomial::new(poly_Bz),
        MultilinearPolynomial::new(poly_Cz),
        MultilinearPolynomial::new(poly_uCz_E),
      )
    };

    let comb_func_outer =
      |poly_A_comp: &E::Scalar,
       poly_B_comp: &E::Scalar,
       poly_C_comp: &E::Scalar,
       poly_D_comp: &E::Scalar|
       -> E::Scalar { *poly_A_comp * (*poly_B_comp * *poly_C_comp - *poly_D_comp) };
    let (sc_proof_outer, r_x, claims_outer) = SumcheckProof::prove_cubic_with_additive_term(
      &E::Scalar::ZERO, // claim is zero
      num_rounds_x,
      &mut poly_tau,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_uCz_E,
      comb_func_outer,
      &mut transcript,
    )?;

    // claims from the end of sum-check
    let (claim_Az, claim_Bz): (E::Scalar, E::Scalar) = (claims_outer[1], claims_outer[2]);
    let claim_Cz = poly_Cz.evaluate(&r_x);
    let eval_E = MultilinearPolynomial::new(W.E.clone()).evaluate(&r_x);
    transcript.absorb(
      b"claims_outer",
      &[claim_Az, claim_Bz, claim_Cz, eval_E].as_slice(),
    );

    // inner sum-check
    let r = transcript.squeeze(b"r")?;
    let claim_inner_joint = claim_Az + r * claim_Bz + r * r * claim_Cz;

    let poly_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(r_x.clone()).evals();

      // Bounds "row" variables of (A, B, C) matrices viewed as 2d multilinear polynomials
      let compute_eval_table_sparse =
        |S: &R1CSShape<E>, rx: &[E::Scalar]| -> (Vec<E::Scalar>, Vec<E::Scalar>, Vec<E::Scalar>) {
          assert_eq!(rx.len(), S.num_cons);

          let inner = |M: &SparseMatrix<E::Scalar>, M_evals: &mut Vec<E::Scalar>| {
            for (row, col, val) in M.iter() {
              M_evals[col] += rx[row] * val;
            }
          };

          let (A_evals, (B_evals, C_evals)) = rayon::join(
            || {
              let mut A_evals: Vec<E::Scalar> = vec![E::Scalar::ZERO; 2 * S.num_vars];
              inner(&S.A, &mut A_evals);
              A_evals
            },
            || {
              rayon::join(
                || {
                  let mut B_evals: Vec<E::Scalar> = vec![E::Scalar::ZERO; 2 * S.num_vars];
                  inner(&S.B, &mut B_evals);
                  B_evals
                },
                || {
                  let mut C_evals: Vec<E::Scalar> = vec![E::Scalar::ZERO; 2 * S.num_vars];
                  inner(&S.C, &mut C_evals);
                  C_evals
                },
              )
            },
          );

          (A_evals, B_evals, C_evals)
        };

      let (evals_A, evals_B, evals_C) = compute_eval_table_sparse(&pk.S, &evals_rx);

      assert_eq!(evals_A.len(), evals_B.len());
      assert_eq!(evals_A.len(), evals_C.len());
      (0..evals_A.len())
        .into_par_iter()
        .map(|i| evals_A[i] + r * evals_B[i] + r * r * evals_C[i])
        .collect::<Vec<E::Scalar>>()
    };

    let poly_z = {
      z.resize(pk.S.num_vars * 2, E::Scalar::ZERO);
      z
    };

    let comb_func = |poly_A_comp: &E::Scalar, poly_B_comp: &E::Scalar| -> E::Scalar {
      *poly_A_comp * *poly_B_comp
    };
    let (sc_proof_inner, r_y, _claims_inner) = SumcheckProof::prove_quad(
      &claim_inner_joint,
      num_rounds_y,
      &mut MultilinearPolynomial::new(poly_ABC),
      &mut MultilinearPolynomial::new(poly_z),
      comb_func,
      &mut transcript,
    )?;

    let eval_W = MultilinearPolynomial::evaluate_with(&W.W, &r_y[1..]);
    let mut w_u_vec = Vec::new();
    w_u_vec.push((
      PolyEvalWitness { p: W.W.clone() },
      PolyEvalInstance {
        c: U.comm_W,
        x: r_y[1..].to_vec(),
        e: eval_W,
      },
    ));

    w_u_vec.push((
      PolyEvalWitness { p: W.E },
      PolyEvalInstance {
        c: U.comm_E,
        x: r_x.clone(),
        e: eval_E,
      },
    ));

    // We will now reduce a vector of claims of evaluations at different points into claims about them at the same point.
    // For example, eval_W =? W(r_y[1..]) and eval_W =? E(r_x) into
    // two claims: eval_W_prime =? W(rz) and eval_E_prime =? E(rz)
    // We can them combine the two into one: eval_W_prime + gamma * eval_E_prime =? (W + gamma*E)(rz),
    // where gamma is a public challenge
    // Since commitments to W and E are homomorphic, the verifier can compute a commitment
    // to the batched polynomial.
    assert!(w_u_vec.len() >= 2);

    let (w_vec, u_vec): (Vec<PolyEvalWitness<E>>, Vec<PolyEvalInstance<E>>) =
      w_u_vec.into_iter().unzip();
    let w_vec_padded = PolyEvalWitness::pad(&w_vec); // pad the polynomials to be of the same size
    let u_vec_padded = PolyEvalInstance::pad(&u_vec); // pad the evaluation points

    let powers = |s: &E::Scalar, n: usize| -> Vec<E::Scalar> {
      assert!(n >= 1);
      let mut powers = Vec::new();
      powers.push(E::Scalar::ONE);
      for i in 1..n {
        powers.push(powers[i - 1] * s);
      }
      powers
    };

    // generate a challenge
    let rho = transcript.squeeze(b"r")?;
    let num_claims = w_vec_padded.len();
    let powers_of_rho = powers(&rho, num_claims);
    let claim_batch_joint = u_vec_padded
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(u, p)| u.e * p)
      .fold(E::Scalar::ZERO, |acc, item| acc + item);

    let mut polys_left: Vec<MultilinearPolynomial<E::Scalar>> = w_vec_padded
      .iter()
      .map(|w| MultilinearPolynomial::new(w.p.clone()))
      .collect();
    let mut polys_right: Vec<MultilinearPolynomial<E::Scalar>> = u_vec_padded
      .iter()
      .map(|u| MultilinearPolynomial::new(EqPolynomial::new(u.x.clone()).evals()))
      .collect();

    let num_rounds_z = u_vec_padded[0].x.len();
    let comb_func = |poly_A_comp: &E::Scalar, poly_B_comp: &E::Scalar| -> E::Scalar {
      *poly_A_comp * *poly_B_comp
    };
    let (sc_proof_batch_prover, r_z, claims_batch) = SumcheckProof::prove_quad_batch_scaled(
      &claim_batch_joint,
      num_rounds_z,
      &mut polys_left,
      &mut polys_right,
      &powers_of_rho,
      comb_func,
      &mut transcript,
    )?;

    let (claims_batch_left, _): (Vec<E::Scalar>, Vec<E::Scalar>) = claims_batch;

    transcript.absorb(b"l", &claims_batch_left.as_slice());

    // we now combine evaluation claims at the same point rz into one
    let gamma = transcript.squeeze(b"g")?;
    let powers_of_gamma: Vec<E::Scalar> = powers(&gamma, num_claims);
    let comm_joint = u_vec_padded
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(u, g_i)| u.c * *g_i)
      .fold(Commitment::<E>::default(), |acc, item| acc + item);
    let poly_joint = PolyEvalWitness::weighted_sum(&w_vec_padded, &powers_of_gamma);
    let eval_joint = claims_batch_left
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(e, g_i)| *e * *g_i)
      .fold(E::Scalar::ZERO, |acc, item| acc + item);

    let eval_arg_prover = EE::prove(
      ck,
      &pk.pk_ee,
      &mut transcript,
      &comm_joint,
      &poly_joint.p,
      &r_z,
      &eval_joint,
    )?;
    Ok((
      Self::ProverProofPart {
        sc_proof_outer,
        claims_outer: (claim_Az, claim_Bz, claim_Cz),
        eval_E,
        sc_proof_inner,
        eval_W,
        sc_proof_batch_prover,
        eval_arg_prover,
        evals_batch_prover: claims_batch_left,
      },
      (r_x, r_y),
    ))
  }

  /// Computes the non-witness related part of the proof, executed by a delegated party
  fn delegated_step(
    ck: &CommitmentKey<E>,
    pk: &<Self as RelaxedR1CSSNARKTrait<E>>::ProverKey,
    _S: &R1CSShape<E>,
    r: (&[E::Scalar], &[E::Scalar]),
  ) -> Result<Self::DelegatedProofPart, NovaError> {
    let mut transcript = E::TE::new(b"RelaxedR1CSSNARK_Delegated");
    transcript.absorb(b"r_x", &r.0);
    transcript.absorb(b"r_y", &r.1);
    let (eval_arg_cc, w_u_vec) = CC::prove(ck, &pk.S, &pk.decomm, &pk.comm, &r, &mut transcript)?;
    let (w_vec, u_vec): (Vec<PolyEvalWitness<E>>, Vec<PolyEvalInstance<E>>) =
      w_u_vec.into_iter().unzip();
    let w_vec_padded = PolyEvalWitness::pad(&w_vec); // pad the polynomials to be of the same size
    let u_vec_padded = PolyEvalInstance::pad(&u_vec); // pad the evaluation points

    let powers = |s: &E::Scalar, n: usize| -> Vec<E::Scalar> {
      assert!(n >= 1);
      let mut powers = Vec::new();
      powers.push(E::Scalar::ONE);
      for i in 1..n {
        powers.push(powers[i - 1] * s);
      }
      powers
    };

    // generate a challenge
    let rho = transcript.squeeze(b"r")?;
    let num_claims = w_vec_padded.len();
    let powers_of_rho = powers(&rho, num_claims);
    let claim_batch_joint = u_vec_padded
      .iter()
      .zip(powers_of_rho.iter())
      .map(|(u, p)| u.e * p)
      .fold(E::Scalar::ZERO, |acc, item| acc + item);

    let mut polys_left: Vec<MultilinearPolynomial<E::Scalar>> = w_vec_padded
      .iter()
      .map(|w| MultilinearPolynomial::new(w.p.clone()))
      .collect();
    let mut polys_right: Vec<MultilinearPolynomial<E::Scalar>> = u_vec_padded
      .iter()
      .map(|u| MultilinearPolynomial::new(EqPolynomial::new(u.x.clone()).evals()))
      .collect();

    let num_rounds_z = u_vec_padded[0].x.len();
    let comb_func = |poly_A_comp: &E::Scalar, poly_B_comp: &E::Scalar| -> E::Scalar {
      *poly_A_comp * *poly_B_comp
    };
    let (sc_proof_batch_deleg, r_z, claims_batch) = SumcheckProof::<E>::prove_quad_batch_scaled(
      &claim_batch_joint,
      num_rounds_z,
      &mut polys_left,
      &mut polys_right,
      &powers_of_rho,
      comb_func,
      &mut transcript,
    )?;

    let (claims_batch_left, _): (Vec<E::Scalar>, Vec<E::Scalar>) = claims_batch;

    transcript.absorb(b"l", &claims_batch_left.as_slice());

    // we now combine evaluation claims at the same point rz into one
    let gamma = transcript.squeeze(b"g")?;
    let powers_of_gamma: Vec<E::Scalar> = powers(&gamma, num_claims);
    let comm_joint = u_vec_padded
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(u, g_i)| u.c * *g_i)
      .fold(Commitment::<E>::default(), |acc, item| acc + item);
    let poly_joint = PolyEvalWitness::weighted_sum(&w_vec_padded, &powers_of_gamma);
    let eval_joint = claims_batch_left
      .iter()
      .zip(powers_of_gamma.iter())
      .map(|(e, g_i)| *e * *g_i)
      .fold(E::Scalar::ZERO, |acc, item| acc + item);

    let eval_arg_deleg = EE::prove(
      ck,
      &pk.pk_ee,
      &mut transcript,
      &comm_joint,
      &poly_joint.p,
      &r_z,
      &eval_joint,
    )?;

    Ok(Self::DelegatedProofPart {
      eval_arg_cc,
      sc_proof_batch_deleg,
      eval_arg_deleg,
      evals_batch_deleg: claims_batch_left,
    })
  }

  fn combine_proofs(
    prover_proof: Self::ProverProofPart,
    delegated_proof: Self::DelegatedProofPart,
  ) -> Self {
    RelaxedR1CSSNARK {
      sc_proof_outer: prover_proof.sc_proof_outer,
      claims_outer: prover_proof.claims_outer,
      eval_E: prover_proof.eval_E,
      sc_proof_inner: prover_proof.sc_proof_inner,
      eval_W: prover_proof.eval_W,
      sc_proof_batch_prover: prover_proof.sc_proof_batch_prover,
      sc_proof_batch_deleg: delegated_proof.sc_proof_batch_deleg,
      evals_batch_prover: prover_proof.evals_batch_prover,
      evals_batch_deleg: delegated_proof.evals_batch_deleg,
      eval_arg_prover: prover_proof.eval_arg_prover,
      eval_arg_deleg: delegated_proof.eval_arg_deleg,
      eval_arg_cc: delegated_proof.eval_arg_cc,
    }
  }
}
