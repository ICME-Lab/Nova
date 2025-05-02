//! A Nova-style implementation of CCS (Custom Constraint Systems)
//! supporting witness commitments, satisfiability checks, folding, and sampling.

use crate::{
  constants::{BN_LIMB_WIDTH, BN_N_LIMBS},
  digest::{DigestComputer, SimpleDigestible},
  errors::NovaError,
  gadgets::{
    nonnative::{bignat::nat_to_limbs, util::f_to_nat},
    utils::scalar_as_base,
  },
  traits::{
    commitment::CommitmentEngineTrait, AbsorbInRO2Trait, AbsorbInROTrait, Engine, TranscriptReprTrait,
  },
  Commitment, CommitmentKey, CE, DerandKey,
};
use core::cmp::max;
use ff::Field;
use once_cell::sync::OnceCell;
use rand_core::OsRng;
use crate::traits::ROTrait;
use serde::{Deserialize, Serialize};
use rayon::prelude::*;

use crate::r1cs::sparse::SparseMatrix;

/// A CCS shape object: defines constraints via linear combinations of matrices
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CCSShape<E: Engine> {
  pub(crate) num_cons: usize,
  pub(crate) num_vars: usize,
  pub(crate) num_io: usize,
  pub(crate) Ms: Vec<SparseMatrix<E::Scalar>>,
  pub(crate) cSs: Vec<(E::Scalar, Vec<usize>)>,
  #[serde(skip, default = "OnceCell::new")]
  pub(crate) digest: OnceCell<E::Scalar>,
}

impl<E: Engine> SimpleDigestible for CCSShape<E> {}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CCSInstance<E: Engine> {
  pub(crate) comm_W: Commitment<E>,
  pub(crate) X: Vec<E::Scalar>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CCSWitness<E: Engine> {
  pub(crate) W: Vec<E::Scalar>,
  pub(crate) r_W: E::Scalar,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CCSRelaxedWitness<E: Engine> {
  pub(crate) W: Vec<E::Scalar>,
  pub(crate) r_W: E::Scalar,
  pub(crate) E: Vec<E::Scalar>,
  pub(crate) r_E: E::Scalar,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CCSRelaxedInstance<E: Engine> {
  pub(crate) comm_W: Commitment<E>,
  pub(crate) comm_E: Commitment<E>,
  pub(crate) X: Vec<E::Scalar>,
  pub(crate) u: E::Scalar,
}

pub type CCSCommitmentKeyHint<E> = dyn Fn(&CCSShape<E>) -> usize;


impl<E: Engine> CCSShape<E> {
  pub fn new(
    num_cons: usize,
    num_vars: usize,
    num_io: usize,
    Ms: Vec<SparseMatrix<E::Scalar>>,
    cSs: Vec<(E::Scalar, Vec<usize>)>,
  ) -> Self {
    Self {
      num_cons,
      num_vars,
      num_io,
      Ms,
      cSs,
      digest: OnceCell::new(),
    }
  }

  pub fn commitment_key(&self, ck_hint: &CCSCommitmentKeyHint<E>) -> CommitmentKey<E> {
    let hint = ck_hint(self);
    E::CE::setup(b"ccs-ck", max(max(self.num_cons, self.num_vars), hint))
  }

  #[allow(unused)]
  pub fn digest(&self) -> E::Scalar {
    self
      .digest
      .get_or_try_init(|| DigestComputer::new(self).digest())
      .cloned()
      .expect("digest failure")
  }

  pub fn multiply_all_Ms(
    &self,
    z: &[E::Scalar],
  ) -> Result<Vec<Vec<E::Scalar>>, NovaError> {
    if z.len() != self.num_vars + 1 + self.num_io {
      return Err(NovaError::InvalidWitnessLength);
    }

    let Mzs = self.Ms
      .par_iter()
      .map(|M| M.multiply_vec(z))
      .collect::<Vec<_>>();

    Ok(Mzs)
  }

  pub fn is_sat_relaxed(
    &self,
    ck: &CommitmentKey<E>,
    U: &CCSRelaxedInstance<E>,
    W: &CCSRelaxedWitness<E>,
  ) -> Result<(), NovaError> {
    let z = [&U.X[..], &[U.u], &W.W[..]].concat();
    let Mzs = self.multiply_all_Ms(&z)?;

  
    let mut acc = vec![E::Scalar::ZERO; self.num_cons];
    for (c, S) in &self.cSs {
      let mut term = vec![*c; self.num_cons];
      for &idx in S {
        term
          .iter_mut()
          .zip(Mzs[idx].iter())
          .for_each(|(t, v)| *t *= v);
      }
      acc.iter_mut().zip(term).for_each(|(a, t)| *a += t);
    }
  
    // acc == E
    let eq = acc
      .iter()
      .zip(&W.E)
      .all(|(a, b)| *a == *b);
    let com_eq = {
      let (cw, ce) = W.commit(ck);
      cw == U.comm_W && ce == U.comm_E
    };
  
    if !eq {
      return Err(NovaError::UnSat {
        reason: "CCS relaxed equation unsatisfied".to_string(),
      });
    }
  
    if !com_eq {
      return Err(NovaError::UnSat {
        reason: "Invalid commitments".to_string(),
      });
    }
  
    Ok(())
  }
  
  #[allow(unused)]
  pub fn is_sat(
    &self,
    ck: &CommitmentKey<E>,
    U: &CCSInstance<E>,
    W: &CCSWitness<E>,
  ) -> Result<(), NovaError> {
    let z = [&U.X[..], &[E::Scalar::ONE], &W.W[..]].concat();
    let Mzs = self.multiply_all_Ms(&z)?;

    let mut acc = vec![E::Scalar::ZERO; self.num_cons];
    for (c, S) in &self.cSs {
      let mut term = vec![*c; self.num_cons];
      for &idx in S {
        term
          .iter_mut()
          .zip(Mzs[idx].iter())
          .for_each(|(t, v)| *t *= v);
      }
      acc.iter_mut().zip(term).for_each(|(a, t)| *a += t);
    }

    if acc.iter().any(|x| (!x.is_zero()).into()) {
      return Err(NovaError::UnSat {
        reason: "CCS unsatisfied".to_string(),
      });
    }

    let comm = CE::<E>::commit(ck, &W.W, &W.r_W);
    if comm != U.comm_W {
      return Err(NovaError::UnSat {
        reason: "Invalid commitment".to_string(),
      });
    }

    Ok(())
  }

  /// Computes the CCS evaluation and commitment for a cross-term T.
  #[allow(unused)]
  pub fn commit_T(
    &self,
    ck: &CommitmentKey<E>,
    z1: &[E::Scalar],
    z2: &[E::Scalar],
    t_prev: &[E::Scalar],
    r_T: &E::Scalar,
  ) -> Result<(Vec<E::Scalar>, Commitment<E>), NovaError> {
    let z = z1
      .iter()
      .zip(z2.iter())
      .map(|(a, b)| *a + *b)
      .collect::<Vec<_>>();

    let Mzs = self.multiply_all_Ms(&z)?;
    let mut acc = vec![E::Scalar::ZERO; self.num_cons];

    for (c, S) in &self.cSs {
      let mut term = vec![*c; self.num_cons];
      for &i in S {
        term.iter_mut().zip(Mzs[i].iter()).for_each(|(t, v)| *t *= v);
      }
      acc.iter_mut().zip(term).for_each(|(a, t)| *a += t);
    }

    let T: Vec<E::Scalar> = acc
      .into_par_iter()
      .zip(t_prev.par_iter())
      .map(|(acc_i, t_i)| acc_i - *t_i)
      .collect();
  

    let comm_T = CE::<E>::commit(ck, &T, r_T);
    Ok((T, comm_T))
  }

  #[allow(unused)]
  pub fn commit_T_relaxed(
    &self,
    ck: &CommitmentKey<E>,
    U1: &CCSInstance<E>,
    W1: &CCSWitness<E>,
    U2: &CCSInstance<E>,
    W2: &CCSWitness<E>,
    r_T: &E::Scalar,
  ) -> Result<(Vec<E::Scalar>, Commitment<E>), NovaError> {
    // Form Z = W || X
    let Z1 = [&W1.W[..], &U1.X[..]].concat();
    let Z2 = [&W2.W[..], &U2.X[..]].concat();
  
    // Compute Z = Z1 + Z2
    let Z = Z1
      .into_par_iter()
      .zip(Z2.into_par_iter())
      .map(|(z1, z2)| z1 + z2)
      .collect::<Vec<E::Scalar>>();
  
    // Compute Mz for each matrix
    let Mzs: Vec<Vec<E::Scalar>> = self.Ms.iter().map(|M| M.multiply_vec(&Z)).collect();
  
    // Compute CCS constraint polynomial T = Σ c ⋅ Π_i M_i(Z) for each constraint
    let mut acc = vec![E::Scalar::ZERO; self.num_cons];
    for (c, S) in &self.cSs {
      let mut term = vec![*c; self.num_cons];
      for &idx in S {
        term
          .iter_mut()
          .zip(Mzs[idx].iter())
          .for_each(|(t, v)| *t *= v);
      }
      acc.iter_mut().zip(term).for_each(|(a, t)| *a += t);
    }
  
    let T = acc;
    let comm_T = CE::<E>::commit(ck, &T, r_T);
  
    Ok((T, comm_T))
  }

  #[allow(unused)]
  pub fn pad(&self) -> Self {
    let m = max(max(self.num_vars, self.num_cons), self.num_io).next_power_of_two();

    if self.num_vars == m && self.num_cons == m {
      return self.clone();
    }

    let pad_vars = m - self.num_vars;
    let pad_cons = m - self.num_cons;

    let pad_matrix = |mut M: SparseMatrix<E::Scalar>| {
      M.indices.par_iter_mut().for_each(|idx| {
        if *idx >= self.num_vars {
          *idx += pad_vars;
        }
      });

      M.cols += pad_vars;

      let ex = {
        let nnz = *M.indptr.last().unwrap();
        vec![nnz; pad_cons]
      };
      M.indptr.extend(ex);
      M
    };

    let Ms_padded = self.Ms.iter().cloned().map(pad_matrix).collect();

    Self {
      num_cons: m,
      num_vars: m,
      num_io: self.num_io,
      Ms: Ms_padded,
      cSs: self.cSs.clone(),
      digest: OnceCell::new(),
    }
  }

}

impl<E: Engine> CCSWitness<E> {
  #[allow(unused)]
  pub fn new(S: &CCSShape<E>, W: &[E::Scalar]) -> Result<Self, NovaError> {
    let mut w = W.to_vec();
    w.resize(S.num_vars, E::Scalar::ZERO);
    Ok(Self {
      W: w,
      r_W: E::Scalar::random(&mut OsRng),
    })
  }

  #[allow(unused)]
  pub fn commit(&self, ck: &CommitmentKey<E>) -> Commitment<E> {
    CE::<E>::commit(ck, &self.W, &self.r_W)
  }

  /// Pads the witness to the correct length as expected by the CCS shape.
  #[allow(unused)]
  pub fn pad(&self, S: &CCSShape<E>) -> Self {
    let mut W = self.W.clone();
    W.resize(S.num_vars, E::Scalar::ZERO);
    Self {
      W,
      r_W: self.r_W,
    }
  }
}

impl<E: Engine> CCSInstance<E> {
  /// A method to create a CCS instance object using the commitment and public inputs.
  #[allow(unused)]
  pub fn new(
    S: &CCSShape<E>,
    comm_W: &Commitment<E>,
    X: &[E::Scalar],
  ) -> Result<CCSInstance<E>, NovaError> {
    if S.num_io != X.len() {
      Err(NovaError::InvalidInputLength)
    } else {
      Ok(CCSInstance {
        comm_W: *comm_W,
        X: X.to_vec(),
      })
    }
  }
}

impl<E: Engine> AbsorbInROTrait<E> for CCSInstance<E> {
  fn absorb_in_ro(&self, ro: &mut E::RO) {
    self.comm_W.absorb_in_ro(ro);
    for x in &self.X {
      ro.absorb(scalar_as_base::<E>(*x));
    }
  }
}

impl<E: Engine> AbsorbInRO2Trait<E> for CCSInstance<E> {
  fn absorb_in_ro2(&self, ro: &mut E::RO2) {
    self.comm_W.absorb_in_ro2(ro);

    for x in &self.X {
      ro.absorb(*x);
    }
  }
}

impl<E: Engine> CCSRelaxedWitness<E> {
  /// Produces a default `CCSRelaxedWitness` given a `CCSShape`
  #[allow(unused)]
  pub fn default(S: &CCSShape<E>) -> Self {
    Self {
      W: vec![E::Scalar::ZERO; S.num_vars],
      r_W: E::Scalar::ZERO,
      E: vec![E::Scalar::ZERO; S.num_cons],
      r_E: E::Scalar::ZERO,
    }
  }

  /// Initializes a new `CCSRelaxedWitness` from a `CCSWitness`
  #[allow(unused)]
  pub fn from_ccs_witness(S: &CCSShape<E>, witness: &CCSWitness<E>) -> Self {
    Self {
      W: witness.W.clone(),
      r_W: witness.r_W,
      E: vec![E::Scalar::ZERO; S.num_cons],
      r_E: E::Scalar::ZERO,
    }
  }

  /// Commits to the witness using the supplied generators
  pub fn commit(&self, ck: &CommitmentKey<E>) -> (Commitment<E>, Commitment<E>) {
    (
      CE::<E>::commit(ck, &self.W, &self.r_W),
      CE::<E>::commit(ck, &self.E, &self.r_E),
    )
  }

  /// Folds an incoming `CCSWitness` into the current one
  #[allow(unused)]
  pub fn fold(
    &self,
    W2: &CCSWitness<E>,
    T: &[E::Scalar],
    r_T: &E::Scalar,
    r: &E::Scalar,
  ) -> Result<Self, NovaError> {
    if self.W.len() != W2.W.len() {
      return Err(NovaError::InvalidWitnessLength);
    }

    let W = self
      .W
      .par_iter()
      .zip(&W2.W)
      .map(|(a, b)| *a + *r * *b)
      .collect();

    let E = self
      .E
      .par_iter()
      .zip(T)
      .map(|(a, b)| *a + *r * *b)
      .collect();

    let r_W = self.r_W + *r * W2.r_W;
    let r_E = self.r_E + *r * *r_T;

    Ok(Self { W, r_W, E, r_E })
  }

  /// Folds an incoming `CCSRelaxedWitness` into the current one
  #[allow(unused)]
  pub fn fold_relaxed(
    &self,
    W2: &Self,
    T: &[E::Scalar],
    r_T: &E::Scalar,
    r: &E::Scalar,
  ) -> Result<Self, NovaError> {
    if self.W.len() != W2.W.len() {
      return Err(NovaError::InvalidWitnessLength);
    }

    let W = self
      .W
      .par_iter()
      .zip(&W2.W)
      .map(|(a, b)| *a + *r * *b)
      .collect();

    let E = self
      .E
      .par_iter()
      .zip(T)
      .zip(W2.E.par_iter())
      .map(|((a, b), c)| *a + *r * *b + *r * *r * *c)
      .collect();

    let r_W = self.r_W + *r * W2.r_W;
    let r_E = self.r_E + *r * *r_T + *r * *r * W2.r_E;

    Ok(Self { W, r_W, E, r_E })
  }

  /// Pads the provided witness to the correct length
  #[allow(unused)]
  pub fn pad(&self, S: &CCSShape<E>) -> Self {
    let mut W = self.W.clone();
    W.resize(S.num_vars, E::Scalar::ZERO);

    let mut E = self.E.clone();
    E.resize(S.num_cons, E::Scalar::ZERO);

    Self {
      W,
      r_W: self.r_W,
      E,
      r_E: self.r_E,
    }
  }

  /// Removes randomness from the commitments and returns original r values
  #[allow(unused)]
  pub fn derandomize(&self) -> (Self, E::Scalar, E::Scalar) {
    (
      Self {
        W: self.W.clone(),
        r_W: E::Scalar::ZERO,
        E: self.E.clone(),
        r_E: E::Scalar::ZERO,
      },
      self.r_W,
      self.r_E,
    )
  }
}

impl<E: Engine> CCSRelaxedInstance<E> {
  #[allow(unused)]
  pub fn default(_ck: &CommitmentKey<E>, shape: &CCSShape<E>) -> Self {
    let comm_W: Commitment<E> = Default::default();
    let comm_E: Commitment<E> = Default::default();
    Self {
      comm_W,
      comm_E,
      X: vec![E::Scalar::ZERO; shape.num_io],
      u: E::Scalar::ZERO,
    }
  }

  #[allow(unused)]
  pub fn from_instance(
    ck: &CommitmentKey<E>,
    shape: &CCSShape<E>,
    instance: &CCSInstance<E>,
  ) -> Self {
    let mut r_instance = Self::default(ck, shape);
    r_instance.comm_W = instance.comm_W;
    r_instance.u = E::Scalar::ONE;
    r_instance.X.clone_from(&instance.X);
    r_instance
  }

  #[allow(unused)]
  pub fn from_instance_unchecked(
    comm_W: &Commitment<E>,
    X: &[E::Scalar],
  ) -> Self {
    let comm_E: Commitment<E> = Default::default();
    Self {
      comm_W: *comm_W,
      comm_E,
      X: X.to_vec(),
      u: E::Scalar::ONE,
    }
  }

  #[allow(unused)]
  pub fn fold(
    &self,
    U2: &CCSInstance<E>,
    comm_T: &Commitment<E>,
    r: &E::Scalar,
  ) -> Self {
    let X = self
      .X
      .par_iter()
      .zip(&U2.X)
      .map(|(a, b)| *a + *r * *b)
      .collect();
    let comm_W = self.comm_W + U2.comm_W * *r;
    let comm_E = self.comm_E + *comm_T * *r;
    let u = self.u + *r;
    Self {
      comm_W,
      comm_E,
      X,
      u,
    }
  }

  #[allow(unused)]
  pub fn fold_relaxed(
    &self,
    U2: &CCSRelaxedInstance<E>,
    comm_T: &Commitment<E>,
    r: &E::Scalar,
  ) -> Self {
    let X = self
      .X
      .par_iter()
      .zip(&U2.X)
      .map(|(a, b)| *a + *r * *b)
      .collect();
    let comm_W = self.comm_W + U2.comm_W * *r;
    let comm_E = self.comm_E + *comm_T * *r + U2.comm_E * *r * *r;
    let u = self.u + *r * U2.u;
    Self {
      comm_W,
      comm_E,
      X,
      u,
    }
  }

  #[allow(unused)]
  pub fn derandomize(
    &self,
    dk: &DerandKey<E>,
    r_W: &E::Scalar,
    r_E: &E::Scalar,
  ) -> Self {
    Self {
      comm_W: CE::<E>::derandomize(dk, &self.comm_W, r_W),
      comm_E: CE::<E>::derandomize(dk, &self.comm_E, r_E),
      X: self.X.clone(),
      u: self.u,
    }
  }
}

impl<E: Engine> TranscriptReprTrait<E::GE> for CCSRelaxedInstance<E> {
  fn to_transcript_bytes(&self) -> Vec<u8> {
    [
      self.comm_W.to_transcript_bytes(),
      self.comm_E.to_transcript_bytes(),
      self.u.to_transcript_bytes(),
      self.X.as_slice().to_transcript_bytes(),
    ]
    .concat()
  }
}

impl<E: Engine> AbsorbInROTrait<E> for CCSRelaxedInstance<E> {
  fn absorb_in_ro(&self, ro: &mut E::RO) {
    self.comm_W.absorb_in_ro(ro);
    self.comm_E.absorb_in_ro(ro);
    ro.absorb(scalar_as_base::<E>(self.u));

    // absorb each element of self.X in bignum format
    for x in &self.X {
      let limbs: Vec<E::Scalar> = nat_to_limbs(&f_to_nat(x), BN_LIMB_WIDTH, BN_N_LIMBS).unwrap();
      for limb in limbs {
        ro.absorb(scalar_as_base::<E>(limb));
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use ff::Field;

  use super::*;
  use crate::{
    provider::{Bn256EngineKZG, PallasEngine, Secp256k1Engine},
    traits::{Engine},
  };
  use crate::r1cs::sparse::SparseMatrix;

  fn tiny_ccs<E: Engine>(num_vars: usize) -> CCSShape<E> {
    let one = E::Scalar::ONE;
    let num_io = 2;
  
    let M0_entries = vec![
      (0, num_vars + 1, one),
      (1, 0, one),
      (2, 1, one),
      (2, num_vars + 1, one),
      (3, 2, one),
      (3, num_vars, one + one + one + one + one),
    ];
  
    let M1_entries = vec![
      (0, num_vars + 1, one),
      (1, num_vars + 1, one),
      (2, num_vars, one),
      (3, num_vars, one),
    ];
  
    let M2_entries = vec![
      (0, 0, one),
      (1, 1, one),
      (2, 2, one),
      (3, num_vars + 2, one),
    ];
  
    let num_cons = [
      M0_entries.iter().map(|(r, _, _)| *r).max().unwrap(),
      M1_entries.iter().map(|(r, _, _)| *r).max().unwrap(),
      M2_entries.iter().map(|(r, _, _)| *r).max().unwrap(),
    ]
    .iter()
    .max()
    .unwrap()
    + 1;
  
    let num_cols = num_vars + num_io + 1;
  
    // 🧪 ASSERT all column indices are < num_cols
    for (i, entries) in [&M0_entries, &M1_entries, &M2_entries].iter().enumerate() {
      let max_col = entries.iter().map(|(_, c, _)| *c).max().unwrap();
      assert!(
        max_col < num_cols,
        "Matrix M{} has a column index {} >= num_cols {}",
        i,
        max_col,
        num_cols
      );
    }
  
    let M0 = SparseMatrix::new(&M0_entries, num_cons, num_cols);
    let M1 = SparseMatrix::new(&M1_entries, num_cons, num_cols);
    let M2 = SparseMatrix::new(&M2_entries, num_cons, num_cols);
  
    dbg!(M0.cols, M1.cols, M2.cols, num_cols); // 🧾 optional debug output
  
    let Ms = vec![M0, M1, M2];
    let cSs = vec![
      (one, vec![0, 1]),
      (-one, vec![2]),
    ];
  
    CCSShape::new(num_cons, num_vars, num_io, Ms, cSs)
  }
  
  fn test_sample_manual_ccs_with<E: Engine>() {
    let shape = tiny_ccs::<E>(4);
    let ck = shape.commitment_key(&|s: &CCSShape<E>| s.num_cons.max(s.num_vars));

    // Set known-good values
    let X = vec![E::Scalar::ZERO; shape.num_io];
    let u = E::Scalar::ONE;
    let W = vec![E::Scalar::ZERO; shape.num_vars];
    let r_W = E::Scalar::random(&mut OsRng);

    let z = [&X[..], &[u], &W[..]].concat();
    let Mzs = shape.multiply_all_Ms(&z).unwrap();

    // Solve acc = Σ c_i * ∏_{j ∈ S_i} M_j(z)
    let mut acc = vec![E::Scalar::ZERO; shape.num_cons];
    for (c, S) in &shape.cSs {
        let mut term = vec![*c; shape.num_cons];
        for &idx in S {
            term
                .iter_mut()
                .zip(Mzs[idx].iter())
                .for_each(|(t, v)| *t *= v);
        }
        acc.iter_mut().zip(term).for_each(|(a, t)| *a += t);
    }

    // Set E = acc, and create RelaxedWitness
    let E_vec = acc;
    let r_E = E::Scalar::random(&mut OsRng);
    let comm_W = CE::<E>::commit(&ck, &W, &r_W);
    let comm_E = CE::<E>::commit(&ck, &E_vec, &r_E);

    let relaxed_inst = CCSRelaxedInstance {
        comm_W,
        comm_E,
        X: X.clone(),
        u,
    };

    let relaxed_wit = CCSRelaxedWitness {
        W,
        r_W,
        E: E_vec,
        r_E,
    };

    assert!(
        shape.is_sat_relaxed(&ck, &relaxed_inst, &relaxed_wit).is_ok(),
        "Manual relaxed CCS instance should be satisfiable"
    );
  }

  fn cubic_ccs<E: Engine>() -> CCSShape<E> {
    let one = E::Scalar::ONE;
    let num_vars = 1;
    let num_io = 1;
    let num_cols = num_vars + num_io + 1; // [x, u, w]

    // M0(z) = x, M1(z) = w
    let M0_entries = vec![(0, 0, one)];     // selects x
    let M1_entries = vec![(0, 2, one)];     // selects w

    let M0 = SparseMatrix::new(&M0_entries, 1, num_cols);
    let M1 = SparseMatrix::new(&M1_entries, 1, num_cols);

    // Constraint: x * w * w - 1 = 0
    let Ms = vec![M0, M1];
    let cSs = vec![
        (one, vec![0, 1, 1]),  // M0 * M1 * M1
        (-one, vec![]),        // -1 (via u = 1, absorbed in constant)
    ];

    CCSShape::new(1, num_vars, num_io, Ms, cSs)
  }

  fn test_cubic_manual_ccs_with<E: Engine>() {
    let shape = cubic_ccs::<E>();
    let ck = shape.commitment_key(&|s| {
      s.Ms.len().max(s.num_cons).max(s.num_vars).max(s.num_io + s.num_vars + 1)
    });

    // Choose values so x * w^2 = 1, e.g. x = 1, w = 1
    let X = vec![E::Scalar::ONE]; // x = 1
    let u = E::Scalar::ONE;
    let W = vec![E::Scalar::ONE]; // w = 1
    let r_W = E::Scalar::random(&mut OsRng);

    let z = [&X[..], &[u], &W[..]].concat();
    let Mzs = shape.multiply_all_Ms(&z).unwrap();

    let mut acc = vec![E::Scalar::ZERO; shape.num_cons];
    for (c, S) in &shape.cSs {
        let mut term = vec![*c; shape.num_cons];
        for &idx in S {
            term
                .iter_mut()
                .zip(Mzs[idx].iter())
                .for_each(|(t, v)| *t *= v);
        }
        acc.iter_mut().zip(term).for_each(|(a, t)| *a += t);
    }

    let E_vec = acc;
    let r_E = E::Scalar::random(&mut OsRng);
    let comm_W = CE::<E>::commit(&ck, &W, &r_W);
    let comm_E = CE::<E>::commit(&ck, &E_vec, &r_E);

    let relaxed_inst = CCSRelaxedInstance {
        comm_W,
        comm_E,
        X: X.clone(),
        u,
    };

    let relaxed_wit = CCSRelaxedWitness {
        W,
        r_W,
        E: E_vec,
        r_E,
    };

    assert!(
        shape.is_sat_relaxed(&ck, &relaxed_inst, &relaxed_wit).is_ok(),
        "Cubic CCS instance should be satisfiable"
    );
  }

  #[test]
  fn test_sample_random_ccs() {
    test_sample_manual_ccs_with::<PallasEngine>();
    test_sample_manual_ccs_with::<Bn256EngineKZG>();
    test_sample_manual_ccs_with::<Secp256k1Engine>();
  }

  #[test]
  fn test_cubic_ccs() {
      test_cubic_manual_ccs_with::<PallasEngine>();
      test_cubic_manual_ccs_with::<Bn256EngineKZG>();
      test_cubic_manual_ccs_with::<Secp256k1Engine>();
  }
}

