//! General-degree CCS frontend using bellpepper-style APIs

#![allow(non_snake_case)]

use super::{shape_cs::ShapeCS, solver::SatisfyingAssignment, test_shape_cs::TestShapeCS};
use crate::{
  ccs::{CCSInstance, CCSShape, CCSWitness},
  errors::NovaError,
  frontend::{Index, LinearCombination},
  traits::Engine,
  CommitmentKey,
};
use ff::PrimeField;
use crate::r1cs::sparse::SparseMatrix;
use ff::Field;

/// Trait for types that expose CCS constraints in general degree form
pub trait CCSConstraintIterable<S: PrimeField> {
  /// Return a vector of multilinear constraints: (scalar, vec of LCs)
  fn general_constraints_iter(&self) -> Vec<(S, Vec<LinearCombination<S>>)>;
}

impl<E: Engine> CCSConstraintIterable<E::Scalar> for ShapeCS<E> {
  fn general_constraints_iter(&self) -> Vec<(E::Scalar, Vec<LinearCombination<E::Scalar>>)> {
    self.constraints.iter().map(|(a, b, c)| {
      vec![
        (E::Scalar::ONE, vec![a.clone(), b.clone()]),
        (-E::Scalar::ONE, vec![c.clone()]),
      ]
    }).flatten().collect()
  }
}

impl<E: Engine> CCSConstraintIterable<E::Scalar> for TestShapeCS<E> {
  fn general_constraints_iter(&self) -> Vec<(E::Scalar, Vec<LinearCombination<E::Scalar>>)> {
    self.constraints.iter().map(|(a, b, c, _)| {
      vec![
        (E::Scalar::ONE, vec![a.clone(), b.clone()]),
        (-E::Scalar::ONE, vec![c.clone()]),
      ]
    }).flatten().collect()
  }
}

/// `NovaCCSWitness` provides a method for acquiring a `CCSInstance` and `CCSWitness` from implementers.
pub trait NovaCCSWitness<E: Engine> {
  /// instance <> witness
  fn ccs_instance_and_witness(
    &self,
    shape: &CCSShape<E>,
    ck: &CommitmentKey<E>,
  ) -> Result<(CCSInstance<E>, CCSWitness<E>), NovaError>;
}

/// `NovaCCSShape` provides methods for acquiring `CCSShape` and `CommitmentKey` from implementers.
pub trait NovaCCSShape<E: Engine> {
  /// fn for ccs shape
  fn ccs_shape<F>(&self, ck_hint: F) -> (CCSShape<E>, CommitmentKey<E>)
  where
    F: Fn(&CCSShape<E>) -> usize + 'static;
}

impl<E: Engine> NovaCCSWitness<E> for SatisfyingAssignment<E> {
  fn ccs_instance_and_witness(
    &self,
    shape: &CCSShape<E>,
    ck: &CommitmentKey<E>,
  ) -> Result<(CCSInstance<E>, CCSWitness<E>), NovaError> {
    let W = CCSWitness::<E>::new(shape, self.aux_assignment())?;
    let X = &self.input_assignment()[1..];
    let comm_W = W.commit(ck);
    let instance = CCSInstance::<E>::new(shape, &comm_W, X)?;
    Ok((instance, W))
  }
}

macro_rules! impl_nova_ccs_shape {
  ( $name:ident ) => {
    impl<E: Engine> NovaCCSShape<E> for $name<E>
    where
      E::Scalar: PrimeField,
      $name<E>: CCSConstraintIterable<E::Scalar>,
    {
      fn ccs_shape<F>(&self, ck_hint: F) -> (CCSShape<E>, CommitmentKey<E>)
      where
        F: Fn(&CCSShape<E>) -> usize + 'static,
      {
        let num_inputs = self.num_inputs();
        let num_vars = self.num_aux();
        let num_io = num_inputs - 1;

        let mut matrices: Vec<SparseMatrix<E::Scalar>> = Vec::new();
        let mut cSs: Vec<(E::Scalar, Vec<usize>)> = Vec::new();

        for (scalar, lcs) in self.general_constraints_iter() {
          let mut mat_idxs = vec![];
          for lc in lcs {
            let m = sparse_matrix_from_lc(0, &lc, num_vars);
            let idx = matrices.len();
            matrices.push(m);
            mat_idxs.push(idx);
          }
          cSs.push((scalar, mat_idxs));
        }

        let num_constraints = matrices.len();
        let shape = CCSShape::new(num_constraints, num_vars, num_io, matrices, cSs);
        let ck = shape.commitment_key(&ck_hint);
        (shape, ck)
      }
    }
  };
}

impl_nova_ccs_shape!(ShapeCS);
impl_nova_ccs_shape!(TestShapeCS);

/// Converts a linear combination into a sparse matrix with a single row.
pub fn sparse_matrix_from_lc<S: PrimeField>(
  row_idx: usize,
  lc: &LinearCombination<S>,
  num_vars: usize,
) -> SparseMatrix<S> {
  let mut matrix_entries = vec![];
  for (index, coeff) in lc.iter() {
    if *coeff != S::ZERO {
      let col = match index.0 {
        Index::Input(i) => num_vars + i,
        Index::Aux(i) => i,
      };
      matrix_entries.push((row_idx, col, *coeff));
    }
  }
  SparseMatrix::new(&matrix_entries, row_idx + 1, num_vars + num_vars + 1)
}
