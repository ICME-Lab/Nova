//! Support for efficiently generating R1CS witness using bellperson.

use ff::PrimeField;

use crate::frontend::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};

/// A [`ConstraintSystem`] trait
pub trait SizedWitness<Scalar: PrimeField, const NumSplits: usize> {
  /// Returns the number of constraints in the constraint system
  fn num_constraints(&self) -> usize;
  /// Returns the number of inputs in the constraint system
  fn num_inputs(&self) -> usize;
  /// Returns the number of auxiliary variables in the constraint system
  fn num_aux(&self) -> usize;

  /// Generate a witness for the constraint system
  fn generate_witness_into(&mut self, aux: &mut [Scalar], inputs: &mut [Scalar]) -> Scalar;

  /// Generate a witness for the constraint system
  fn generate_witness_into_cs<CS: ConstraintSystem<Scalar, NumSplits>>(&mut self, cs: &mut CS) -> Scalar {
    assert!(cs.is_witness_generator());

    let aux_count = self.num_aux();
    let inputs_count = self.num_inputs();

    let (aux, inputs) = cs.allocate_empty(aux_count, inputs_count);

    assert_eq!(aux.len(), aux_count);
    assert_eq!(inputs.len(), inputs_count);

    self.generate_witness_into(aux, inputs)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A `ConstraintSystem` which calculates witness values for a concrete instance of an R1CS circuit.
pub struct WitnessCS<Scalar, const NumSplits: usize>
where
  Scalar: PrimeField,
{
  // Assignments of variables
  pub(crate) input_assignment: Vec<Scalar>,
  pub(crate) aux_assignment: Vec<Scalar>,
  pub(crate) precommitted_assignment: [Vec<Scalar>; NumSplits],
}

impl<Scalar, const NumSplits: usize> WitnessCS<Scalar, NumSplits>
where
  Scalar: PrimeField,
{
  /// Get input assignment
  pub fn input_assignment(&self) -> &[Scalar] {
    &self.input_assignment
  }

  /// Get aux assignment
  pub fn aux_assignment(&self) -> &[Scalar] {
    &self.aux_assignment
  }

  /// Get precommitted assignment
  pub fn precommitted_assignment(&self) -> &[Vec<Scalar>; NumSplits] {
    &self.precommitted_assignment
  }
}

impl<Scalar, const NumSplits: usize> ConstraintSystem<Scalar, NumSplits> for WitnessCS<Scalar, NumSplits>
where
  Scalar: PrimeField,
{
  type Root = Self;

  fn new() -> Self {
    let input_assignment = vec![Scalar::ONE];

    Self {
      input_assignment,
      aux_assignment: vec![],
      precommitted_assignment: {
        let mut precommitted = Vec::with_capacity(NumSplits);
        precommitted.resize_with(NumSplits, Vec::new);
        precommitted.try_into().unwrap()
      },
    }
  }

  fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
  where
    F: FnOnce() -> Result<Scalar, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    self.aux_assignment.push(f()?);

    Ok(Variable(Index::Aux(self.aux_assignment.len() - 1)))
  }

  fn alloc_input<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
  where
    F: FnOnce() -> Result<Scalar, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    self.input_assignment.push(f()?);

    Ok(Variable(Index::Input(self.input_assignment.len() - 1)))
  }

  fn alloc_precommitted<F, A, AR>(&mut self, _: A, f: F, idx: usize) -> Result<Variable, SynthesisError>
  where
    F: FnOnce() -> Result<Scalar, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    assert!(idx < NumSplits, "Index out of bounds for precommitted_assignment");

    let precommitted_assignment = &mut self.precommitted_assignment[idx];
    precommitted_assignment.push(f()?);

    Ok(Variable(Index::Precommitted((idx, precommitted_assignment.len() - 1))))
  }

  fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, _a: LA, _b: LB, _c: LC)
  where
    A: FnOnce() -> AR,
    AR: Into<String>,
    LA: FnOnce(LinearCombination<Scalar, NumSplits>) -> LinearCombination<Scalar, NumSplits>,
    LB: FnOnce(LinearCombination<Scalar, NumSplits>) -> LinearCombination<Scalar, NumSplits>,
    LC: FnOnce(LinearCombination<Scalar, NumSplits>) -> LinearCombination<Scalar, NumSplits>,
  {
    // Do nothing: we don't care about linear-combination evaluations in this context.
  }

  fn push_namespace<NR, N>(&mut self, _: N)
  where
    NR: Into<String>,
    N: FnOnce() -> NR,
  {
    // Do nothing; we don't care about namespaces in this context.
  }

  fn pop_namespace(&mut self) {
    // Do nothing; we don't care about namespaces in this context.
  }

  fn get_root(&mut self) -> &mut Self::Root {
    self
  }

  ////////////////////////////////////////////////////////////////////////////////
  // Extensible
  fn is_extensible() -> bool {
    true
  }

  fn extend(&mut self, other: &Self) {
    self.input_assignment
            // Skip first input, which must have been a temporarily allocated one variable.
            .extend(&other.input_assignment[1..]);
    self.aux_assignment.extend(&other.aux_assignment);
  }

  ////////////////////////////////////////////////////////////////////////////////
  // Witness generator
  fn is_witness_generator(&self) -> bool {
    true
  }

  fn extend_inputs(&mut self, new_inputs: &[Scalar]) {
    self.input_assignment.extend(new_inputs);
  }

  fn extend_aux(&mut self, new_aux: &[Scalar]) {
    self.aux_assignment.extend(new_aux);
  }

  fn allocate_empty(&mut self, aux_n: usize, inputs_n: usize) -> (&mut [Scalar], &mut [Scalar]) {
    let allocated_aux = {
      let i = self.aux_assignment.len();
      self.aux_assignment.resize(aux_n + i, Scalar::ZERO);
      &mut self.aux_assignment[i..]
    };

    let allocated_inputs = {
      let i = self.input_assignment.len();
      self.input_assignment.resize(inputs_n + i, Scalar::ZERO);
      &mut self.input_assignment[i..]
    };

    (allocated_aux, allocated_inputs)
  }

  fn inputs_slice(&self) -> &[Scalar] {
    &self.input_assignment
  }

  fn aux_slice(&self) -> &[Scalar] {
    &self.aux_assignment
  }
}
