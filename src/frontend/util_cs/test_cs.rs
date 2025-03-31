//! Test constraint system for use in tests.

use std::collections::HashMap;

use crate::frontend::{ConstraintSystem, Index, LinearCombination, SynthesisError, Variable};

use ff::PrimeField;

#[derive(Debug)]
enum NamedObject {
  Constraint,
  Var(Variable),
  Namespace,
}

/// Constraint system for testing purposes.
#[derive(Debug)]
pub struct TestConstraintSystem<Scalar: PrimeField> {
  named_objects: HashMap<String, NamedObject>,
  current_namespace: Vec<String>,
  #[allow(clippy::type_complexity)]
  constraints: Vec<(
    LinearCombination<Scalar>,
    LinearCombination<Scalar>,
    LinearCombination<Scalar>,
    String,
  )>,
  inputs: Vec<(Scalar, String)>,
  aux: Vec<(Scalar, String)>,
}

fn _eval_lc2<Scalar: PrimeField>(
  terms: &LinearCombination<Scalar>,
  inputs: &[Scalar],
  aux: &[Scalar],
) -> Scalar {
  let mut acc = Scalar::ZERO;

  for (var, coeff) in terms.iter() {
    let mut tmp = match var.get_unchecked() {
      Index::Input(index) => inputs[index],
      Index::Aux(index) => aux[index],
    };

    tmp.mul_assign(coeff);
    acc.add_assign(&tmp);
  }

  acc
}

fn eval_lc<Scalar: PrimeField>(
  terms: &LinearCombination<Scalar>,
  inputs: &[(Scalar, String)],
  aux: &[(Scalar, String)],
) -> Scalar {
  let mut acc = Scalar::ZERO;

  for (var, coeff) in terms.iter() {
    let mut tmp = match var.get_unchecked() {
      Index::Input(index) => inputs[index].0,
      Index::Aux(index) => aux[index].0,
    };

    tmp.mul_assign(coeff);
    acc.add_assign(&tmp);
  }

  acc
}

impl<Scalar: PrimeField> Default for TestConstraintSystem<Scalar> {
  fn default() -> Self {
    let mut map = HashMap::new();
    map.insert(
      "ONE".into(),
      NamedObject::Var(TestConstraintSystem::<Scalar>::one()),
    );

    TestConstraintSystem {
      named_objects: map,
      current_namespace: vec![],
      constraints: vec![],
      inputs: vec![(Scalar::ONE, "ONE".into())],
      aux: vec![],
    }
  }
}

impl<Scalar: PrimeField> TestConstraintSystem<Scalar> {
  /// Create a new test constraint system.
  pub fn new() -> Self {
    Default::default()
  }

  /// Get the number of constraints
  pub fn num_constraints(&self) -> usize {
    self.constraints.len()
  }

  /// Get path which is unsatisfied
  pub fn which_is_unsatisfied(&self) -> Option<&str> {
    for (a, b, c, path) in &self.constraints {
      let mut a = eval_lc::<Scalar>(a, &self.inputs, &self.aux);
      let b = eval_lc::<Scalar>(b, &self.inputs, &self.aux);
      let c = eval_lc::<Scalar>(c, &self.inputs, &self.aux);

      a.mul_assign(&b);

      if a != c {
        return Some(path);
      }
    }

    None
  }

  /// Check if the constraint system is satisfied.
  pub fn is_satisfied(&self) -> bool {
    match self.which_is_unsatisfied() {
      Some(b) => {
        println!("fail: {:?}", b);
        false
      }
      None => true,
    }
  }

  fn set_named_obj(&mut self, path: String, to: NamedObject) {
    assert!(
      !self.named_objects.contains_key(&path),
      "tried to create object at existing path: {}",
      path
    );

    self.named_objects.insert(path, to);
  }

  /// Set a variable at a given path to a value.
  pub fn set(&mut self, path: &str, to: Scalar) {
    match self.named_objects.get(path) {
      Some(NamedObject::Var(v)) => match v.get_unchecked() {
        Index::Input(index) => self.inputs[index].0 = to,
        Index::Aux(index) => self.aux[index].0 = to,
      },
      Some(e) => panic!(
        "tried to set path `{}` to value, but `{:?}` already exists there.",
        path, e
      ),
      _ => panic!("no variable exists at path: {}", path),
    }
  }

  /// Get the value of a variable at a given path.
  pub fn get(&mut self, path: &str) -> Scalar {
    match self.named_objects.get(path) {
      Some(NamedObject::Var(v)) => match v.get_unchecked() {
        Index::Input(index) => self.inputs[index].0,
        Index::Aux(index) => self.aux[index].0,
      },
      Some(e) => panic!(
        "tried to get value of path `{}`, but `{:?}` exists there (not a variable)",
        path, e
      ),
      _ => panic!("no variable exists at path: {}", path),
    }
  }
}

fn compute_path(ns: &[String], this: &str) -> String {
  assert!(
    !this.chars().any(|a| a == '/'),
    "'/' is not allowed in names"
  );

  if ns.is_empty() {
    return this.to_string();
  }

  let name = ns.join("/");
  format!("{}/{}", name, this)
}

impl<Scalar: PrimeField> ConstraintSystem<Scalar> for TestConstraintSystem<Scalar> {
  type Root = Self;

  fn alloc<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
  where
    F: FnOnce() -> Result<Scalar, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    let index = self.aux.len();
    let path = compute_path(&self.current_namespace, &annotation().into());
    self.aux.push((f()?, path.clone()));
    let var = Variable::new_unchecked(Index::Aux(index));
    self.set_named_obj(path, NamedObject::Var(var));

    Ok(var)
  }

  fn alloc_input<F, A, AR>(&mut self, annotation: A, f: F) -> Result<Variable, SynthesisError>
  where
    F: FnOnce() -> Result<Scalar, SynthesisError>,
    A: FnOnce() -> AR,
    AR: Into<String>,
  {
    let index = self.inputs.len();
    let path = compute_path(&self.current_namespace, &annotation().into());
    self.inputs.push((f()?, path.clone()));
    let var = Variable::new_unchecked(Index::Input(index));
    self.set_named_obj(path, NamedObject::Var(var));

    Ok(var)
  }

  fn enforce<A, AR, LA, LB, LC>(&mut self, annotation: A, a: LA, b: LB, c: LC)
  where
    A: FnOnce() -> AR,
    AR: Into<String>,
    LA: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
    LB: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
    LC: FnOnce(LinearCombination<Scalar>) -> LinearCombination<Scalar>,
  {
    let path = compute_path(&self.current_namespace, &annotation().into());
    self.set_named_obj(path.clone(), NamedObject::Constraint);

    let a = a(LinearCombination::zero());
    let b = b(LinearCombination::zero());
    let c = c(LinearCombination::zero());

    self.constraints.push((a, b, c, path));
  }

  fn push_namespace<NR, N>(&mut self, name_fn: N)
  where
    NR: Into<String>,
    N: FnOnce() -> NR,
  {
    let name = name_fn().into();
    let path = compute_path(&self.current_namespace, &name);
    self.set_named_obj(path, NamedObject::Namespace);
    self.current_namespace.push(name);
  }

  fn pop_namespace(&mut self) {
    assert!(self.current_namespace.pop().is_some());
  }

  fn get_root(&mut self) -> &mut Self::Root {
    self
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{provider::Bn256EngineIPA, traits::Engine};
  use ff::Field;

  type Fr = <Bn256EngineIPA as Engine>::Scalar;

  #[test]
  fn test_compute_path() {
    assert_eq!(
      compute_path(
        &[
          "hello".to_string(),
          "world".to_string(),
          "things".to_string()
        ],
        "thing"
      ),
      "hello/world/things/thing"
    );
  }

  #[test]
  fn test_cs() {
    let mut cs = TestConstraintSystem::<Fr>::new();
    assert!(cs.is_satisfied());
    assert_eq!(cs.num_constraints(), 0);
    let a = cs
      .namespace(|| "a")
      .alloc(|| "var", || Ok(Fr::from(10u64)))
      .unwrap();
    let b = cs
      .namespace(|| "b")
      .alloc(|| "var", || Ok(Fr::from(4u64)))
      .unwrap();
    let c = cs.alloc(|| "product", || Ok(Fr::from(40u64))).unwrap();

    cs.enforce(|| "mult", |lc| lc + a, |lc| lc + b, |lc| lc + c);
    assert!(cs.is_satisfied());
    assert_eq!(cs.num_constraints(), 1);

    cs.set("a/var", Fr::from(4u64));

    let one = TestConstraintSystem::<Fr>::one();
    cs.enforce(|| "eq", |lc| lc + a, |lc| lc + one, |lc| lc + b);

    assert!(!cs.is_satisfied());
    assert!(cs.which_is_unsatisfied() == Some("mult"));

    assert!(cs.get("product") == Fr::from(40u64));

    cs.set("product", Fr::from(16u64));
    assert!(cs.is_satisfied());

    {
      let mut cs = cs.namespace(|| "test1");
      let mut cs = cs.namespace(|| "test2");
      cs.alloc(|| "hehe", || Ok(Fr::ONE)).unwrap();
    }

    assert!(cs.get("test1/test2/hehe") == Fr::ONE);
  }
}
