//! This module provides interfaces to directly prove a step circuit by using Spartan SNARK.
//! In particular, it supports any SNARK that implements `RelaxedR1CSSNARK` trait
//! (e.g., with the SNARKs implemented in ppsnark.rs or snark.rs).
use crate::{
  errors::NovaError,
  frontend::{
    num::AllocatedNum,
    r1cs::{NovaShape, NovaWitness},
    shape_cs::ShapeCS,
    solver::SatisfyingAssignment,
    Circuit, ConstraintSystem, SynthesisError,
  },
  r1cs::{R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness},
  traits::{
    circuit::StepCircuit,
    commitment::CommitmentEngineTrait,
    snark::{DigestHelperTrait, RelaxedR1CSSNARKTrait},
    Engine,
  },
  Commitment, CommitmentKey, DerandKey,
};
use core::marker::PhantomData;
use ff::Field;
use serde::{Deserialize, Serialize};

use super::delegatedsnark::Delegatable;

/// A direct circuit that can be synthesized
pub struct DirectCircuit<E: Engine, SC: StepCircuit<E::Scalar>> {
  z_i: Option<Vec<E::Scalar>>, // inputs to the circuit
  sc: SC,                      // step circuit to be executed
}

impl<E: Engine, SC: StepCircuit<E::Scalar>> DirectCircuit<E, SC> {
  /// Create a new direct circuit from a step circuit and optional inputs
  pub fn new(z_i: Option<Vec<E::Scalar>>, sc: SC) -> Self {
    Self { z_i, sc }
  }
}

impl<E: Engine, SC: StepCircuit<E::Scalar>> Circuit<E::Scalar> for DirectCircuit<E, SC> {
  fn synthesize<CS: ConstraintSystem<E::Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
    // obtain the arity information
    let arity = self.sc.arity();

    // Allocate zi. If inputs.zi is not provided, allocate default value 0
    let zero = vec![E::Scalar::ZERO; arity];
    let z_i = (0..arity)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("zi_{i}")), || {
          Ok(self.z_i.as_ref().unwrap_or(&zero)[i])
        })
      })
      .collect::<Result<Vec<AllocatedNum<E::Scalar>>, _>>()?;

    let z_i_plus_one = self.sc.synthesize(&mut cs.namespace(|| "F"), &z_i)?;

    // inputize both z_i and z_i_plus_one
    for (j, input) in z_i.iter().enumerate().take(arity) {
      let _ = input.inputize(cs.namespace(|| format!("input {j}")));
    }
    for (j, output) in z_i_plus_one.iter().enumerate().take(arity) {
      let _ = output.inputize(cs.namespace(|| format!("output {j}")));
    }

    Ok(())
  }
}

/// A type that holds the prover key
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProverKey<E, S>
where
  E: Engine,
  S: RelaxedR1CSSNARKTrait<E>,
{
  S: R1CSShape<E>,
  ck: CommitmentKey<E>,
  pk: S::ProverKey,
}

/// A type that holds the verifier key
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct VerifierKey<E, S>
where
  E: Engine,
  S: RelaxedR1CSSNARKTrait<E>,
{
  dk: DerandKey<E>,
  vk: S::VerifierKey,
}

impl<E: Engine, S: RelaxedR1CSSNARKTrait<E>> VerifierKey<E, S> {
  /// Returns the digest of the verifier's key
  pub fn digest(&self) -> E::Scalar {
    self.vk.digest()
  }
}

/// A direct SNARK proving a step circuit
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct DirectSNARK<E, S, C>
where
  E: Engine,
  S: RelaxedR1CSSNARKTrait<E>,
  C: StepCircuit<E::Scalar>,
{
  comm_W: Commitment<E>, // commitment to the witness
  blind_r_W: E::Scalar,
  snark: S, // snark proving the witness is satisfying
  _p: PhantomData<C>,
}

impl<E: Engine, S: RelaxedR1CSSNARKTrait<E>, C: StepCircuit<E::Scalar>> DirectSNARK<E, S, C> {
  /// Produces prover and verifier keys for the direct SNARK
  pub fn setup(sc: C) -> Result<(ProverKey<E, S>, VerifierKey<E, S>), NovaError> {
    // construct a circuit that can be synthesized
    let circuit: DirectCircuit<E, C> = DirectCircuit { z_i: None, sc };

    let mut cs: ShapeCS<E> = ShapeCS::new();
    let _ = circuit.synthesize(&mut cs);

    let (shape, ck) = cs.r1cs_shape(&*S::ck_floor());

    let (pk, vk) = S::setup(&ck, &shape)?;

    let dk = E::CE::derand_key(&ck);

    let pk = ProverKey { S: shape, ck, pk };

    let vk = VerifierKey { dk, vk };

    Ok((pk, vk))
  }

  /// Produces a proof of satisfiability of the provided circuit
  pub fn prove(pk: &ProverKey<E, S>, sc: C, z_i: &[E::Scalar]) -> Result<Self, NovaError> {
    let mut cs = SatisfyingAssignment::<E>::new();

    let circuit: DirectCircuit<E, C> = DirectCircuit {
      z_i: Some(z_i.to_vec()),
      sc,
    };

    let _ = circuit.synthesize(&mut cs);
    let (u, w) = cs
      .r1cs_instance_and_witness(&pk.S, &pk.ck)
      .map_err(|_e| NovaError::UnSat {
        reason: "Unable to generate a satisfying witness".to_string(),
      })?;

    // convert the instance and witness to relaxed form
    let (u_relaxed, w_relaxed) = (
      RelaxedR1CSInstance::from_r1cs_instance_unchecked(&u.comm_W, &u.X),
      RelaxedR1CSWitness::from_r1cs_witness(&pk.S, &w),
    );

    // derandomize/unblind commitments
    let (derandom_w_relaxed, blind_W, blind_E) = w_relaxed.derandomize();
    let derandom_u_relaxed = u_relaxed.derandomize(&E::CE::derand_key(&pk.ck), &blind_W, &blind_E);

    // prove the instance using Spartan
    let snark = S::prove(
      &pk.ck,
      &pk.pk,
      &pk.S,
      &derandom_u_relaxed,
      &derandom_w_relaxed,
    )?;

    Ok(DirectSNARK {
      comm_W: u.comm_W,
      blind_r_W: w_relaxed.r_W,
      snark,
      _p: PhantomData,
    })
  }

  /// Verifies a proof of satisfiability
  pub fn verify(&self, vk: &VerifierKey<E, S>, io: &[E::Scalar]) -> Result<(), NovaError> {
    // derandomize/unblind commitments
    let comm_W = E::CE::derandomize(&vk.dk, &self.comm_W, &self.blind_r_W);

    // construct an instance using the provided commitment to the witness and z_i and z_{i+1}
    let u_relaxed = RelaxedR1CSInstance::from_r1cs_instance_unchecked(&comm_W, io);

    // verify the snark using the constructed instance
    self.snark.verify(&vk.vk, &u_relaxed)?;

    Ok(())
  }
}

impl<E: Engine, S: Delegatable<E>, C: StepCircuit<E::Scalar>> DirectSNARK<E, S, C> {
  /// Prepare instance and witness
  fn setup_u_w(
    pk: &ProverKey<E, S>,
    sc: C,
    z_i: &[E::Scalar],
  ) -> Result<
    (
      Commitment<E>,
      E::Scalar,
      RelaxedR1CSInstance<E>,
      RelaxedR1CSWitness<E>,
    ),
    NovaError,
  > {
    let mut cs = SatisfyingAssignment::<E>::new();

    let circuit: DirectCircuit<E, C> = DirectCircuit {
      z_i: Some(z_i.to_vec()),
      sc,
    };

    let _ = circuit.synthesize(&mut cs);
    let (u, w) = cs
      .r1cs_instance_and_witness(&pk.S, &pk.ck)
      .map_err(|_e| NovaError::UnSat {
        reason: "Unable to generate a satisfying witness".to_string(),
      })?;

    // convert the instance and witness to relaxed form
    let (u_relaxed, w_relaxed) = (
      RelaxedR1CSInstance::from_r1cs_instance_unchecked(&u.comm_W, &u.X),
      RelaxedR1CSWitness::from_r1cs_witness(&pk.S, &w),
    );

    let (derandom_w_relaxed, blind_W, blind_E) = w_relaxed.derandomize();
    let derandom_u_relaxed = u_relaxed.derandomize(&E::CE::derand_key(&pk.ck), &blind_W, &blind_E);

    Ok((
      u.comm_W,
      w_relaxed.r_W,
      derandom_u_relaxed,
      derandom_w_relaxed,
    ))
  }

  /// Builds witness-related part of proof
  fn prover_step(
    pk: &ProverKey<E, S>,
    u: &RelaxedR1CSInstance<E>,
    w: &RelaxedR1CSWitness<E>,
  ) -> Result<(S::ProverProofPart, (Vec<E::Scalar>, Vec<E::Scalar>)), NovaError> {
    // prove the instance using Spartan
    let (prover_part, r) = S::prover_step(&pk.ck, &pk.pk, &pk.S, u, w)?;

    Ok((prover_part, r))
  }

  /// Builds non-witness-related part of proof
  fn delegated_step(
    pk: &ProverKey<E, S>,
    r: (&[E::Scalar], &[E::Scalar]),
  ) -> Result<S::DelegatedProofPart, NovaError> {
    // prove the instance using Spartan
    let delegated_part = S::delegated_step(&pk.ck, &pk.pk, &pk.S, r)?;

    Ok(delegated_part)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    frontend::{
      num::AllocatedNum, AllocatedBit, ConstraintSystem, LinearCombination, SynthesisError,
    },
    provider::Bn256EngineKZG,
    spartan::spark::SparkEngine,
    traits::Group,
  };
  use core::marker::PhantomData;
  use ff::{PrimeField, PrimeFieldBits};
  use rand::Rng;
  use std::time::Instant;

  #[derive(Clone, Debug)]
  struct AndInstance<G: Group> {
    a: u64,
    b: u64,
    _p: PhantomData<G>,
  }

  impl<G: Group> AndInstance<G> {
    // produces an AND instance
    fn new() -> Self {
      let mut rng = rand::thread_rng();
      let a: u64 = rng.gen();
      let b: u64 = rng.gen();
      Self {
        a,
        b,
        _p: PhantomData,
      }
    }
  }

  #[derive(Clone, Debug)]
  struct AndCircuit<E: Engine> {
    batch: Vec<AndInstance<E::GE>>,
  }

  impl<E: Engine> AndCircuit<E> {
    // produces a batch of AND instances
    fn new(num_ops_per_step: usize) -> Self {
      let mut batch = Vec::new();
      for _ in 0..num_ops_per_step {
        batch.push(AndInstance::new());
      }
      Self { batch }
    }
  }

  pub fn u64_into_bit_vec_le<Scalar: PrimeField, CS: ConstraintSystem<Scalar>>(
    mut cs: CS,
    value: Option<u64>,
  ) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let values = match value {
      Some(ref value) => {
        let mut tmp = Vec::with_capacity(64);

        for i in 0..64 {
          tmp.push(Some((*value >> i) & 1 == 1));
        }

        tmp
      }
      None => vec![None; 64],
    };

    let bits = values
      .into_iter()
      .enumerate()
      .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("bit {}", i)), b))
      .collect::<Result<Vec<_>, SynthesisError>>()?;

    Ok(bits)
  }

  /// Gets as input the little indian representation of a number and spits out the number
  pub fn le_bits_to_num<Scalar, CS>(
    mut cs: CS,
    bits: &[AllocatedBit],
  ) -> Result<AllocatedNum<Scalar>, SynthesisError>
  where
    Scalar: PrimeField + PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
  {
    // We loop over the input bits and construct the constraint
    // and the field element that corresponds to the result
    let mut lc = LinearCombination::zero();
    let mut coeff = Scalar::ONE;
    let mut fe = Some(Scalar::ZERO);
    for bit in bits.iter() {
      lc = lc + (coeff, bit.get_variable());
      fe = bit.get_value().map(|val| {
        if val {
          fe.unwrap() + coeff
        } else {
          fe.unwrap()
        }
      });
      coeff = coeff.double();
    }
    let num = AllocatedNum::alloc(cs.namespace(|| "Field element"), || {
      fe.ok_or(SynthesisError::AssignmentMissing)
    })?;
    lc = lc - num.get_variable();
    cs.enforce(|| "compute number from bits", |lc| lc, |lc| lc, |_| lc);
    Ok(num)
  }

  impl<E: Engine> StepCircuit<E::Scalar> for AndCircuit<E> {
    fn arity(&self) -> usize {
      1
    }

    fn synthesize<CS: ConstraintSystem<E::Scalar>>(
      &self,
      cs: &mut CS,
      z_in: &[AllocatedNum<E::Scalar>],
    ) -> Result<Vec<AllocatedNum<E::Scalar>>, SynthesisError> {
      for i in 0..self.batch.len() {
        // allocate a and b as field elements
        let a = AllocatedNum::alloc(cs.namespace(|| format!("a_{}", i)), || {
          Ok(E::Scalar::from(self.batch[i].a))
        })?;
        let b = AllocatedNum::alloc(cs.namespace(|| format!("b_{}", i)), || {
          Ok(E::Scalar::from(self.batch[i].b))
        })?;

        // obtain bit representations of a and b
        let a_bits = u64_into_bit_vec_le(
          cs.namespace(|| format!("a_bits_{}", i)),
          Some(self.batch[i].a),
        )?; // little endian
        let b_bits = u64_into_bit_vec_le(
          cs.namespace(|| format!("b_bits_{}", i)),
          Some(self.batch[i].b),
        )?; // little endian

        // enforce that bits of a and b are correct
        let a_from_bits = le_bits_to_num(cs.namespace(|| format!("a_{}", i)), &a_bits)?;
        let b_from_bits = le_bits_to_num(cs.namespace(|| format!("b_{}", i)), &b_bits)?;

        cs.enforce(
          || format!("a_{} == a_from_bits", i),
          |lc| lc + a.get_variable(),
          |lc| lc + CS::one(),
          |lc| lc + a_from_bits.get_variable(),
        );
        cs.enforce(
          || format!("b_{} == b_from_bits", i),
          |lc| lc + b.get_variable(),
          |lc| lc + CS::one(),
          |lc| lc + b_from_bits.get_variable(),
        );

        let mut c_bits = Vec::new();

        // perform bitwise AND
        for i in 0..64 {
          let c_bit = AllocatedBit::and(
            cs.namespace(|| format!("and_bit_{}", i)),
            &a_bits[i],
            &b_bits[i],
          )?;
          c_bits.push(c_bit);
        }

        // convert back to an allocated num
        let c_from_bits = le_bits_to_num(cs.namespace(|| format!("c_{}", i)), &c_bits)?;

        let c = AllocatedNum::alloc(cs.namespace(|| format!("c_{}", i)), || {
          Ok(E::Scalar::from(self.batch[i].a & self.batch[i].b))
        })?;

        // enforce that c is correct
        cs.enforce(
          || format!("c_{} == c_from_bits", i),
          |lc| lc + c.get_variable(),
          |lc| lc + CS::one(),
          |lc| lc + c_from_bits.get_variable(),
        );
      }

      Ok(z_in.to_vec())
    }
  }

  impl<E: Engine> AndCircuit<E> {
    fn output(&self, z: &[E::Scalar]) -> Vec<E::Scalar> {
      vec![z[0]]
    }
  }

  #[test]
  fn test_direct_snark_deleg() {
    let num_steps = 16;

    type E2 = Bn256EngineKZG;
    type EE2 = crate::provider::hyperkzg::EvaluationEngine<E2>;
    type CC2 = SparkEngine<E2, EE2>;

    type S2 = crate::spartan::snark::RelaxedR1CSSNARK<E2, EE2>;
    test_direct_snark_with::<E2, S2>("snark", num_steps);

    type S2pp = crate::spartan::ppsnark::RelaxedR1CSSNARK<E2, EE2>;
    test_direct_snark_with::<E2, S2pp>("ppsnark", num_steps);

    type S2deleg = crate::spartan::delegatedsnark::RelaxedR1CSSNARK<E2, EE2, CC2>;
    test_direct_deleg_snark_with::<E2, S2deleg>("delegatedsnark", num_steps);
  }

  fn test_direct_snark_with<E: Engine, S: RelaxedR1CSSNARKTrait<E>>(
    proof_type: &str,
    num_steps: usize,
  ) {
    let circuit = AndCircuit::new(num_steps);

    // produce keys
    let (pk, vk) = DirectSNARK::<E, S, AndCircuit<E>>::setup(circuit.clone()).unwrap();

    // setup inputs
    let z0 = vec![<E as Engine>::Scalar::ZERO];
    let mut z_i = z0;

    // produce a SNARK
    let start = Instant::now();
    let res = DirectSNARK::prove(&pk, circuit.clone(), &z_i);
    assert!(res.is_ok());
    println!(
      "Time elapsed for proving with {} is: {:?}",
      proof_type,
      start.elapsed()
    );

    let z_i_plus_one = circuit.output(&z_i);

    let snark = res.unwrap();

    let mut encoder = flate2::write::ZlibEncoder::new(Vec::new(), flate2::Compression::default());
    bincode::serialize_into(&mut encoder, &snark).unwrap();
    let compressed_snark_encoded = encoder.finish().unwrap();
    println!(
      "Compressed snark len {:?} bytes\n",
      compressed_snark_encoded.len()
    );

    // verify the SNARK
    let io = z_i
      .clone()
      .into_iter()
      .chain(z_i_plus_one.clone())
      .collect::<Vec<_>>();
    let res = snark.verify(&vk, &io);
    assert!(res.is_ok());

    // set input to the next step
    z_i.clone_from(&z_i_plus_one);

    // sanity: check the claimed output with a direct computation of the same
    // assert_eq!(z_i, vec![<E as Engine>::Scalar::from(2460515u64)]);
  }

  fn test_direct_deleg_snark_with<E: Engine, S: Delegatable<E>>(
    proof_type: &str,
    num_steps: usize,
  ) {
    let circuit = AndCircuit::new(num_steps);

    // produce keys
    let (pk, vk) = DirectSNARK::<E, S, AndCircuit<E>>::setup(circuit.clone()).unwrap();

    // setup inputs
    let z0 = vec![<E as Engine>::Scalar::ZERO];
    let mut z_i = z0;

    let total = Instant::now();
    // produce a SNARK
    let (comm_W, r_W, u, w) =
      DirectSNARK::<E, S, AndCircuit<E>>::setup_u_w(&pk, circuit.clone(), &z_i).unwrap();

    let start = Instant::now();
    let (prover_step, r) = DirectSNARK::<E, S, AndCircuit<E>>::prover_step(&pk, &u, &w).unwrap();
    println!(
      "Time elapsed for witness-related part of proving with {} is: {:?}",
      proof_type,
      start.elapsed()
    );

    let mut encoder = flate2::write::ZlibEncoder::new(Vec::new(), flate2::Compression::default());
    bincode::serialize_into(&mut encoder, &prover_step).unwrap();
    let compressed_prover_step_encoded = encoder.finish().unwrap();
    println!(
      "Compressed prover step len {:?} bytes",
      compressed_prover_step_encoded.len()
    );

    let r = (r.0.as_slice(), r.1.as_slice());
    let start = Instant::now();
    let delegated_step = DirectSNARK::<E, S, AndCircuit<E>>::delegated_step(&pk, r).unwrap();
    println!(
      "Time elapsed for delegated part of proving with {} is: {:?}",
      proof_type,
      start.elapsed()
    );

    let mut encoder = flate2::write::ZlibEncoder::new(Vec::new(), flate2::Compression::default());
    bincode::serialize_into(&mut encoder, &delegated_step).unwrap();
    let compressed_delegated_step_encoded = encoder.finish().unwrap();
    println!(
      "Compressed delegated step len {:?} bytes",
      compressed_delegated_step_encoded.len()
    );

    println!(
      "Total time elapsed for proving with {} is: {:?}\n",
      proof_type,
      total.elapsed()
    );

    let z_i_plus_one = circuit.output(&z_i);

    let snark = DirectSNARK::<E, S, AndCircuit<E>> {
      comm_W,
      blind_r_W: r_W,
      snark: S::combine_proofs(prover_step, delegated_step),
      _p: PhantomData,
    };

    // verify the SNARK
    let io = z_i
      .clone()
      .into_iter()
      .chain(z_i_plus_one.clone())
      .collect::<Vec<_>>();
    let res = snark.verify(&vk, &io);
    assert!(res.is_ok());

    // set input to the next step
    z_i.clone_from(&z_i_plus_one);

    // sanity: check the claimed output with a direct computation of the same
    // assert_eq!(z_i, vec![<E as Engine>::Scalar::from(2460515u64)]);
  }
}
