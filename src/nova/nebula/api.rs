//! This module defines the Nebula API. A CC-IVC scheme that proves the correct execution of a program
//! and that the program maintained memory correctly.

use super::product_circuits::{
  convert_advice_separate, BatchedOpsCircuit, OpsCircuit, ScanCircuit,
};
use crate::{
  errors::NovaError,
  nova::{
    ic::increment_ic, CompressedSNARK, IncrementalCommitment, ProverKey, PublicParams,
    RecursiveSNARK, VerifierKey,
  },
  traits::{
    circuit::StepCircuit,
    snark::{default_ck_hint, RelaxedR1CSSNARKTrait},
    Engine, TranscriptEngineTrait,
  },
};
use ff::Field;
use itertools::Itertools;
use once_cell::sync::OnceCell;
use serde::{Deserialize, Serialize};

/// Public parameters for the Nebula SNARK
///
/// /// The constant `M` is the number of memory operations per step in the vm.
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct NebulaPublicParams<E1, E2, S1, S2, const M: usize>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  F: PublicParams<E1, E2>,
  ops: PublicParams<E1, E2>,
  scan: PublicParams<E1, E2>,
  #[serde(skip, default = "OnceCell::new")]
  pk_and_vk: OnceCell<(
    NebulaProverKey<E1, E2, S1, S2>,
    NebulaVerifierKey<E1, E2, S1, S2>,
  )>,
}

impl<E1, E2, S1, S2, const M: usize> NebulaPublicParams<E1, E2, S1, S2, M>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  fn F(&self) -> &PublicParams<E1, E2> {
    &self.F
  }

  fn ops(&self) -> &PublicParams<E1, E2> {
    &self.ops
  }

  fn scan(&self) -> &PublicParams<E1, E2> {
    &self.scan
  }

  /// provides a reference to a ProverKey suitable for producing a CompressedProof
  pub fn pk(&self) -> &NebulaProverKey<E1, E2, S1, S2> {
    let (pk, _vk) = self
      .pk_and_vk
      .get_or_init(|| NebulaCompressedSNARK::<E1, E2, S1, S2>::setup(self).unwrap());
    pk
  }

  /// provides a reference to a VerifierKey suitable for verifying a CompressedProof
  pub fn vk(&self) -> &NebulaVerifierKey<E1, E2, S1, S2> {
    let (_pk, vk) = self
      .pk_and_vk
      .get_or_init(|| NebulaCompressedSNARK::<E1, E2, S1, S2>::setup(self).unwrap());
    vk
  }
}

/// Nebula Prover key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct NebulaProverKey<E1, E2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  F: ProverKey<E1, E2, S1, S2>,
  ops: ProverKey<E1, E2, S1, S2>,
  scan: ProverKey<E1, E2, S1, S2>,
}

/// Nebula Verifier key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct NebulaVerifierKey<E1, E2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  F: VerifierKey<E1, E2, S1, S2>,
  ops: VerifierKey<E1, E2, S1, S2>,
  scan: VerifierKey<E1, E2, S1, S2>,
}

/// Apply Spartan to prove knowledge of a valid Nebula IVC proof
#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(bound = "")]
pub struct NebulaCompressedSNARK<E1, E2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  F: CompressedSNARK<E1, E2, S1, S2>,
  ops: CompressedSNARK<E1, E2, S1, S2>,
  scan: CompressedSNARK<E1, E2, S1, S2>,
}

impl<E1, E2, S1, S2> NebulaCompressedSNARK<E1, E2, S1, S2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  /// Setup the Prover and Verifier keys for the Nebula SNARK
  pub fn setup<const M: usize>(
    pp: &NebulaPublicParams<E1, E2, S1, S2, M>,
  ) -> Result<
    (
      NebulaProverKey<E1, E2, S1, S2>,
      NebulaVerifierKey<E1, E2, S1, S2>,
    ),
    NovaError,
  > {
    let (F_pk, F_vk) = CompressedSNARK::<E1, E2, S1, S2>::setup(pp.F())?;
    let (ops_pk, ops_vk) = CompressedSNARK::<E1, E2, S1, S2>::setup(pp.ops())?;
    let (scan_pk, scan_vk) = CompressedSNARK::<E1, E2, S1, S2>::setup(pp.scan())?;
    Ok((
      NebulaProverKey {
        F: F_pk,
        ops: ops_pk,
        scan: scan_pk,
      },
      NebulaVerifierKey {
        F: F_vk,
        ops: ops_vk,
        scan: scan_vk,
      },
    ))
  }

  /// produce a compressed proof for the Nebula SNARK
  pub fn prove<const M: usize>(
    pp: &NebulaPublicParams<E1, E2, S1, S2, M>,
    pk: &NebulaProverKey<E1, E2, S1, S2>,
    rs: &NebulaRecursiveSNARK<E1, E2>,
    U: &NebulaInstance<E1>,
  ) -> Result<NebulaCompressedSNARK<E1, E2, S1, S2>, NovaError> {
    let F = CompressedSNARK::prove(pp.F(), &pk.F, &rs.F, U.F_ic)?;
    let ops = CompressedSNARK::prove(pp.ops(), &pk.ops, &rs.ops, U.ops_ic)?;
    let scan = CompressedSNARK::prove(pp.scan(), &pk.scan, &rs.scan, U.scan_ic)?;
    Ok(NebulaCompressedSNARK { F, ops, scan })
  }

  /// verify a compressed proof for the Nebula SNARK
  pub fn verify(
    &self,
    vk: &NebulaVerifierKey<E1, E2, S1, S2>,
    U: &NebulaInstance<E1>,
  ) -> Result<(Vec<E1::Scalar>, Vec<E1::Scalar>), NovaError> {
    self.F.verify(&vk.F, U.F_num_steps, &U.F_z_0)?;
    let ops_z_i = self.ops.verify(&vk.ops, U.ops_num_steps, &U.ops_z_0)?;
    let scan_z_i = self.scan.verify(&vk.scan, U.scan_num_steps, &U.scan_z_0)?;
    Ok((ops_z_i, scan_z_i))
  }
}

/// A SNARK that proves correct execution of a vm and that the vm maintained
/// memory correctly.
///
/// The constant `M` is the number of memory operations per step in the vm.
#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(bound = "")]
pub enum NebulaSNARK<E1, E2, S1, S2, const M: usize>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
{
  /// RecursiveSNARK for vm execution
  Recursive(Box<NebulaRecursiveSNARK<E1, E2>>),
  /// CompressedSNARK for vm execution
  Compressed(Box<NebulaCompressedSNARK<E1, E2, S1, S2>>),
}

/// A SNARK that proves correct execution of a vm and that the vm maintained
/// memory correctly.
///
/// The constant `M` is the number of memory operations per step in the vm.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct NebulaRecursiveSNARK<E1, E2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  F: RecursiveSNARK<E1, E2>,
  ops: RecursiveSNARK<E1, E2>,
  scan: RecursiveSNARK<E1, E2>,
}

impl<E1, E2, S1, S2, const M: usize> NebulaSNARK<E1, E2, S1, S2, M>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  S1: RelaxedR1CSSNARKTrait<E1>,
  S2: RelaxedR1CSSNARKTrait<E2>,
  <E1 as Engine>::Scalar: PartialOrd,
{
  /// Fn used to obtain setup material for producing succinct arguments for
  /// WASM program executions
  pub fn setup(
    F: &impl StepCircuit<E1::Scalar>,
    step_size: StepSize,
  ) -> Result<NebulaPublicParams<E1, E2, S1, S2, M>, NovaError> {
    let F_pp = PublicParams::setup(F, &*default_ck_hint::<E1>(), &*default_ck_hint::<E2>())?;
    let ops_pp = PublicParams::setup(
      &BatchedOpsCircuit::empty::<M>(step_size.execution),
      &*default_ck_hint::<E1>(),
      &*default_ck_hint::<E2>(),
    )?;
    let scan_pp = PublicParams::setup(
      &ScanCircuit::empty(step_size.memory),
      &*default_ck_hint::<E1>(),
      &*default_ck_hint::<E2>(),
    )?;

    Ok(NebulaPublicParams {
      F: F_pp,
      ops: ops_pp,
      scan: scan_pp,
      pk_and_vk: OnceCell::new(),
    })
  }

  /// Produce a SNARK that proves correct execution of a vm and that the vm maintained
  /// memory correctly.
  pub fn prove(
    pp: &NebulaPublicParams<E1, E2, S1, S2, M>,
    step_size: StepSize,
    vm_multi_sets: VMMultiSets,
    F_engine: impl RecursiveSNARKEngine<E1, E2>,
  ) -> Result<(Self, NebulaInstance<E1>), NovaError> {
    let (init_memory, final_memory, read_ops, write_ops) = vm_multi_sets;

    // --- Run the F (transition) circuit ---
    //
    // We use commitment-carrying IVC to prove the repeated execution of F
    tracing::debug!("Execution proving");
    let (F_rs, F_ic, F_z_0) = RecursiveSNARKEngine::run(|| F_engine, pp.F())?;

    // --- Get challenges gamma and alpha ---
    //
    // * Compute commitment to IS & FS -> IC_Audit
    // * hash ic_ops & ic_scan and get gamma, alpha
    let (gamma, alpha) = Self::gamma_alpha(
      pp.scan(),
      &init_memory,
      &final_memory,
      F_ic.0,
      step_size.memory,
    )?;

    // Grand product checks for RS & WS
    tracing::debug!("MCC: Incrementally computing grand products for RS & WS");
    let (ops_rs, ops_ic, ops_z_0) = RecursiveSNARKEngine::run(
      || OpsGrandProductEngine::<E1, M>::new(read_ops, write_ops, gamma, alpha, step_size),
      pp.ops(),
    )?;

    // Grand product checks for IS & FS
    tracing::debug!("MCC: Incrementally computing grand products for IS & FS");
    let (scan_rs, scan_ic, scan_z_0) = RecursiveSNARKEngine::run(
      || ScanGrandProductEngine::new(init_memory, final_memory, gamma, alpha, step_size),
      pp.scan(),
    )?;
    let U = NebulaInstance {
      F_z_0,
      F_ic,
      F_num_steps: F_rs.num_steps(),
      ops_z_0,
      ops_ic,
      ops_num_steps: ops_rs.num_steps(),
      scan_z_0,
      scan_ic,
      scan_num_steps: scan_rs.num_steps(),
    };
    Ok((
      Self::Recursive(Box::new(NebulaRecursiveSNARK {
        F: F_rs,
        ops: ops_rs,
        scan: scan_rs,
      })),
      U,
    ))
  }

  /// Apply Spartan on top of the Nebula IVC proofs
  pub fn compress(
    &self,
    pp: &NebulaPublicParams<E1, E2, S1, S2, M>,
    U: &NebulaInstance<E1>,
  ) -> Result<Self, NovaError> {
    match self {
      Self::Recursive(rs) => Ok(Self::Compressed(Box::new(NebulaCompressedSNARK::prove(
        pp,
        pp.pk(),
        rs.as_ref(),
        U,
      )?))),
      Self::Compressed(..) => Err(NovaError::NotRecursive),
    }
  }

  /// Verify the [`NebulaSNARK`]
  pub fn verify(
    &self,
    pp: &NebulaPublicParams<E1, E2, S1, S2, M>,
    U: &NebulaInstance<E1>,
  ) -> Result<(), NovaError> {
    let (ops_z_i, scan_z_i) = match self {
      Self::Recursive(rs) => {
        // verify F
        rs.F.verify(pp.F(), rs.F.num_steps(), &U.F_z_0, U.F_ic)?;

        // verify F_ops
        let ops_z_i = rs
          .ops
          .verify(pp.ops(), rs.ops.num_steps(), &U.ops_z_0, U.ops_ic)?;

        // verify F_scan
        let scan_z_i = rs
          .scan
          .verify(pp.scan(), rs.scan.num_steps(), &U.scan_z_0, U.scan_ic)?;

        (ops_z_i, scan_z_i)
      }
      Self::Compressed(spartan) => spartan.verify(pp.vk(), U)?,
    };
    // 1. check h_IS = h_RS = h_WS = h_FS = 1 // initial values are correct
    let (init_h_is, init_h_rs, init_h_ws, init_h_fs) =
      { (U.scan_z_0[2], U.ops_z_0[3], U.ops_z_0[4], U.scan_z_0[3]) };
    if init_h_is != E1::Scalar::ONE
      || init_h_rs != E1::Scalar::ONE
      || init_h_ws != E1::Scalar::ONE
      || init_h_fs != E1::Scalar::ONE
    {
      return Err(NovaError::InvalidMultisetProof {
        reason: "initial values are incorrect".to_string(),
      });
    }

    // --- 2. check Cn' = Cn  ---
    //
    // commitments carried in both Πops and ΠF are the same
    if U.F_ic != U.ops_ic {
      return Err(NovaError::InvalidMultisetProof {
        reason: "Cn' != Cn".to_string(),
      });
    }

    // --- 3. check γ and γ are derived by hashing C and C′′. ---
    //
    // Get alpha and gamma
    let mut keccak = E1::TE::new(b"compute MCC challenges");
    keccak.absorb(b"ic_ops", &U.F_ic.0);
    keccak.absorb(b"ic_is", &U.scan_ic.0);
    keccak.absorb(b"ic_fs", &U.scan_ic.1);
    let gamma = keccak.squeeze(b"gamma")?;
    let alpha = keccak.squeeze(b"alpha")?;

    if U.ops_z_0[0] != gamma || U.ops_z_0[1] != alpha {
      return Err(NovaError::InvalidMultisetProof {
        reason: "gamma and alpha do not match".to_string(),
      });
    }

    // --- 4. check h_IS' · h_WS' = h_RS' · h_FS'.---
    //
    // Inputs for multiset check
    let (h_is, h_rs, h_ws, h_fs) = { (scan_z_i[2], ops_z_i[3], ops_z_i[4], scan_z_i[3]) };
    if h_is * h_ws != h_rs * h_fs {
      return Err(NovaError::InvalidMultisetProof {
        reason: "h_IS' · h_WS' != h_RS' · h_FS'".to_string(),
      });
    }

    Ok(())
  }

  // Get MCC challenges for grand products
  fn gamma_alpha(
    pp: &PublicParams<E1, E2>,
    init_memory: &[(usize, u64, u64)],
    final_memory: &[(usize, u64, u64)],
    ic_F: E1::Scalar,
    memory_size: usize,
  ) -> Result<(E1::Scalar, E1::Scalar), NovaError> {
    let mut ic_scan = IncrementalCommitment::<E1>::default();
    for (init_memory_chunk, final_memory_chunk) in init_memory
      .chunks(memory_size)
      .zip_eq(final_memory.chunks(memory_size))
    {
      ic_scan = increment_ic::<E1, E2>(
        &pp.ck_primary,
        &pp.ro_consts_primary,
        ic_scan,
        (
          &convert_advice_separate(init_memory_chunk),
          &convert_advice_separate(final_memory_chunk),
        ),
      );
    }
    let mut keccak = E1::TE::new(b"compute MCC challenges");
    keccak.absorb(b"ic_ops", &ic_F);
    keccak.absorb(b"ic_is", &ic_scan.0);
    keccak.absorb(b"ic_fs", &ic_scan.1);
    let gamma = keccak.squeeze(b"gamma")?;
    let alpha = keccak.squeeze(b"alpha")?;
    Ok((gamma, alpha))
  }
}

/// A trait that encapsulates the common steps for a recursive SNARK prover:
/// 1. Building its circuits,
/// 2. Providing its initial input, and
/// 3. Running the recursive proving loop.
pub trait RecursiveSNARKEngine<E1, E2>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  Self: Sized,
{
  /// Type of circuit to prove
  type Circuit: StepCircuit<E1::Scalar>;

  /// Build the circuits that will be used by the recursive SNARK.
  /// (A mutable reference is required if the implementation consumes internal
  /// data.)
  fn circuits(&mut self) -> Result<Vec<Self::Circuit>, NovaError>;

  /// Return the initial input vector for the recursive SNARK.
  fn z0(&self) -> Vec<E1::Scalar>;

  /// Run the recursive proving loop over the built circuits.
  fn prove_recursive(
    &mut self,
    pp: &PublicParams<E1, E2>,
  ) -> Result<
    (
      RecursiveSNARK<E1, E2>,
      IncrementalCommitment<E1>,
      Vec<E1::Scalar>,
    ),
    NovaError,
  > {
    let circuits = self.circuits()?;
    let z_0 = self.z0();
    let first = circuits.first().ok_or(NovaError::NoCircuit)?;
    let mut rs = RecursiveSNARK::new(pp, first, &z_0)?;
    let mut ic = IncrementalCommitment::<E1>::default();
    for (i, circuit) in circuits.iter().enumerate() {
      tracing::debug!("Proving step {}/{}", i + 1, circuits.len());
      rs.prove_step(pp, circuit, ic)?;
      let (advice_0, advice_1) = circuit.advice();
      ic = increment_ic::<E1, E2>(
        &pp.ck_primary,
        &pp.ro_consts_primary,
        ic,
        (&advice_0, &advice_1),
      );
    }
    Ok((rs, ic, z_0))
  }

  /// Run the engine
  #[tracing::instrument(skip_all, name = "RecursiveSNARKEngine::run")]
  fn run(
    constructor: impl FnOnce() -> Self,
    pp: &PublicParams<E1, E2>,
  ) -> Result<
    (
      RecursiveSNARK<E1, E2>,
      IncrementalCommitment<E1>,
      Vec<E1::Scalar>,
    ),
    NovaError,
  > {
    let mut engine = constructor();
    engine.prove_recursive(pp)
  }
}

struct OpsGrandProductEngine<E, const M: usize>
where
  E: Engine,
{
  RS: Vec<Vec<(usize, u64, u64)>>,
  WS: Vec<Vec<(usize, u64, u64)>>,
  gamma: E::Scalar,
  alpha: E::Scalar,
  step_size: StepSize,
}

impl<E, const M: usize> OpsGrandProductEngine<E, M>
where
  E: Engine,
{
  fn new(
    RS: Vec<Vec<(usize, u64, u64)>>,
    WS: Vec<Vec<(usize, u64, u64)>>,
    gamma: E::Scalar,
    alpha: E::Scalar,
    step_size: StepSize,
  ) -> Self {
    Self {
      RS,
      WS,
      gamma,
      alpha,
      step_size,
    }
  }
}

impl<E1, E2, const M: usize> RecursiveSNARKEngine<E1, E2> for OpsGrandProductEngine<E1, M>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
  <E1 as Engine>::Scalar: PartialOrd,
{
  type Circuit = BatchedOpsCircuit;

  fn circuits(&mut self) -> Result<Vec<Self::Circuit>, NovaError> {
    // Build OpsCircuit from the stored RS and WS multisets.
    let circuits = self
      .RS
      .iter()
      .zip_eq(self.WS.iter())
      .map(|(rs, ws)| OpsCircuit::new(rs.clone(), ws.clone()))
      .collect_vec();
    Ok(
      circuits
        .chunks(self.step_size.execution)
        .map(|chunk| BatchedOpsCircuit::new(chunk.to_vec()))
        .collect::<Vec<_>>(),
    )
  }

  fn z0(&self) -> Vec<E1::Scalar> {
    // The ops RS initial input is [gamma, alpha, ts=0, h_RS=1, h_WS=1, ms_size]
    vec![
      self.gamma,
      self.alpha,
      E1::Scalar::ZERO,
      E1::Scalar::ONE,
      E1::Scalar::ONE,
      E1::Scalar::from(M as u64),
    ]
  }
}

struct ScanGrandProductEngine<E1>
where
  E1: Engine,
{
  IS: Vec<(usize, u64, u64)>,
  FS: Vec<(usize, u64, u64)>,
  gamma: E1::Scalar,
  alpha: E1::Scalar,
  step_size: StepSize,
}

impl<E1> ScanGrandProductEngine<E1>
where
  E1: Engine,
{
  fn new(
    IS: Vec<(usize, u64, u64)>,
    FS: Vec<(usize, u64, u64)>,
    gamma: E1::Scalar,
    alpha: E1::Scalar,
    step_size: StepSize,
  ) -> Self {
    Self {
      IS,
      FS,
      gamma,
      alpha,
      step_size,
    }
  }
}

impl<E1, E2> RecursiveSNARKEngine<E1, E2> for ScanGrandProductEngine<E1>
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  type Circuit = ScanCircuit;

  fn circuits(&mut self) -> Result<Vec<Self::Circuit>, NovaError> {
    // Build ScanCircuit from the stored IS and FS multisets.
    let circuits = self
      .IS
      .chunks(self.step_size.memory)
      .zip_eq(self.FS.chunks(self.step_size.memory))
      .map(|(is_chunk, fs_chunk)| ScanCircuit::new(is_chunk.to_vec(), fs_chunk.to_vec()))
      .collect();
    Ok(circuits)
  }

  fn z0(&self) -> Vec<E1::Scalar> {
    // scan_z0 = [gamma, alpha, h_IS=1, h_FS=1, ms_size]
    vec![
      self.gamma,
      self.alpha,
      E1::Scalar::ONE,
      E1::Scalar::ONE,
      E1::Scalar::from(self.step_size.memory as u64),
    ]
  }
}

/// Public i/o for a Nebula zkVM
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NebulaInstance<E1>
where
  E1: Engine,
{
  F_z_0: Vec<E1::Scalar>,
  F_ic: IncrementalCommitment<E1>,
  F_num_steps: usize,
  ops_z_0: Vec<E1::Scalar>,
  ops_ic: IncrementalCommitment<E1>,
  ops_num_steps: usize,
  scan_z_0: Vec<E1::Scalar>,
  scan_ic: IncrementalCommitment<E1>,
  scan_num_steps: usize,
}

// IS, FS, RS, WS
type VMMultiSets = (
  Vec<(usize, u64, u64)>,
  Vec<(usize, u64, u64)>,
  Vec<Vec<(usize, u64, u64)>>,
  Vec<Vec<(usize, u64, u64)>>,
);

/// Step size of used for zkVM execution
#[derive(Clone, Debug, Copy, Serialize, Deserialize)]
pub struct StepSize {
  /// How many opcodes to execute per recursive step
  pub execution: usize,
  /// How many memory addresses to audit per recursive step
  pub memory: usize,
}

impl StepSize {
  /// Create a new instance of [`StepSize`]
  ///
  /// Sets both execution and memory step size to `step_size`
  pub fn new(step_size: usize) -> Self {
    Self {
      execution: step_size,
      memory: step_size,
    }
  }

  /// Set the memory step size
  ///
  /// Returns a modified instance of [`StepSize`]
  pub fn set_memory_step_size(mut self, memory: usize) -> Self {
    self.memory = memory;
    self
  }
}
