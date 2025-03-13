//! Incremental commitment scheme.
use crate::constants::NUM_HASH_BITS;
use crate::gadgets::utils::scalar_as_base;
use crate::traits::{AbsorbInROTrait, ROTrait};

use super::IncrementalCommitment;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::CommitmentKey;
use crate::{
  traits::{Engine, ROConstants},
  Commitment,
};
use ff::Field;

/// Produces two incremental commitments to non-deterministic advice ω
///
/// * commits to advice with Pedersen
/// * hashes previous commitment & pedersen commitment to advice
/// * outputs hash bits as scalar
pub fn increment_ic<E1, E2>(
  ck: &CommitmentKey<E1>,
  ro_consts: &ROConstants<E1>,
  prev_ic: IncrementalCommitment<E1>,
  advice: (&[E1::Scalar], &[E1::Scalar]),
) -> (E1::Scalar, E1::Scalar)
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  // TODO: add blind.
  //       We have not added blinding yet because for sharding we need the incremental comms to be deterministic
  let comm_advice_0 = E1::CE::commit(ck, advice.0, &E1::Scalar::ZERO);
  let comm_advice_1 = E1::CE::commit_at(ck, advice.1, &E1::Scalar::ZERO, advice.0.len());
  increment_comm::<E1, E2>(ro_consts, prev_ic, (comm_advice_0, comm_advice_1))
}

/// Produce two incremental commitment to already pedersen committed non-deterministic advice ω
pub(crate) fn increment_comm<E1, E2>(
  ro_consts: &ROConstants<E1>,
  prev_ic: IncrementalCommitment<E1>,
  comm_advice: (Commitment<E1>, Commitment<E1>),
) -> (E1::Scalar, E1::Scalar)
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  (
    increment_sole_comm::<E1, E2>(ro_consts, prev_ic.0, comm_advice.0),
    increment_sole_comm::<E1, E2>(ro_consts, prev_ic.1, comm_advice.1),
  )
}

/// Produce an incremental commitment to already pedersen committed non-deterministic advice ω
pub(crate) fn increment_sole_comm<E1, E2>(
  ro_consts: &ROConstants<E1>,
  prev_ic: E1::Scalar,
  comm_advice: Commitment<E1>, // commitment to non-deterministic witness ω
) -> E1::Scalar
where
  E1: Engine<Base = <E2 as Engine>::Scalar>,
  E2: Engine<Base = <E1 as Engine>::Scalar>,
{
  let mut ro = E1::RO::new(ro_consts.clone());
  ro.absorb(scalar_as_base::<E1>(prev_ic));
  comm_advice.absorb_in_ro(&mut ro);
  scalar_as_base::<E2>(ro.squeeze(NUM_HASH_BITS))
}
