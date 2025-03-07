//! This module implements various gadgets necessary for folding R1CS types.
use crate::{
  constants::NUM_CHALLENGE_BITS,
  frontend::{num::AllocatedNum, Assignment, Boolean, ConstraintSystem, SynthesisError},
  gadgets::{
    ecc::AllocatedPoint,
    nonnative::{
      bignat::BigNat,
      util::{f_to_nat, Num},
    },
    utils::{
      alloc_bignat_constant, alloc_one, alloc_scalar_as_base, conditionally_select,
      conditionally_select_bignat, le_bits_to_num,
    },
  },
  r1cs::{
    split::{SplitR1CSInstance, SplitRelaxedR1CSInstance},
    R1CSInstance, RelaxedR1CSInstance,
  },
  traits::{commitment::CommitmentTrait, Engine, Group, ROCircuitTrait, ROConstantsCircuit},
};
use ff::Field;

/// An Allocated R1CS Instance
#[derive(Clone)]
pub struct AllocatedR1CSInstance<E: Engine> {
  pub(crate) W: AllocatedPoint<E>,
  pub(crate) X0: AllocatedNum<E::Base>,
  pub(crate) X1: AllocatedNum<E::Base>,
  pub(crate) precommit0: AllocatedPoint<E>,
  pub(crate) precommit1: AllocatedPoint<E>,
}

impl<E: Engine> AllocatedR1CSInstance<E> {
  /// Takes the r1cs instance and creates a new allocated r1cs instance
  pub fn alloc<CS: ConstraintSystem<<E as Engine>::Base>>(
    mut cs: CS,
    u: Option<&SplitR1CSInstance<E>>,
  ) -> Result<Self, SynthesisError> {
    let W = AllocatedPoint::alloc(
      cs.namespace(|| "allocate W"),
      u.map(|u| u.aux.comm_W.to_coordinates()),
    )?;
    W.check_on_curve(cs.namespace(|| "check W on curve"))?;

    let X0 = alloc_scalar_as_base::<E, _>(cs.namespace(|| "allocate X[0]"), u.map(|u| u.aux.X[0]))?;
    let X1 = alloc_scalar_as_base::<E, _>(cs.namespace(|| "allocate X[1]"), u.map(|u| u.aux.X[1]))?;

    let precommit0 = AllocatedPoint::alloc(
      cs.namespace(|| "allocate pre_commit_0"),
      u.map(|u| u.precommitted.0.to_coordinates()),
    )?;
    precommit0.check_on_curve(cs.namespace(|| "check pre_commit_0 on curve"))?;
    let precommit1 = AllocatedPoint::alloc(
      cs.namespace(|| "allocate pre_commit_1"),
      u.map(|u| u.precommitted.1.to_coordinates()),
    )?;
    precommit1.check_on_curve(cs.namespace(|| "check pre_commit_1 on curve"))?;

    Ok(AllocatedR1CSInstance {
      W,
      X0,
      X1,
      precommit0,
      precommit1,
    })
  }

  /// Absorb the provided instance in the RO
  pub fn absorb_in_ro(&self, ro: &mut E::ROCircuit) {
    ro.absorb(&self.W.x);
    ro.absorb(&self.W.y);
    ro.absorb(&self.W.is_infinity);
    ro.absorb(&self.X0);
    ro.absorb(&self.X1);
    ro.absorb(&self.precommit0.x);
    ro.absorb(&self.precommit0.y);
    ro.absorb(&self.precommit0.is_infinity);
    ro.absorb(&self.precommit1.x);
    ro.absorb(&self.precommit1.y);
    ro.absorb(&self.precommit1.is_infinity);
  }
}

/// An Allocated Relaxed R1CS Instance
pub struct AllocatedRelaxedR1CSInstance<E: Engine> {
  pub(crate) W: AllocatedPoint<E>,
  pub(crate) E: AllocatedPoint<E>,
  pub(crate) u: AllocatedNum<E::Base>,
  pub(crate) X0: BigNat<E::Base>,
  pub(crate) X1: BigNat<E::Base>,
  pub(crate) precommit0: AllocatedPoint<E>,
  pub(crate) precommit1: AllocatedPoint<E>,
}

impl<E: Engine> AllocatedRelaxedR1CSInstance<E> {
  /// Allocates the given `RelaxedR1CSInstance` as a witness of the circuit
  pub fn alloc<CS: ConstraintSystem<<E as Engine>::Base>>(
    mut cs: CS,
    inst: Option<&SplitRelaxedR1CSInstance<E>>,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<Self, SynthesisError> {
    // We do not need to check that W or E are well-formed (e.g., on the curve) as we do a hash check
    // in the Nova augmented circuit, which ensures that the relaxed instance
    // came from a prior iteration of Nova.
    let W = AllocatedPoint::alloc(
      cs.namespace(|| "allocate W"),
      inst.map(|inst| inst.aux.comm_W.to_coordinates()),
    )?;

    let E = AllocatedPoint::alloc(
      cs.namespace(|| "allocate E"),
      inst.map(|inst| inst.aux.comm_E.to_coordinates()),
    )?;

    // u << |E::Base| despite the fact that u is a scalar.
    // So we parse all of its bytes as a E::Base element
    let u =
      alloc_scalar_as_base::<E, _>(cs.namespace(|| "allocate u"), inst.map(|inst| inst.aux.u))?;

    // Allocate X0 and X1. If the input instance is None, then allocate default values 0.
    let X0 = BigNat::alloc_from_nat(
      cs.namespace(|| "allocate X[0]"),
      || {
        Ok(f_to_nat(
          &inst.map_or(E::Scalar::ZERO, |inst| inst.aux.X[0]),
        ))
      },
      limb_width,
      n_limbs,
    )?;

    let X1 = BigNat::alloc_from_nat(
      cs.namespace(|| "allocate X[1]"),
      || {
        Ok(f_to_nat(
          &inst.map_or(E::Scalar::ZERO, |inst| inst.aux.X[1]),
        ))
      },
      limb_width,
      n_limbs,
    )?;

    let precommit0 = AllocatedPoint::alloc(
      cs.namespace(|| "allocate pre_commit_0"),
      inst.map(|inst| inst.precommitted.0.to_coordinates()),
    )?;
    let precommit1 = AllocatedPoint::alloc(
      cs.namespace(|| "allocate pre_commit_1"),
      inst.map(|inst| inst.precommitted.1.to_coordinates()),
    )?;

    Ok(AllocatedRelaxedR1CSInstance {
      W,
      E,
      u,
      X0,
      X1,
      precommit0,
      precommit1,
    })
  }

  /// Allocates the hardcoded default `RelaxedR1CSInstance` in the circuit.
  /// W = E = 0, u = 0, X0 = X1 = 0
  pub fn default<CS: ConstraintSystem<<E as Engine>::Base>>(
    mut cs: CS,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<Self, SynthesisError> {
    let W = AllocatedPoint::default(cs.namespace(|| "allocate W"))?;
    let E = W.clone();

    let u = W.x.clone(); // In the default case, W.x = u = 0

    // X0 and X1 are allocated and in the honest prover case set to zero
    // If the prover is malicious, it can set to arbitrary values, but the resulting
    // relaxed R1CS instance with the checked default values of W, E, and u must still be satisfying
    let X0 = BigNat::alloc_from_nat(
      cs.namespace(|| "allocate x_default[0]"),
      || Ok(f_to_nat(&E::Scalar::ZERO)),
      limb_width,
      n_limbs,
    )?;

    let X1 = BigNat::alloc_from_nat(
      cs.namespace(|| "allocate x_default[1]"),
      || Ok(f_to_nat(&E::Scalar::ZERO)),
      limb_width,
      n_limbs,
    )?;

    let precommit0 = W.clone();
    let precommit1 = W.clone();

    Ok(AllocatedRelaxedR1CSInstance {
      W,
      E,
      u,
      X0,
      X1,
      precommit0,
      precommit1,
    })
  }

  /// Allocates the R1CS Instance as a `RelaxedR1CSInstance` in the circuit.
  /// E = 0, u = 1
  pub fn from_r1cs_instance<CS: ConstraintSystem<<E as Engine>::Base>>(
    mut cs: CS,
    inst: AllocatedR1CSInstance<E>,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<Self, SynthesisError> {
    let E = AllocatedPoint::default(cs.namespace(|| "allocate default E"))?;

    let u = alloc_one(cs.namespace(|| "one"));

    let X0 = BigNat::from_num(
      cs.namespace(|| "allocate X0 from relaxed r1cs"),
      &Num::from(inst.X0),
      limb_width,
      n_limbs,
    )?;

    let X1 = BigNat::from_num(
      cs.namespace(|| "allocate X1 from relaxed r1cs"),
      &Num::from(inst.X1),
      limb_width,
      n_limbs,
    )?;

    Ok(AllocatedRelaxedR1CSInstance {
      W: inst.W,
      E,
      u,
      X0,
      X1,
      precommit0: inst.precommit0,
      precommit1: inst.precommit1,
    })
  }

  /// Absorb the provided instance in the RO
  pub fn absorb_in_ro<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
    ro: &mut E::ROCircuit,
  ) -> Result<(), SynthesisError> {
    ro.absorb(&self.W.x);
    ro.absorb(&self.W.y);
    ro.absorb(&self.W.is_infinity);
    ro.absorb(&self.E.x);
    ro.absorb(&self.E.y);
    ro.absorb(&self.E.is_infinity);
    ro.absorb(&self.u);

    // Analyze X0 as limbs
    let X0_bn = self
      .X0
      .as_limbs()
      .iter()
      .enumerate()
      .map(|(i, limb)| {
        limb.as_allocated_num(cs.namespace(|| format!("convert limb {i} of X_r[0] to num")))
      })
      .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;

    // absorb each of the limbs of X[0]
    for limb in X0_bn {
      ro.absorb(&limb);
    }

    // Analyze X1 as limbs
    let X1_bn = self
      .X1
      .as_limbs()
      .iter()
      .enumerate()
      .map(|(i, limb)| {
        limb.as_allocated_num(cs.namespace(|| format!("convert limb {i} of X_r[1] to num")))
      })
      .collect::<Result<Vec<AllocatedNum<E::Base>>, _>>()?;

    // absorb each of the limbs of X[1]
    for limb in X1_bn {
      ro.absorb(&limb);
    }

    // absorb precommit0
    ro.absorb(&self.precommit0.x);
    ro.absorb(&self.precommit0.y);
    ro.absorb(&self.precommit0.is_infinity);
    // absorb precommit1
    ro.absorb(&self.precommit1.x);
    ro.absorb(&self.precommit1.y);
    ro.absorb(&self.precommit1.is_infinity);

    Ok(())
  }

  /// Folds self with a relaxed r1cs instance and returns the result
  pub fn fold_with_r1cs<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
    params: &AllocatedNum<E::Base>, // hash of R1CSShape of F'
    u: &AllocatedR1CSInstance<E>,
    T: &AllocatedPoint<E>,
    ro_consts: ROConstantsCircuit<E>,
    limb_width: usize,
    n_limbs: usize,
  ) -> Result<AllocatedRelaxedR1CSInstance<E>, SynthesisError> {
    // Compute r:
    let mut ro = E::ROCircuit::new(ro_consts);
    ro.absorb(params);

    // running instance `U` does not need to absorbed since u.X[0] = Hash(params, U, i, z0, zi)
    u.absorb_in_ro(&mut ro);

    ro.absorb(&T.x);
    ro.absorb(&T.y);
    ro.absorb(&T.is_infinity);
    let r_bits = ro.squeeze(cs.namespace(|| "r bits"), NUM_CHALLENGE_BITS)?;
    let r = le_bits_to_num(cs.namespace(|| "r"), &r_bits)?;

    // W_fold = self.W + r * u.W
    let rW = u.W.scalar_mul(cs.namespace(|| "r * u.W"), &r_bits)?;
    let W_fold = self.W.add(cs.namespace(|| "self.W + r * u.W"), &rW)?;

    // precommit0_fold = self.precommit0 + r * u.precommit0
    let r_precommit0 = u
      .precommit0
      .scalar_mul(cs.namespace(|| "r * u.precommit0"), &r_bits)?;
    let precommit0_fold = self.precommit0.add(
      cs.namespace(|| "self.precommit0 + r * u.precommit0"),
      &r_precommit0,
    )?;

    // precommit1_fold = self.precommit1 + r * u.precommit1
    let r_precommit1 = u
      .precommit1
      .scalar_mul(cs.namespace(|| "r * u.precommit1"), &r_bits)?;
    let precommit1_fold = self.precommit1.add(
      cs.namespace(|| "self.precommit1 + r * u.precommit1"),
      &r_precommit1,
    )?;

    // E_fold = self.E + r * T
    let rT = T.scalar_mul(cs.namespace(|| "r * T"), &r_bits)?;
    let E_fold = self.E.add(cs.namespace(|| "self.E + r * T"), &rT)?;

    // u_fold = u_r + r
    let u_fold = AllocatedNum::alloc(cs.namespace(|| "u_fold"), || {
      Ok(*self.u.get_value().get()? + r.get_value().get()?)
    })?;
    cs.enforce(
      || "Check u_fold",
      |lc| lc,
      |lc| lc,
      |lc| lc + u_fold.get_variable() - self.u.get_variable() - r.get_variable(),
    );

    // Fold the IO:
    // Analyze r into limbs
    let r_bn = BigNat::from_num(
      cs.namespace(|| "allocate r_bn"),
      &Num::from(r),
      limb_width,
      n_limbs,
    )?;

    // Allocate the order of the non-native field as a constant
    let m_bn = alloc_bignat_constant(
      cs.namespace(|| "alloc m"),
      &E::GE::group_params().2,
      limb_width,
      n_limbs,
    )?;

    // Analyze X0 to bignat
    let X0_bn = BigNat::from_num(
      cs.namespace(|| "allocate X0_bn"),
      &Num::from(u.X0.clone()),
      limb_width,
      n_limbs,
    )?;

    // Fold self.X[0] + r * X[0]
    let (_, r_0) = X0_bn.mult_mod(cs.namespace(|| "r*X[0]"), &r_bn, &m_bn)?;
    // add X_r[0]
    let r_new_0 = self.X0.add(&r_0)?;
    // Now reduce
    let X0_fold = r_new_0.red_mod(cs.namespace(|| "reduce folded X[0]"), &m_bn)?;

    // Analyze X1 to bignat
    let X1_bn = BigNat::from_num(
      cs.namespace(|| "allocate X1_bn"),
      &Num::from(u.X1.clone()),
      limb_width,
      n_limbs,
    )?;

    // Fold self.X[1] + r * X[1]
    let (_, r_1) = X1_bn.mult_mod(cs.namespace(|| "r*X[1]"), &r_bn, &m_bn)?;
    // add X_r[1]
    let r_new_1 = self.X1.add(&r_1)?;
    // Now reduce
    let X1_fold = r_new_1.red_mod(cs.namespace(|| "reduce folded X[1]"), &m_bn)?;

    Ok(Self {
      W: W_fold,
      E: E_fold,
      u: u_fold,
      X0: X0_fold,
      X1: X1_fold,
      precommit0: precommit0_fold,
      precommit1: precommit1_fold,
    })
  }

  /// If the condition is true then returns this otherwise it returns the other
  pub fn conditionally_select<CS: ConstraintSystem<<E as Engine>::Base>>(
    &self,
    mut cs: CS,
    other: &AllocatedRelaxedR1CSInstance<E>,
    condition: &Boolean,
  ) -> Result<AllocatedRelaxedR1CSInstance<E>, SynthesisError> {
    let W = AllocatedPoint::conditionally_select(
      cs.namespace(|| "W = cond ? self.W : other.W"),
      &self.W,
      &other.W,
      condition,
    )?;

    let E = AllocatedPoint::conditionally_select(
      cs.namespace(|| "E = cond ? self.E : other.E"),
      &self.E,
      &other.E,
      condition,
    )?;

    let u = conditionally_select(
      cs.namespace(|| "u = cond ? self.u : other.u"),
      &self.u,
      &other.u,
      condition,
    )?;

    let X0 = conditionally_select_bignat(
      cs.namespace(|| "X[0] = cond ? self.X[0] : other.X[0]"),
      &self.X0,
      &other.X0,
      condition,
    )?;

    let X1 = conditionally_select_bignat(
      cs.namespace(|| "X[1] = cond ? self.X[1] : other.X[1]"),
      &self.X1,
      &other.X1,
      condition,
    )?;

    let precommit0 = AllocatedPoint::conditionally_select(
      cs.namespace(|| "precommit0 = cond ? self.precommit0 : other.precommit0"),
      &self.precommit0,
      &other.precommit0,
      condition,
    )?;

    let precommit1 = AllocatedPoint::conditionally_select(
      cs.namespace(|| "precommit1 = cond ? self.precommit1 : other.precommit1"),
      &self.precommit1,
      &other.precommit1,
      condition,
    )?;

    Ok(AllocatedRelaxedR1CSInstance {
      W,
      E,
      u,
      X0,
      X1,
      precommit0,
      precommit1,
    })
  }
}
