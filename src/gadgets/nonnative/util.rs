use super::{BitAccess, OptionExt};
use crate::frontend::{
  num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError, Variable,
};
use byteorder::WriteBytesExt;
use ff::PrimeField;
use num_bigint::{BigInt, Sign};
use std::{
  convert::From,
  io::{self, Write},
};

#[derive(Clone)]
/// A representation of a bit
pub struct Bit<Scalar: PrimeField, const NumSplits: usize> {
  /// The linear combination which constrain the value of the bit
  pub bit: LinearCombination<Scalar, NumSplits>,
}

#[derive(Clone)]
/// A representation of a bit-vector
pub struct Bitvector<Scalar: PrimeField, const NumSplits: usize> {
  /// The linear combination which constrain the values of the bits
  pub bits: Vec<LinearCombination<Scalar, NumSplits>>,
  /// The value of the bits (filled at witness-time)
  pub values: Option<Vec<bool>>,
  /// Allocated bit variables
  pub allocations: Vec<Bit<Scalar, NumSplits>>,
}

impl<Scalar: PrimeField, const NumSplits: usize> Bit<Scalar, NumSplits> {
  /// Allocate a variable in the constraint system which can only be a
  /// boolean value.
  pub fn alloc<CS: ConstraintSystem<Scalar, NumSplits>>(
    mut cs: CS,
    value: Option<bool>,
  ) -> Result<Self, SynthesisError> {
    let var = cs.alloc(
      || "boolean",
      || {
        if *value.grab()? {
          Ok(Scalar::ONE)
        } else {
          Ok(Scalar::ZERO)
        }
      },
    )?;

    // Constrain: (1 - a) * a = 0
    // This constrains a to be either 0 or 1.
    cs.enforce(
      || "boolean constraint",
      |lc| lc + CS::one() - var,
      |lc| lc + var,
      |lc| lc,
    );

    Ok(Self {
      bit: LinearCombination::zero() + var,
    })
  }
}

pub struct Num<Scalar: PrimeField, const NumSplits: usize> {
  pub(crate) num: LinearCombination<Scalar, NumSplits>,
  pub(crate) value: Option<Scalar>,
}

impl<Scalar: PrimeField, const NumSplits: usize> Num<Scalar, NumSplits> {
  pub const fn new(value: Option<Scalar>, num: LinearCombination<Scalar, NumSplits>) -> Self {
    Self { value, num }
  }
  pub fn alloc<CS, F>(mut cs: CS, value: F) -> Result<Self, SynthesisError>
  where
    CS: ConstraintSystem<Scalar, NumSplits>,
    F: FnOnce() -> Result<Scalar, SynthesisError>,
  {
    let mut new_value = None;
    let var = cs.alloc(
      || "num",
      || {
        let tmp = value()?;

        new_value = Some(tmp);

        Ok(tmp)
      },
    )?;

    Ok(Num {
      value: new_value,
      num: LinearCombination::zero() + var,
    })
  }

  pub fn fits_in_bits<CS: ConstraintSystem<Scalar, NumSplits>>(
    &self,
    mut cs: CS,
    n_bits: usize,
  ) -> Result<(), SynthesisError> {
    let v = self.value;

    // Allocate all but the first bit.
    let bits: Vec<Variable> = (1..n_bits)
      .map(|i| {
        cs.alloc(
          || format!("bit {i}"),
          || {
            let r = if *v.grab()?.get_bit(i).grab()? {
              Scalar::ONE
            } else {
              Scalar::ZERO
            };
            Ok(r)
          },
        )
      })
      .collect::<Result<_, _>>()?;

    for (i, v) in bits.iter().enumerate() {
      cs.enforce(
        || format!("{i} is bit"),
        |lc| lc + *v,
        |lc| lc + CS::one() - *v,
        |lc| lc,
      )
    }

    // Last bit
    cs.enforce(
      || "last bit",
      |mut lc| {
        let mut f = Scalar::ONE;
        lc = lc + &self.num;
        for v in bits.iter() {
          f = f.double();
          lc = lc - (f, *v);
        }
        lc
      },
      |mut lc| {
        lc = lc + CS::one();
        let mut f = Scalar::ONE;
        lc = lc - &self.num;
        for v in bits.iter() {
          f = f.double();
          lc = lc + (f, *v);
        }
        lc
      },
      |lc| lc,
    );
    Ok(())
  }

  /// Computes the natural number represented by an array of bits.
  /// Checks if the natural number equals `self`
  pub fn is_equal<CS: ConstraintSystem<Scalar, NumSplits>>(&self, mut cs: CS, other: &Bitvector<Scalar, NumSplits>) {
    let allocations = other.allocations.clone();
    let mut f = Scalar::ONE;
    let sum = allocations
      .iter()
      .fold(LinearCombination::zero(), |lc, bit| {
        let l = lc + (f, &bit.bit);
        f = f.double();
        l
      });
    let sum_lc = LinearCombination::zero() + &self.num - &sum;
    cs.enforce(|| "sum", |lc| lc + &sum_lc, |lc| lc + CS::one(), |lc| lc);
  }

  /// Compute the natural number represented by an array of limbs.
  /// The limbs are assumed to be based the `limb_width` power of 2.
  /// Low-index bits are low-order
  pub fn decompose<CS: ConstraintSystem<Scalar, NumSplits>>(
    &self,
    mut cs: CS,
    n_bits: usize,
  ) -> Result<Bitvector<Scalar, NumSplits>, SynthesisError> {
    let values: Option<Vec<bool>> = self.value.as_ref().map(|v| {
      let num = *v;
      (0..n_bits).map(|i| num.get_bit(i).unwrap()).collect()
    });
    let allocations: Vec<Bit<Scalar, NumSplits>> = (0..n_bits)
      .map(|bit_i| {
        Bit::alloc(
          cs.namespace(|| format!("bit{bit_i}")),
          values.as_ref().map(|vs| vs[bit_i]),
        )
      })
      .collect::<Result<Vec<_>, _>>()?;
    let mut f = Scalar::ONE;
    let sum = allocations
      .iter()
      .fold(LinearCombination::zero(), |lc, bit| {
        let l = lc + (f, &bit.bit);
        f = f.double();
        l
      });
    let sum_lc = LinearCombination::zero() + &self.num - &sum;
    cs.enforce(|| "sum", |lc| lc + &sum_lc, |lc| lc + CS::one(), |lc| lc);
    let bits: Vec<LinearCombination<Scalar, NumSplits>> = allocations
      .clone()
      .into_iter()
      .map(|a| LinearCombination::zero() + &a.bit)
      .collect();
    Ok(Bitvector {
      allocations,
      values,
      bits,
    })
  }

  pub fn as_allocated_num<CS: ConstraintSystem<Scalar, NumSplits>>(
    &self,
    mut cs: CS,
  ) -> Result<AllocatedNum<Scalar, NumSplits>, SynthesisError> {
    let new = AllocatedNum::alloc(cs.namespace(|| "alloc"), || Ok(*self.value.grab()?))?;
    cs.enforce(
      || "eq",
      |lc| lc,
      |lc| lc,
      |lc| lc + new.get_variable() - &self.num,
    );
    Ok(new)
  }
}

impl<Scalar: PrimeField, const NumSplits: usize> From<AllocatedNum<Scalar, NumSplits>> for Num<Scalar, NumSplits> {
  fn from(a: AllocatedNum<Scalar, NumSplits>) -> Self {
    Self::new(a.get_value(), LinearCombination::zero() + a.get_variable())
  }
}

fn write_be<F: PrimeField, W: Write>(f: &F, mut writer: W) -> io::Result<()> {
  for digit in f.to_repr().as_ref().iter().rev() {
    writer.write_u8(*digit)?;
  }

  Ok(())
}

/// Convert a field element to a natural number
pub fn f_to_nat<Scalar: PrimeField>(f: &Scalar) -> BigInt {
  let mut s = Vec::new();
  write_be(f, &mut s).unwrap(); // f.to_repr().write_be(&mut s).unwrap();
  BigInt::from_bytes_le(Sign::Plus, f.to_repr().as_ref())
}

/// Convert a natural number to a field element.
/// Returns `None` if the number is too big for the field.
pub fn nat_to_f<Scalar: PrimeField>(n: &BigInt) -> Option<Scalar> {
  Scalar::from_str_vartime(&format!("{n}"))
}
