//! Offset radix-4 fixed-base walks inside their consuming steps.
//!
//! Every interior addition has distinct affine x coordinates for every Boolean
//! assignment: its positive prefix is smaller than the next offset digit, and
//! their sum is below q. Only the finite-input complete adder handles the top.

use alloc::vec::Vec;
use core::array;

use lazy_static::lazy_static;
use ragu_core::{
    Error, Result,
    drivers::{Coeff, Driver, DriverValue},
    maybe::Maybe as _,
};
use ragu_primitives::{
    Boolean, Element, GadgetExt as _, Point,
    vec::{ConstLen, FixedVec},
};
use udon::{
    curve::{Affine as _, Projective as _},
    field::Field as _,
};

use super::{
    super::super::{
        constants::MAX_MONEY,
        keys::public::ACTION_AUTH_GENERATOR,
        pasta::{Ep, EpAffine, Fp, Fq},
        relations::arithmetic,
        value,
    },
    CompletePoint,
};

pub(crate) struct Table<const W: usize> {
    // Native constant storage only. Circuit iteration is bounded by const W,
    // never this vector's length; the constructor is private to this module.
    low: Vec<[EpAffine; 4]>,
    top: [EpAffine; 8],
}

lazy_static! {
    pub(crate) static ref R_TABLE: Table<126> = table(*value::VALUE_COMMIT_R, Ep::identity());
    pub(crate) static ref G_TABLE: Table<126> =
        table(ACTION_AUTH_GENERATOR.to_projective(), Ep::identity());
    pub(crate) static ref V_TABLE: Table<24> = table(*value::VALUE_COMMIT_V, Ep::identity());
    pub(crate) static ref NEG_V: Table<24> = table(-*value::VALUE_COMMIT_V, Ep::identity());
    pub(crate) static ref FEE_V: Table<24> = table(
        *value::VALUE_COMMIT_V,
        -*value::VALUE_COMMIT_V * Fq::from(MAX_MONEY)
    );
}

#[cfg(test)]
fn initialize() {
    lazy_static::initialize(&R_TABLE);
    lazy_static::initialize(&G_TABLE);
    lazy_static::initialize(&V_TABLE);
    lazy_static::initialize(&NEG_V);
    lazy_static::initialize(&FEE_V);
}

fn table<const W: usize>(base: Ep, correction: Ep) -> Table<W> {
    assert!(!base.is_identity(), "fixed bases must be nonidentity");
    let mut power = Fq::ONE;
    let mut offset = Fq::ZERO;
    let mut low = Vec::with_capacity(W);
    for _ in 0..W {
        low.push(array::from_fn(|digit| {
            (base * (Fq::from(u64::try_from(digit + 2).unwrap_or(u64::MAX)) * power)).to_affine()
        }));
        offset += Fq::from(2) * power;
        power *= Fq::from(4);
    }
    let top = array::from_fn(|digit| {
        let point = base * (Fq::from(u64::try_from(digit).unwrap_or(u64::MAX)) * power - offset)
            + correction;
        assert!(!point.is_identity(), "every fixed top entry must be finite");
        point.to_affine()
    });
    Table { low, top }
}

struct Finite<'dr, D: Driver<'dr>> {
    x: Element<'dr, D>,
    y: Element<'dr, D>,
}

#[cfg(test)]
fn constant<'dr, D: Driver<'dr, F = Fp>>(dr: &mut D, point: EpAffine) -> Result<Finite<'dr, D>> {
    let (x, y) = point
        .coordinates()
        .ok_or_else(|| Error::InvalidWitness("finite constant required".into()))?;
    Ok(Finite {
        x: Element::constant(dr, x),
        y: Element::constant(dr, y),
    })
}

#[expect(clippy::indexing_slicing, reason = "fixed Boolean cube")]
fn coefficients(mut values: [Fp; 8]) -> [Fp; 8] {
    for bit in 0..3 {
        for index in 0..8 {
            if index & (1 << bit) != 0 {
                values[index] -= values[index ^ (1 << bit)];
            }
        }
    }
    values
}

fn select_low<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    row: &[EpAffine; 4],
    bits: [&Boolean<'dr, D>; 2],
) -> Result<Finite<'dr, D>> {
    let coordinates = row.map(|point| point.coordinates().unwrap_or((Fp::ZERO, Fp::ZERO)));
    let product = bits[0].element().mul(dr, &bits[1].element())?;
    let coordinate = |driver: &mut D, values: [Fp; 4]| {
        let mut out = Element::constant(driver, values[0]);
        for (element, coefficient) in [
            (bits[0].element(), values[1] - values[0]),
            (bits[1].element(), values[2] - values[0]),
            (
                product.clone(),
                values[3] - values[2] - values[1] + values[0],
            ),
        ] {
            let term = element.scale(driver, Coeff::Arbitrary(coefficient));
            out = out.add(driver, &term);
        }
        out
    };
    Ok(Finite {
        x: coordinate(dr, coordinates.map(|pair| pair.0)),
        y: coordinate(dr, coordinates.map(|pair| pair.1)),
    })
}

fn select_top<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    row: &[EpAffine; 8],
    bits: [&Boolean<'dr, D>; 3],
) -> Result<Finite<'dr, D>> {
    let low = bits[0].element();
    let middle = bits[1].element();
    let high = bits[2].element();
    let low_middle = low.mul(dr, &middle)?;
    let low_high = low.mul(dr, &high)?;
    let middle_high = middle.mul(dr, &high)?;
    let triple = low_middle.mul(dr, &high)?;
    let monomials = [
        Element::one(),
        low,
        middle,
        low_middle,
        high,
        low_high,
        middle_high,
        triple,
    ];
    let coordinates = row.map(|point| point.coordinates().unwrap_or((Fp::ZERO, Fp::ZERO)));
    let coordinate = |driver: &mut D, values: [Fp; 8]| {
        let coefficients = coefficients(values);
        let mut out = Element::zero(driver);
        for (element, coefficient) in monomials.iter().zip(coefficients) {
            let term = element.scale(driver, Coeff::Arbitrary(coefficient));
            out = out.add(driver, &term);
        }
        out
    };
    Ok(Finite {
        x: coordinate(dr, coordinates.map(|pair| pair.0)),
        y: coordinate(dr, coordinates.map(|pair| pair.1)),
    })
}

/// Pins slope and its square in two gates. Caller proves denominator nonzero.
fn slope<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    numerator: &Element<'dr, D>,
    denominator: &Element<'dr, D>,
) -> Result<(Element<'dr, D>, Element<'dr, D>)> {
    let assignment = D::try_just(|| {
        let inverse = denominator
            .value()
            .take()
            .invert()
            .ok_or_else(|| Error::InvalidWitness("zero affine denominator".into()))?;
        Ok(*numerator.value().take() * inverse)
    })?;
    let (slope, square) = Element::alloc_square(dr, assignment)?;
    let (slope_wire, denominator_wire, numerator_wire) = dr.mul(|| {
        Ok((
            Coeff::Arbitrary(*slope.value().take()),
            Coeff::Arbitrary(*denominator.value().take()),
            Coeff::Arbitrary(*numerator.value().take()),
        ))
    })?;
    dr.enforce_equal(&slope_wire, slope.wire())?;
    dr.enforce_equal(&denominator_wire, denominator.wire())?;
    dr.enforce_equal(&numerator_wire, numerator.wire())?;
    Ok((slope, square))
}

/// Private to the fixed-base module: only offset-walk interiors may call this.
/// Distinct x coordinates must hold for every satisfying Boolean assignment.
fn add_incomplete<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    left: &Finite<'dr, D>,
    right: &Finite<'dr, D>,
) -> Result<Finite<'dr, D>> {
    let numerator = right.y.sub(dr, &left.y);
    let denominator = right.x.sub(dr, &left.x);
    let (slope, square) = slope(dr, &numerator, &denominator)?;
    let x = square.sub(dr, &left.x).sub(dr, &right.x);
    let difference = left.x.sub(dr, &x);
    let y = slope.mul(dr, &difference)?.sub(dr, &left.y);
    Ok(Finite { x, y })
}

/// Complete only for finite inputs. Odd prime order rules out y=0 doubling.
fn add_finite<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    left: &Finite<'dr, D>,
    right: &Finite<'dr, D>,
) -> Result<CompletePoint<'dr, D>> {
    let same_x = left.x.is_equal(dr, &mut (), &right.x)?;
    let same_y = left.y.is_equal(dr, &mut (), &right.y)?;
    let square = left.x.square(dr)?;
    let double_numerator = square.scale(dr, Coeff::Arbitrary(Fp::from(3)));
    let add_numerator = right.y.sub(dr, &left.y);
    let numerator = same_x.conditional_select(dr, &add_numerator, &double_numerator)?;
    let double_denominator = left.y.double(dr);
    let add_denominator = right.x.sub(dr, &left.x);
    let denominator = same_x.conditional_select(dr, &add_denominator, &double_denominator)?;
    let (slope, slope_square) = slope(dr, &numerator, &denominator)?;
    let x = slope_square.sub(dr, &left.x).sub(dr, &right.x);
    let difference = left.x.sub(dr, &x);
    let y = slope.mul(dr, &difference)?.sub(dr, &left.y);
    let not_same_y = same_y.not(dr);
    let infinity = same_x.and(dr, &not_same_y)?;
    Ok(CompletePoint { x, y, infinity })
}

/// Interior coefficients satisfy 0 < A < b and A+b < q for W <= 126,
/// excluding both equality and inverses. The top addition is always complete.
#[expect(
    clippy::indexing_slicing,
    clippy::missing_asserts_for_indexing,
    reason = "fixed mixed-width windows, never witness-length loops"
)]
pub(crate) fn walk<'dr, D: Driver<'dr, F = Fp>, const W: usize>(
    dr: &mut D,
    table: &Table<W>,
    bits: &[Boolean<'dr, D>],
) -> Result<CompletePoint<'dr, D>> {
    const {
        assert!(W > 0 && W <= 126, "the offset-walk theorem covers W=1..126");
    }
    let mut accumulator = select_low(dr, &table.low[0], [&bits[0], &bits[1]])?;
    for window in 1..W {
        let digit = select_low(
            dr,
            &table.low[window],
            [&bits[2 * window], &bits[2 * window + 1]],
        )?;
        accumulator = add_incomplete(dr, &accumulator, &digit)?;
    }
    let top = select_top(
        dr,
        &table.top,
        [&bits[2 * W], &bits[2 * W + 1], &bits[2 * W + 2]],
    )?;
    add_finite(dr, &accumulator, &top)
}

#[expect(clippy::indexing_slicing, reason = "fixed 255-bit canonical encoding")]
pub(crate) fn canonical<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    bits: &[Boolean<'dr, D>],
) -> Result<()> {
    let maximum = (-Fp::ONE).to_le_bits();
    let mut equal = bits[254].element();
    let mut run = Element::zero(dr);
    let mut pending = false;
    for index in (0..254).rev() {
        if maximum.as_ref()[index] {
            if pending {
                equal.mul(dr, &run)?.enforce_zero(dr)?;
                run = Element::zero(dr);
                pending = false;
            }
            equal = equal.mul(dr, &bits[index].element())?;
        } else {
            run = run.add(dr, &bits[index].element());
            pending = true;
        }
    }
    if pending {
        equal.mul(dr, &run)?.enforce_zero(dr)?;
    }
    Ok(())
}

#[expect(clippy::indexing_slicing, reason = "native fixed field representation")]
pub(crate) fn hash_bits<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    value: &Element<'dr, D>,
) -> Result<FixedVec<Boolean<'dr, D>, ConstLen<255>>> {
    let bits = FixedVec::try_from_fn(|index| {
        Boolean::alloc(
            dr,
            &mut (),
            value
                .value()
                .map(|candidate| candidate.to_le_bits().as_ref()[index]),
        )
    })?;
    let mut recomposed = Element::zero(dr);
    for bit in bits.iter().rev() {
        recomposed = recomposed.double(dr).add(dr, &bit.element());
    }
    recomposed.enforce_equal(dr, value)?;
    canonical(dr, &bits)?;
    Ok(bits)
}

/// Free opening advice. No header or hash binds the integer encoding of rcv;
/// every 255-bit assignment represents an Fq opening after reduction mod q.
#[expect(clippy::indexing_slicing, reason = "native fixed field representation")]
pub(crate) fn free_bits<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    value: &DriverValue<D, Fq>,
) -> Result<FixedVec<Boolean<'dr, D>, ConstLen<255>>> {
    FixedVec::try_from_fn(|index| {
        Boolean::alloc(
            dr,
            &mut (),
            value
                .as_ref()
                .map(|candidate| candidate.to_le_bits().as_ref()[index]),
        )
    })
}

#[expect(
    clippy::type_complexity,
    reason = "returns the change expression and fixed slack bits without an alias"
)]
pub(crate) fn slacks<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    maximum: &Element<'dr, D>,
    fee: &Element<'dr, D>,
) -> Result<(Element<'dr, D>, FixedVec<Boolean<'dr, D>, ConstLen<51>>)> {
    arithmetic::bits::<D, 51>(dr, fee)?;
    let change = maximum.sub(dr, fee);
    arithmetic::bits::<D, 51>(dr, &change)
        .map_err(|_err| Error::InvalidWitness("FeeFuse: change is out of range".into()))?;
    let bound = Element::constant(dr, Fp::from(MAX_MONEY));
    let slack = bound.sub(dr, maximum);
    let bits = arithmetic::bits::<D, 51>(dr, &slack)
        .map_err(|_err| Error::InvalidWitness("FeeFuse: maximum fee exceeds MAX_MONEY".into()))?;
    Ok((change, bits))
}

pub(crate) fn amount_bits<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    value: &Element<'dr, D>,
) -> Result<FixedVec<Boolean<'dr, D>, ConstLen<51>>> {
    let bits = arithmetic::bits::<D, 51>(dr, value)?;
    let bound = Element::constant(dr, Fp::from(MAX_MONEY));
    let slack = bound.sub(dr, value);
    arithmetic::bits::<D, 51>(dr, &slack)?;
    Ok(bits)
}

pub(crate) fn commitment<'dr, D: Driver<'dr, F = Fp>, const NEGATIVE: bool>(
    dr: &mut D,
    amount: &[Boolean<'dr, D>],
    blind: &[Boolean<'dr, D>],
) -> Result<Point<'dr, D, EpAffine>> {
    let product = if NEGATIVE {
        walk(dr, &NEG_V, amount)?
    } else {
        walk(dr, &V_TABLE, amount)?
    };
    let blind_point = walk(dr, &R_TABLE, blind)?;
    let sum = super::add_complete(dr, &product, &blind_point)?;
    super::finish(dr, &sum)
}

#[cfg(test)]
mod tests;
