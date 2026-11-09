//! Point arithmetic that permits identity intermediates and returns finite
//! points to proof steps.

use alloc::vec::Vec;

use ragu_core::{
    Error, Result,
    drivers::{Coeff, Driver},
    maybe::Maybe as _,
};
use ragu_primitives::{Boolean, Element, GadgetExt as _, Point};
use udon::{curve::Affine as _, field::Field as _};

use crate::pasta::{EpAffine, Fp};

// Only the complete arithmetic below uses an infinity flag. Header fields
// and the exported results remain finite `Point`s.
pub(crate) struct CompletePoint<'dr, D: Driver<'dr>> {
    x: Element<'dr, D>,
    y: Element<'dr, D>,
    infinity: Boolean<'dr, D>,
}

pub(crate) fn coordinates<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    point: &Point<'dr, D, EpAffine>,
) -> Result<[Element<'dr, D>; 2]> {
    let mut coordinates = Vec::new();
    point.write(dr, &mut coordinates)?;
    coordinates
        .try_into()
        .map_err(|_err| Error::InvalidWitness("point must write two coordinates".into()))
}

pub(crate) fn from_point<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    point: &Point<'dr, D, EpAffine>,
) -> Result<CompletePoint<'dr, D>> {
    let [x, y] = coordinates(dr, point)?;
    let one = Element::constant(dr, Fp::ONE);
    Ok(CompletePoint {
        x,
        y,
        infinity: one.is_zero(dr, &mut ())?,
    })
}

fn select<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    condition: &Boolean<'dr, D>,
    left: &CompletePoint<'dr, D>,
    right: &CompletePoint<'dr, D>,
) -> Result<CompletePoint<'dr, D>> {
    let x = condition.conditional_select(dr, &left.x, &right.x)?;
    let y = condition.conditional_select(dr, &left.y, &right.y)?;
    let infinity =
        condition.conditional_select(dr, &left.infinity.element(), &right.infinity.element())?;
    let one = Element::constant(dr, Fp::ONE);
    Ok(CompletePoint {
        x,
        y,
        infinity: infinity.is_equal(dr, &mut (), &one)?,
    })
}

pub(crate) fn add_complete<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    left: &CompletePoint<'dr, D>,
    right: &CompletePoint<'dr, D>,
) -> Result<CompletePoint<'dr, D>> {
    let one = Element::constant(dr, Fp::ONE);
    let same_x = left.x.is_equal(dr, &mut (), &right.x)?;
    let same_y = left.y.is_equal(dr, &mut (), &right.y)?;
    let dx = right.x.sub(dr, &left.x);
    let denominator = same_x
        .conditional_select(dr, &dx, &one)?
        .enforce_nonzero(dr)?;
    let dy = right.y.sub(dr, &left.y);
    let slope = dy.divide(dr, &denominator)?;
    let add_x = slope.square(dr)?.sub(dr, &left.x).sub(dr, &right.x);
    let difference = left.x.sub(dr, &add_x);
    let add_y = slope.mul(dr, &difference)?.sub(dr, &left.y);

    let twice_y = left.y.double(dr);
    let double_denominator = left
        .infinity
        .conditional_select(dr, &twice_y, &one)?
        .enforce_nonzero(dr)?;
    let numerator = left.x.square(dr)?.scale(dr, Coeff::Arbitrary(Fp::from(3)));
    let double_slope = numerator.divide(dr, &double_denominator)?;
    let twice_x = left.x.double(dr);
    let double_x = double_slope.square(dr)?.sub(dr, &twice_x);
    let double_difference = left.x.sub(dr, &double_x);
    let double_y = double_slope.mul(dr, &double_difference)?.sub(dr, &left.y);

    let x = same_x.conditional_select(dr, &add_x, &double_x)?;
    let y = same_x.conditional_select(dr, &add_y, &double_y)?;
    let not_same_y = same_y.not(dr);
    let infinity = same_x.and(dr, &not_same_y)?;
    let sum = CompletePoint { x, y, infinity };
    let left_corrected = select(dr, &left.infinity, &sum, right)?;
    select(dr, &right.infinity, &left_corrected, left)
}

pub(crate) fn finish<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    computed: &CompletePoint<'dr, D>,
) -> Result<Point<'dr, D, EpAffine>> {
    computed.infinity.element().enforce_zero(dr)?;
    let native = D::try_just(|| {
        EpAffine::from_xy(*computed.x.value().take(), *computed.y.value().take()).ok_or_else(|| {
            Error::InvalidWitness("complete arithmetic produced an invalid point".into())
        })
    })?;
    let point = Point::alloc(dr, native)?;
    let [x, y] = coordinates(dr, &point)?;
    computed.x.enforce_equal(dr, &x)?;
    computed.y.enforce_equal(dr, &y)?;
    Ok(point)
}

#[cfg(test)]
mod tests;

pub(crate) mod fixed_base;
