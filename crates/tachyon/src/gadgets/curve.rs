//! Affine point arithmetic over finite points.
//!
//! Every addition either proves distinct x coordinates from integer bounds or
//! constrains them distinct, so no intermediate is the identity.

use alloc::vec::Vec;

use ragu_core::{Error, Result, drivers::Driver, maybe::Maybe as _};
use ragu_primitives::{Element, GadgetExt as _, Point};
use udon::curve::Affine as _;

use crate::pasta::{EpAffine, Fp};

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

/// Coordinates of a finite curve point. On-curve by construction: each value
/// is a fixed table entry, a checked [`Point`], or a sum of those computed by
/// a sound affine addition.
pub(crate) struct Finite<'dr, D: Driver<'dr>> {
    pub(crate) x: Element<'dr, D>,
    pub(crate) y: Element<'dr, D>,
}

impl<'dr, D: Driver<'dr, F = Fp>> Finite<'dr, D> {
    /// Reallocates the point as a [`Point`] for header fields.
    pub(crate) fn to_point(&self, dr: &mut D) -> Result<Point<'dr, D, EpAffine>> {
        let native = D::try_just(|| {
            EpAffine::from_xy(*self.x.value().take(), *self.y.value().take())
                .ok_or_else(|| Error::InvalidWitness("affine addition left the curve".into()))
        })?;
        let point = Point::alloc(dr, native)?;
        let [x, y] = coordinates(dr, &point)?;
        self.x.enforce_equal(dr, &x)?;
        self.y.enforce_equal(dr, &y)?;
        Ok(point)
    }
}

pub(crate) mod fixed_base;
