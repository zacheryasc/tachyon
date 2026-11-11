//! Fixed-width arithmetic and curve gadgets for proof steps.

use alloc::vec::Vec;

use ragu_core::{Error, Result, drivers::Driver};
use ragu_primitives::{Element, GadgetExt as _, Point};

use crate::pasta::{EpAffine, Fp};

pub(crate) mod arithmetic;
pub(crate) mod fixed_base;

/// The affine coordinates of a point, read through its [`Write`] encoding.
///
/// [`Write`]: ragu_primitives::io::Write
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
