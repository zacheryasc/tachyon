//! Range checks and integer operations for proof steps.

use ragu_core::{
    Result,
    drivers::{Coeff, Driver, DriverValue},
    maybe::Maybe as _,
};
use ragu_primitives::{
    Boolean, Element, GadgetExt as _, multipack,
    vec::{ConstLen, FixedVec},
};
use udon::field::Field as _;

use crate::{constants::EPOCH_MAX, pasta::Fp, primitives::EpochIndex};

/// At 255 bits, the representation must also be below the field modulus;
/// otherwise distinct bit strings could represent the same field element.
#[expect(clippy::indexing_slicing, reason = "fixed field and bit widths")]
pub(crate) fn bits<'dr, D: Driver<'dr, F = Fp>, const N: usize>(
    dr: &mut D,
    value: &Element<'dr, D>,
) -> Result<FixedVec<Boolean<'dr, D>, ConstLen<N>>> {
    const {
        assert!(N > 0 && N <= 255, "decomposition width must fit the field");
    }
    let bits = FixedVec::try_from_fn(|i| {
        Boolean::alloc(
            dr,
            &mut (),
            value
                .value()
                .map(|candidate| candidate.to_le_bits().as_ref()[i]),
        )
    })?;
    let packed = multipack(dr, &bits)?;
    let recomposed = if N == 255 {
        let high = packed[1].scale(dr, Coeff::Arbitrary(Fp::from(2).pow_u64(254)));
        packed[0].add(dr, &high)
    } else {
        packed[0].clone()
    };
    recomposed.enforce_equal(dr, value)?;
    if N == 255 {
        canonical(dr, &bits)?;
    }
    Ok(bits)
}

/// The caller supplies a public maximum below 2^N. Both the value and
/// `maximum - value` must fit N bits, preventing field wraparound.
/// Returns the checked decomposition of `value` for arithmetic consumers.
pub(crate) fn bounded<'dr, D: Driver<'dr, F = Fp>, const N: usize>(
    dr: &mut D,
    value: &Element<'dr, D>,
    maximum: u64,
) -> Result<FixedVec<Boolean<'dr, D>, ConstLen<N>>> {
    const {
        assert!(
            N > 0 && N <= 64,
            "bounded integer width must be at most 64 bits"
        );
    }
    let value_bits = bits::<D, N>(dr, value)?;
    let maximum_element = Element::constant(dr, Fp::from(maximum));
    let slack = maximum_element.sub(dr, value);
    bits::<D, N>(dr, &slack)?;
    Ok(value_bits)
}

/// Compare the canonical field bits with p-1, sharing a product across each
/// maximal zero run. Its sum has at most 254 Boolean terms and cannot wrap.
#[expect(clippy::indexing_slicing, reason = "fixed 255-bit canonical encoding")]
fn canonical<'dr, D: Driver<'dr, F = Fp>>(dr: &mut D, bits: &[Boolean<'dr, D>]) -> Result<()> {
    if bits.len() != 255 {
        return Err(ragu_core::Error::InvalidWitness(
            "canonical field representation must have 255 bits".into(),
        ));
    }
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

pub(crate) fn epoch_next<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    epoch: &Element<'dr, D>,
) -> Result<Element<'dr, D>> {
    bounded::<D, 32>(dr, epoch, u64::from(EPOCH_MAX))?;
    let one = Element::constant(dr, Fp::ONE);
    let next = epoch.add(dr, &one);
    bounded::<D, 32>(dr, &next, u64::from(EPOCH_MAX))?;
    Ok(next)
}

/// Requires an epoch that has already passed the range check.
pub(crate) fn epoch_value<'dr, D: Driver<'dr, F = Fp>>(
    epoch: &Element<'dr, D>,
) -> DriverValue<D, EpochIndex> {
    epoch.value().map(|candidate| {
        let [first, second, third, fourth, ..] = candidate.to_bytes();
        EpochIndex::new(u32::from_le_bytes([first, second, third, fourth]))
    })
}

#[cfg(test)]
mod tests;
