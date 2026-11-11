//! Range-checked epoch indices for proof steps.

use ragu_core::{
    Result,
    drivers::{Driver, DriverValue},
    maybe::Maybe as _,
};
use ragu_primitives::{
    Boolean, Element, GadgetExt as _, multipack,
    vec::{ConstLen, FixedVec},
};
use udon::field::Field as _;

use crate::{constants::EPOCH_MAX, pasta::Fp, primitives};

/// A range-checked epoch index inside a circuit.
pub(crate) struct EpochIndex<'dr, D: Driver<'dr>>(Element<'dr, D>);

impl<'dr, D: Driver<'dr, F = Fp>> EpochIndex<'dr, D> {
    /// Both the index and `EPOCH_MAX - index` must fit 32 bits, preventing
    /// field wraparound.
    #[expect(
        clippy::indexing_slicing,
        reason = "multipack packs 32 bits into one chunk"
    )]
    pub(crate) fn new(dr: &mut D, epoch: &Element<'dr, D>) -> Result<Self> {
        let maximum = Element::constant(dr, Fp::from(u64::from(EPOCH_MAX)));
        let slack = maximum.sub(dr, epoch);
        for value in [epoch, &slack] {
            let bits = FixedVec::<_, ConstLen<32>>::try_from_fn(|index| {
                Boolean::alloc(
                    dr,
                    &mut (),
                    value
                        .value()
                        .map(|candidate| candidate.to_le_bits().as_ref()[index]),
                )
            })?;
            multipack(dr, &bits)?[0].enforce_equal(dr, value)?;
        }
        Ok(Self(epoch.clone()))
    }

    pub(crate) fn next(&self, dr: &mut D) -> Result<Self> {
        let one = Element::constant(dr, Fp::ONE);
        let next = self.0.add(dr, &one);
        Self::new(dr, &next)
    }

    /// The native index. Witness generation rejects an out-of-range element,
    /// as the range check rejects it in the circuit.
    pub(crate) fn value(&self) -> Result<DriverValue<D, primitives::EpochIndex>> {
        D::try_just(|| {
            primitives::EpochIndex::try_from(*self.0.value().take())
                .map_err(|_err| ragu_core::Error::InvalidWitness("epoch index out of range".into()))
        })
    }

    pub(crate) fn into_element(self) -> Element<'dr, D> {
        self.0
    }
}

#[cfg(test)]
mod tests;
