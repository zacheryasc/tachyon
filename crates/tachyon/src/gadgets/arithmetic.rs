//! Range checks and integer operations for proof steps.

use derive_more::Deref;
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

/// A fixed-width Boolean decomposition.
#[derive(Deref)]
pub(crate) struct Bits<'dr, D: Driver<'dr>, const N: usize>(FixedVec<Boolean<'dr, D>, ConstLen<N>>);

impl<'dr, D: Driver<'dr, F = Fp>, const N: usize> Bits<'dr, D, N> {
    #[expect(
        clippy::indexing_slicing,
        reason = "multipack packs N bits into one chunk"
    )]
    pub(crate) fn new(dr: &mut D, value: &Element<'dr, D>) -> Result<Self> {
        const {
            assert!(
                N > 0 && N <= 64,
                "decomposition width must be at most 64 bits"
            );
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
        multipack(dr, &bits)?[0].enforce_equal(dr, value)?;
        Ok(Self(bits))
    }

    /// The caller supplies a public maximum below 2^N. Both the value and
    /// `maximum - value` must fit N bits, preventing field wraparound.
    /// Returns the checked decomposition of `value` for arithmetic consumers.
    pub(crate) fn bounded(dr: &mut D, value: &Element<'dr, D>, maximum: u64) -> Result<Self> {
        let value_bits = Self::new(dr, value)?;
        let maximum_element = Element::constant(dr, Fp::from(maximum));
        let slack = maximum_element.sub(dr, value);
        Self::new(dr, &slack)?;
        Ok(value_bits)
    }
}

/// A range-checked epoch index inside a circuit.
pub(crate) struct EpochIndex<'dr, D: Driver<'dr>>(Element<'dr, D>);

impl<'dr, D: Driver<'dr, F = Fp>> EpochIndex<'dr, D> {
    pub(crate) fn new(dr: &mut D, epoch: &Element<'dr, D>) -> Result<Self> {
        Bits::<D, 32>::bounded(dr, epoch, u64::from(EPOCH_MAX))?;
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
