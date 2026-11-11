//! Range checks and integer operations for proof steps.

use derive_more::Deref;
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

use crate::{
    constants::EPOCH_MAX,
    pasta::{Fp, Fq},
    primitives,
};

/// A fixed-width Boolean decomposition.
#[derive(Deref)]
pub(crate) struct Bits<'dr, D: Driver<'dr>, const N: usize>(FixedVec<Boolean<'dr, D>, ConstLen<N>>);

impl<'dr, D: Driver<'dr, F = Fp>, const N: usize> Bits<'dr, D, N> {
    /// At 255 bits, the representation must also be below the field modulus;
    /// otherwise distinct bit strings could represent the same field element.
    #[expect(clippy::indexing_slicing, reason = "fixed field and bit widths")]
    pub(crate) fn new(dr: &mut D, value: &Element<'dr, D>) -> Result<Self> {
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
        let result = Self(bits);
        if N == 255 {
            // Only instantiate the width-specific checker for 255 bits.
            // Cloning the Boolean handles adds no circuit constraints.
            Bits::<D, 255>(FixedVec::from_fn(|index| result.0[index].clone()))
                .enforce_canonical(dr)?;
        }
        Ok(result)
    }

    /// The caller supplies a public maximum below 2^N. Both the value and
    /// `maximum - value` must fit N bits, preventing field wraparound.
    /// Returns the checked decomposition of `value` for arithmetic consumers.
    pub(crate) fn bounded(dr: &mut D, value: &Element<'dr, D>, maximum: u64) -> Result<Self> {
        const {
            assert!(
                N > 0 && N <= 64,
                "bounded integer width must be at most 64 bits"
            );
        }
        let value_bits = Self::new(dr, value)?;
        let maximum_element = Element::constant(dr, Fp::from(maximum));
        let slack = maximum_element.sub(dr, value);
        Self::new(dr, &slack)?;
        Ok(value_bits)
    }

    /// Compare the canonical field bits with p-1, sharing a product across each
    /// maximal zero run. Its sum has at most 254 Boolean terms and cannot wrap.
    #[expect(clippy::indexing_slicing, reason = "fixed 255-bit canonical encoding")]
    fn enforce_canonical(&self, dr: &mut D) -> Result<()> {
        const {
            assert!(
                N == 255,
                "canonical field representation must have 255 bits"
            );
        }
        let bits = &self.0;
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
}

impl<'dr, D: Driver<'dr, F = Fp>> Bits<'dr, D, 255> {
    /// Free opening advice: no header or hash binds the integer encoding of
    /// rcv.
    #[expect(clippy::indexing_slicing, reason = "native fixed field representation")]
    pub(crate) fn free(dr: &mut D, value: &DriverValue<D, Fq>) -> Result<Self> {
        FixedVec::try_from_fn(|index| {
            Boolean::alloc(
                dr,
                &mut (),
                value
                    .as_ref()
                    .map(|candidate| candidate.to_le_bits().as_ref()[index]),
            )
        })
        .map(Self)
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
