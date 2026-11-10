//! Halo2-style unsigned radix-8 fixed-base multiplication with a `+2` offset.
//!
//! Window $i$ holds little-endian bits of $k_i \in [0, 8)$. Interior windows
//! add $[(k_i + 2) 8^i]B$, and the top window adds
//! $[k_{W-1} 8^{W-1} - \sum_{i < W-1} 2 \cdot 8^i]B + C$, so the walk computes
//! $[\sum_i k_i 8^i]B + C$ for the binary value of the bits. Ragu has no
//! lookups, so halo2's Lagrange interpolation becomes a two-gate selection
//! precomputed per window (see [`Window`]).
//!
//! Every interior prefix satisfies $0 < A_j \le 9(8^j - 1)/7 < 2 \cdot 8^j
//! \le D_j$ and $A_j + D_j \le 9(8^{j+1} - 1)/7 < q$ for $j \le 83$, so no
//! interior addition meets equal or inverse operands and no prefix is the
//! identity. The top addition is complete; with all digits zero, a zero
//! correction reaches its inverse case and a correction of twice the offset
//! reaches doubling.
//!
//! What a walk proves depends on how its bits are bound:
//!
//! - [`crate::gadgets::arithmetic::Bits::free`]: some $k$, the binary value of
//!   255 free bits ($r$ or $r + q$), for a blind nothing else binds.
//! - the canonical bits of a digest $h$ (`bits::<255>`, with its comparator
//!   against $p - 1$): exactly $h$, today's native scalar.
//! - the 51 bits from `bounded`: exactly $v$. As in Orchard's short path, $v$
//!   is a magnitude and a sign; Tachyon's sign is constant per step and lives
//!   in the table's base.

use alloc::vec::Vec;

use lazy_static::lazy_static;
use ragu_core::{Result, drivers::Driver};
use ragu_primitives::{
    Boolean, Point,
    vec::{ConstLen, FixedVec},
};
use udon::{
    curve::{Affine as _, Projective as _},
    field::Field as _,
};

use super::{
    super::super::super::{
        constants::orchard::{self, ACTION_AUTH_GENERATOR},
        pasta::{Ep, EpAffine, Fp, Fq},
    },
    CompletePoint, Window, add_finite, add_incomplete, select,
};

lazy_static! {
    pub(crate) static ref R_TABLE: Table<85> = Table::new(*orchard::VALUE_COMMIT_R, Ep::identity());
    pub(crate) static ref G_TABLE: Table<85> =
        Table::new(ACTION_AUTH_GENERATOR.to_projective(), Ep::identity());
    pub(crate) static ref V_TABLE: Table<17> = Table::new(*orchard::VALUE_COMMIT_V, Ep::identity());
    pub(crate) static ref NEG_V_TABLE: Table<17> =
        Table::new(-*orchard::VALUE_COMMIT_V, Ep::identity());
}

pub(crate) struct Table<const W: usize> {
    // Native constant storage only. Circuit iteration is bounded by const W.
    low: Vec<Window>,
    top: Window,
}

impl<const W: usize> Table<W> {
    #[expect(
        clippy::expect_used,
        reason = "fixed tables must contain only finite points"
    )]
    pub(crate) fn new(base: Ep, correction: Ep) -> Self {
        assert!(!base.is_identity(), "fixed bases must be nonidentity");
        let mut power = Fq::ONE;
        let mut offset = Fq::ZERO;
        let mut low = Vec::with_capacity(W - 1);
        for _ in 1..W {
            low.push(Window::new(&[2u64, 3, 4, 5, 6, 7, 8, 9].map(|digit| {
                (base * (Fq::from(digit) * power))
                    .to_affine()
                    .coordinates()
                    .expect("every fixed low entry must be finite")
            })));
            offset += Fq::from(2) * power;
            power *= Fq::from(8);
        }
        let top = Window::new(&[0u64, 1, 2, 3, 4, 5, 6, 7].map(|digit| {
            (base * (Fq::from(digit) * power - offset) + correction)
                .to_affine()
                .coordinates()
                .expect("every fixed top entry must be finite")
        }));
        Self { low, top }
    }

    #[expect(
        clippy::indexing_slicing,
        reason = "const assertions fix the bit count; new() constructs exactly W - 1 low windows"
    )]
    pub(crate) fn walk<'dr, D: Driver<'dr, F = Fp>, const N: usize>(
        &self,
        dr: &mut D,
        bits: &FixedVec<Boolean<'dr, D>, ConstLen<N>>,
    ) -> Result<CompletePoint<'dr, D>> {
        const {
            assert!(W > 1 && W <= 85, "the offset bound covers W=2..85");
            assert!(N == 3 * W, "the bit width must match the fixed-base table");
        }
        let window = |index: usize| [&bits[3 * index], &bits[3 * index + 1], &bits[3 * index + 2]];
        let mut accumulator = select(dr, &self.low[0], window(0))?;
        for index in 1..W - 1 {
            let digit = select(dr, &self.low[index], window(index))?;
            accumulator = add_incomplete(dr, &accumulator, &digit)?;
        }
        let top = select(dr, &self.top, window(W - 1))?;
        add_finite(dr, &accumulator, &top)
    }
}

impl Table<17> {
    pub(crate) fn commitment<'dr, D: Driver<'dr, F = Fp>>(
        &self,
        dr: &mut D,
        amount: &FixedVec<Boolean<'dr, D>, ConstLen<51>>,
        blind: &FixedVec<Boolean<'dr, D>, ConstLen<255>>,
    ) -> Result<Point<'dr, D, EpAffine>> {
        let product = self.walk(dr, amount)?;
        let blind_point = R_TABLE.walk(dr, blind)?;
        let sum = super::super::add_complete(dr, &product, &blind_point)?;
        super::super::finish(dr, &sum)
    }
}

#[cfg(test)]
mod tests;
