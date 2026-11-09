//! Signed odd-digit radix-8 fixed-base multiplication.
//!
//! Window i reads bits (s, m, n) as (2s - 1)(1 + 2m + 4n), using
//! [`crate::radix8::DIGITS`]. A W-window walk computes `[k]B + C` for
//! k = Σ d_i 8^i. Every prefix A_j is odd and satisfies
//! |A_j| <= 8^j - 1 < |d_j|8^j and |A_j| + |d_j|8^j < 8^(j+1).
//! For j + 1 <= 84 this is below q, so interior operands have distinct x
//! coordinates and every prefix is finite. The last addition is complete,
//! including the inverse and doubling cases at W = 85.
//!
//! Free blind bits bind some scalar opening. Hash-derived scalars keep the
//! canonical 255-bit comparator: h + p recomposes to h but reads differently
//! under [`crate::radix8::fp_to_fq`]. Amount digits bind 2v + 1 with a pinned
//! top digit +1; the walk over `[1/2]B` subtracts `[1/2]B` to compute `[v]B`.

use alloc::vec::Vec;
use core::array;

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

use super::{super::arithmetic, CompletePoint};
use crate::{
    pasta::{Ep, EpAffine, Fp, Fq},
    radix8::DIGITS,
};

pub(crate) struct Table<const W: usize> {
    // Native constant storage only. Circuit iteration is bounded by const W.
    rows: Vec<[(Fp, Fp); 4]>,
    correction: Option<(Fp, Fp)>,
}

/// Rows hold the positive digits from [`DIGITS`] times [8^i]B.
/// A corrected walk uses W <= 84 and joins its finite correction completely.
#[expect(
    clippy::expect_used,
    reason = "fixed table entries and corrections must be finite"
)]
pub(crate) fn table<const W: usize>(base: Ep, correction: Option<Ep>) -> Table<W> {
    const {
        assert!(W > 1 && W <= 85, "the signed-walk bound covers W=2..85");
    }
    assert!(!base.is_identity(), "fixed bases must be nonidentity");
    assert!(
        W <= 84 || correction.is_none(),
        "corrected walks keep digit additions incomplete"
    );
    let mut power = Fq::ONE;
    let mut rows = Vec::with_capacity(W);
    let [_, one, _, three, _, five, _, seven] = DIGITS;
    for _ in 0..W {
        rows.push([one, three, five, seven].map(|digit| {
            let magnitude = u64::from(digit.unsigned_abs());
            (base * (Fq::from(magnitude) * power))
                .to_affine()
                .coordinates()
                .expect("fixed signed entries must be finite")
        }));
        power *= Fq::from(8);
    }
    let correction_coordinates = correction.map(|point| {
        point
            .to_affine()
            .coordinates()
            .expect("fixed corrections must be finite")
    });
    Table {
        rows,
        correction: correction_coordinates,
    }
}

/// Walks 2v + 1 over `[1/2]B`, then subtracts `[1/2]B` and adds `correction`.
/// The fixed top +1 contributes `[8^17/2]B` to the final correction.
#[expect(clippy::expect_used, reason = "two is invertible in Fq")]
pub(crate) fn amount_table(base: Ep, correction: Ep) -> Table<17> {
    let half = base * Fq::from(2).invert().expect("two is invertible");
    let offset = half * (Fq::from(8).pow_u64(17) - Fq::ONE);
    table(half, Some(offset + correction))
}

struct Finite<'dr, D: Driver<'dr>> {
    x: Element<'dr, D>,
    y: Element<'dr, D>,
}

/// Two gates share m*n between both coordinates and apply the sign to y.
fn select<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    row: &[(Fp, Fp); 4],
    bits: [&Boolean<'dr, D>; 3],
) -> Result<Finite<'dr, D>> {
    let [sign, low, high] = bits;
    let product = low.element().mul(dr, &high.element())?;
    let bilinear = |driver: &mut D, values: [Fp; 4]| {
        let mut out = Element::constant(driver, values[0]);
        for (element, coefficient) in [
            (low.element(), values[1] - values[0]),
            (high.element(), values[2] - values[0]),
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
    let x = bilinear(dr, row.map(|pair| pair.0));
    let unsigned_y = bilinear(dr, row.map(|pair| pair.1));
    let signum = sign
        .element()
        .scale(dr, Coeff::Arbitrary(Fp::from(2)))
        .sub(dr, &Element::one());
    let y = signum.mul(dr, &unsigned_y)?;
    Ok(Finite { x, y })
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

/// Computes the signed sum with incomplete interior additions: the prefix
/// bound excludes equal and inverse operands. The final finite-input join is
/// complete. Digest bits require a canonical decomposition; blind bits are
/// free.
#[expect(
    clippy::indexing_slicing,
    reason = "const assertions fix N = 3 * W; table constructs W rows"
)]
pub(crate) fn walk<'dr, D: Driver<'dr, F = Fp>, const W: usize, const N: usize>(
    dr: &mut D,
    table: &Table<W>,
    bits: &FixedVec<Boolean<'dr, D>, ConstLen<N>>,
) -> Result<CompletePoint<'dr, D>> {
    const {
        assert!(W > 1 && W <= 85, "the signed-walk bound covers W=2..85");
        assert!(N == 3 * W, "the bit width must match the fixed-base table");
    }
    let window = |driver: &mut D, index: usize| {
        select(
            driver,
            &table.rows[index],
            [&bits[3 * index], &bits[3 * index + 1], &bits[3 * index + 2]],
        )
    };
    let mut accumulator = window(dr, 0)?;
    let incomplete = if table.correction.is_some() { W } else { W - 1 };
    for index in 1..incomplete {
        let digit = window(dr, index)?;
        // Three gates; the signed-prefix bound excludes a zero denominator.
        let numerator = digit.y.sub(dr, &accumulator.y);
        let denominator = digit.x.sub(dr, &accumulator.x);
        let (slope, square) = slope(dr, &numerator, &denominator)?;
        let x = square.sub(dr, &accumulator.x).sub(dr, &digit.x);
        let difference = accumulator.x.sub(dr, &x);
        let y = slope.mul(dr, &difference)?.sub(dr, &accumulator.y);
        accumulator = Finite { x, y };
    }
    let last = match table.correction {
        Some((x, y)) => Finite {
            x: Element::constant(dr, x),
            y: Element::constant(dr, y),
        },
        None => window(dr, W - 1)?,
    };
    // Eleven-gate finite-input addition. Equal x selects the doubling slope;
    // 2y is nonzero on this odd-prime-order curve. Inverses set the identity
    // flag, whose placeholder coordinates are ignored by complete joins.
    let same_x = accumulator.x.is_equal(dr, &mut (), &last.x)?;
    let same_y = accumulator.y.is_equal(dr, &mut (), &last.y)?;
    let square = accumulator.x.square(dr)?;
    let double_numerator = square.scale(dr, Coeff::Arbitrary(Fp::from(3)));
    let add_numerator = last.y.sub(dr, &accumulator.y);
    let numerator = same_x.conditional_select(dr, &add_numerator, &double_numerator)?;
    let double_denominator = accumulator.y.double(dr);
    let add_denominator = last.x.sub(dr, &accumulator.x);
    let denominator = same_x.conditional_select(dr, &add_denominator, &double_denominator)?;
    let (slope, slope_square) = slope(dr, &numerator, &denominator)?;
    let x = slope_square.sub(dr, &accumulator.x).sub(dr, &last.x);
    let difference = accumulator.x.sub(dr, &x);
    let y = slope.mul(dr, &difference)?.sub(dr, &accumulator.y);
    let not_same_y = same_y.not(dr);
    let infinity = same_x.and(dr, &not_same_y)?;
    Ok(CompletePoint { x, y, infinity })
}

/// Recodes unsigned windows t as signed windows summing to 2t - (8^W - 1).
fn recode<const N: usize>(offset: [bool; N]) -> [bool; N] {
    const {
        assert!(N.is_multiple_of(3), "signed windows have three bits");
    }
    let mut windows = [false; N];
    for (
        &[low, middle, high],
        &mut [ref mut sign, ref mut magnitude_low, ref mut magnitude_high],
    ) in offset
        .as_chunks::<3>()
        .0
        .iter()
        .zip(windows.as_chunks_mut::<3>().0.iter_mut())
    {
        *sign = high;
        *magnitude_low = low == high;
        *magnitude_high = middle == high;
    }
    windows
}

/// Encodes the odd representative K in {r, r-q} via t = (K + 2^255 - 1)/2.
/// Odd r gives floor(r/2) + 2^254; even r gives (r-1)/2 + 2^254 mod q,
/// whose canonical reduction is the required t below q.
#[expect(
    clippy::expect_used,
    clippy::indexing_slicing,
    reason = "two is invertible; Fq has a 256-bit representation"
)]
fn encode(scalar: Fq) -> [bool; 255] {
    let bits = scalar.to_le_bits();
    let offset = if bits.as_ref()[0] {
        array::from_fn(|index| index == 254 || bits.as_ref()[index + 1])
    } else {
        let half = Fq::from(2).invert().expect("two is invertible");
        let even = (scalar - Fq::ONE) * half + Fq::from(2).pow_u64(254);
        let even_bits = even.to_le_bits();
        array::from_fn(|index| even_bits.as_ref()[index])
    };
    recode(offset)
}

/// Free opening advice for a blind whose integer encoding is otherwise unbound.
#[expect(clippy::indexing_slicing, reason = "encode returns 255 bits")]
pub(crate) fn free_bits<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    value: &DriverValue<D, Fq>,
) -> Result<FixedVec<Boolean<'dr, D>, ConstLen<255>>> {
    let encoded = value.as_ref().map(|candidate| encode(*candidate));
    FixedVec::try_from_fn(|index| {
        Boolean::alloc(dr, &mut (), encoded.as_ref().map(|windows| windows[index]))
    })
}

/// Pins 2v + 1 = 8^17 + Σ d_i 8^i using 17 signed windows.
/// The pinned top +1 bounds the sum to [1, 2^52), so recomposition pins v
/// to [0, 2^51) in Fp. Its windows recode v's own unsigned bits.
#[expect(clippy::indexing_slicing, reason = "51 bits form exactly 17 windows")]
pub(crate) fn amount_digits<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    value: &Element<'dr, D>,
) -> Result<FixedVec<Boolean<'dr, D>, ConstLen<51>>> {
    let windows = value.value().map(|candidate| {
        let bits = candidate.to_le_bits();
        recode::<51>(array::from_fn(|index| bits.as_ref()[index]))
    });
    let bits = FixedVec::<_, ConstLen<51>>::try_from_fn(|index| {
        Boolean::alloc(dr, &mut (), windows.as_ref().map(|all| all[index]))
    })?;
    let mut sum = Element::constant(dr, Fp::from(8).pow_u64(17));
    let mut power = Fp::ONE;
    for window in 0..17 {
        let low = bits[3 * window + 1]
            .element()
            .scale(dr, Coeff::Arbitrary(Fp::from(2)));
        let high = bits[3 * window + 2]
            .element()
            .scale(dr, Coeff::Arbitrary(Fp::from(4)));
        let magnitude = Element::one().add(dr, &low).add(dr, &high);
        let positive = bits[3 * window].element().mul(dr, &magnitude)?;
        let digit = positive.double(dr).sub(dr, &magnitude);
        let term = digit.scale(dr, Coeff::Arbitrary(power));
        sum = sum.add(dr, &term);
        power *= Fp::from(8);
    }
    let odd = value.double(dr).add(dr, &Element::one());
    sum.enforce_equal(dr, &odd)?;
    Ok(bits)
}

/// Pins value and its 51-bit slack below the caller's public maximum < 2^51.
pub(crate) fn bounded_amount<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    value: &Element<'dr, D>,
    maximum: u64,
) -> Result<FixedVec<Boolean<'dr, D>, ConstLen<51>>> {
    let digits = amount_digits(dr, value)?;
    let maximum_element = Element::constant(dr, Fp::from(maximum));
    let slack = maximum_element.sub(dr, value);
    arithmetic::bits::<D, 51>(dr, &slack)?;
    Ok(digits)
}

pub(crate) fn commitment<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    value_table: &Table<17>,
    blind_table: &Table<85>,
    amount: &FixedVec<Boolean<'dr, D>, ConstLen<51>>,
    blind: &FixedVec<Boolean<'dr, D>, ConstLen<255>>,
) -> Result<Point<'dr, D, EpAffine>> {
    let product = walk(dr, value_table, amount)?;
    let blind_point = walk(dr, blind_table, blind)?;
    let sum = super::add_complete(dr, &product, &blind_point)?;
    super::finish(dr, &sum)
}

#[cfg(test)]
mod tests;
