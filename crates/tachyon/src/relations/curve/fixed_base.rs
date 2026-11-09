//! Offset radix-4 fixed-base multiplication.
//!
//! Every interior addition has distinct affine x coordinates for every Boolean
//! assignment: its positive prefix is smaller than the next offset digit, and
//! their sum is below q. The top addition is complete for finite inputs.

use alloc::vec::Vec;

use lazy_static::lazy_static;
use ragu_core::{
    Error, Result,
    drivers::{Coeff, Driver, DriverValue},
    maybe::Maybe as _,
};
use ragu_primitives::{
    Boolean, Element, Point,
    vec::{ConstLen, FixedVec},
};
use udon::{
    curve::{Affine as _, Projective as _},
    field::Field as _,
};

use super::{
    super::super::{
        keys::public::ACTION_AUTH_GENERATOR,
        pasta::{Ep, EpAffine, Fp, Fq},
        value,
    },
    CompletePoint,
};

pub(crate) struct Table<const W: usize> {
    // Native constant storage only. Circuit iteration is bounded by const W,
    // never this vector's length; table() fixes the length and finite entries.
    low: Vec<[(Fp, Fp); 4]>,
    top: [(Fp, Fp); 8],
}

lazy_static! {
    pub(crate) static ref R_TABLE: Table<126> = table(*value::VALUE_COMMIT_R, Ep::identity());
    pub(crate) static ref G_TABLE: Table<126> =
        table(ACTION_AUTH_GENERATOR.to_projective(), Ep::identity());
    pub(crate) static ref V_TABLE: Table<24> = table(*value::VALUE_COMMIT_V, Ep::identity());
    pub(crate) static ref NEG_V_TABLE: Table<24> = table(-*value::VALUE_COMMIT_V, Ep::identity());
}

#[expect(
    clippy::expect_used,
    reason = "fixed tables must contain only finite points"
)]
pub(crate) fn table<const W: usize>(base: Ep, correction: Ep) -> Table<W> {
    assert!(!base.is_identity(), "fixed bases must be nonidentity");
    let mut power = Fq::ONE;
    let mut offset = Fq::ZERO;
    let mut low = Vec::with_capacity(W);
    for _ in 0..W {
        low.push([2u64, 3, 4, 5].map(|digit| {
            (base * (Fq::from(digit) * power))
                .to_affine()
                .coordinates()
                .expect("every fixed low entry must be finite")
        }));
        offset += Fq::from(2) * power;
        power *= Fq::from(4);
    }
    let top = [0u64, 1, 2, 3, 4, 5, 6, 7].map(|digit| {
        (base * (Fq::from(digit) * power - offset) + correction)
            .to_affine()
            .coordinates()
            .expect("every fixed top entry must be finite")
    });
    Table { low, top }
}

struct Finite<'dr, D: Driver<'dr>> {
    x: Element<'dr, D>,
    y: Element<'dr, D>,
}

fn select_low<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    row: &[(Fp, Fp); 4],
    bits: [&Boolean<'dr, D>; 2],
) -> Result<Finite<'dr, D>> {
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
        x: coordinate(dr, row.map(|pair| pair.0)),
        y: coordinate(dr, row.map(|pair| pair.1)),
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

/// Interior coefficients satisfy 0 < A < b and A+b < q for W <= 126,
/// excluding both equality and inverses. The top addition is always complete.
#[expect(
    clippy::indexing_slicing,
    reason = "const assertions fix the bit count; table() constructs exactly W low windows"
)]
#[expect(
    clippy::missing_asserts_for_indexing,
    reason = "const assertions enforce N == 2 * W + 3 and W > 0"
)]
pub(crate) fn walk<'dr, D: Driver<'dr, F = Fp>, const W: usize, const N: usize>(
    dr: &mut D,
    table: &Table<W>,
    bits: &FixedVec<Boolean<'dr, D>, ConstLen<N>>,
) -> Result<CompletePoint<'dr, D>> {
    const {
        assert!(W > 0 && W <= 126, "the offset-walk theorem covers W=1..126");
        assert!(
            N == 2 * W + 3,
            "the bit width must match the fixed-base table"
        );
    }
    let mut accumulator = select_low(dr, &table.low[0], [&bits[0], &bits[1]])?;
    for window in 1..W {
        let digit = select_low(
            dr,
            &table.low[window],
            [&bits[2 * window], &bits[2 * window + 1]],
        )?;
        // Three-gate incomplete addition. The offset theorem above excludes
        // a zero denominator for every satisfying Boolean assignment.
        let numerator = digit.y.sub(dr, &accumulator.y);
        let denominator = digit.x.sub(dr, &accumulator.x);
        let (slope, square) = slope(dr, &numerator, &denominator)?;
        let x = square.sub(dr, &accumulator.x).sub(dr, &digit.x);
        let difference = accumulator.x.sub(dr, &x);
        let y = slope.mul(dr, &difference)?.sub(dr, &accumulator.y);
        accumulator = Finite { x, y };
    }

    // Shared monomials select the top three-bit digit in four gates.
    let low = bits[2 * W].element();
    let middle = bits[2 * W + 1].element();
    let high = bits[2 * W + 2].element();
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
    let coordinate = |driver: &mut D, mut coefficients: [Fp; 8]| {
        for dimension in 0..3 {
            for index in 0..8 {
                if index & (1 << dimension) != 0 {
                    coefficients[index] -= coefficients[index ^ (1 << dimension)];
                }
            }
        }
        let mut out = Element::zero(driver);
        for (element, coefficient) in monomials.iter().zip(coefficients) {
            let term = element.scale(driver, Coeff::Arbitrary(coefficient));
            out = out.add(driver, &term);
        }
        out
    };
    let top = Finite {
        x: coordinate(dr, table.top.map(|pair| pair.0)),
        y: coordinate(dr, table.top.map(|pair| pair.1)),
    };

    // Eleven-gate finite-input addition. Equal x selects the doubling slope;
    // 2y is nonzero on this odd-prime-order curve. Inverses set the identity
    // flag, whose placeholder coordinates are ignored by complete joins.
    let same_x = accumulator.x.is_equal(dr, &mut (), &top.x)?;
    let same_y = accumulator.y.is_equal(dr, &mut (), &top.y)?;
    let square = accumulator.x.square(dr)?;
    let double_numerator = square.scale(dr, Coeff::Arbitrary(Fp::from(3)));
    let add_numerator = top.y.sub(dr, &accumulator.y);
    let numerator = same_x.conditional_select(dr, &add_numerator, &double_numerator)?;
    let double_denominator = accumulator.y.double(dr);
    let add_denominator = top.x.sub(dr, &accumulator.x);
    let denominator = same_x.conditional_select(dr, &add_denominator, &double_denominator)?;
    let (slope, slope_square) = slope(dr, &numerator, &denominator)?;
    let x = slope_square.sub(dr, &accumulator.x).sub(dr, &top.x);
    let difference = accumulator.x.sub(dr, &x);
    let y = slope.mul(dr, &difference)?.sub(dr, &accumulator.y);
    let not_same_y = same_y.not(dr);
    let infinity = same_x.and(dr, &not_same_y)?;
    Ok(CompletePoint { x, y, infinity })
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

pub(crate) fn commitment<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    value_table: &Table<24>,
    amount: &FixedVec<Boolean<'dr, D>, ConstLen<51>>,
    blind: &FixedVec<Boolean<'dr, D>, ConstLen<255>>,
) -> Result<Point<'dr, D, EpAffine>> {
    let product = walk(dr, value_table, amount)?;
    let blind_point = walk(dr, &R_TABLE, blind)?;
    let sum = super::add_complete(dr, &product, &blind_point)?;
    super::finish(dr, &sum)
}

#[cfg(test)]
mod tests;
