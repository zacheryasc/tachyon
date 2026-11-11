//! Fixed-base multiplication: shared affine adders for the [`unsigned`]
//! walks.
//!
//! The incomplete adder pins its slope only when the operands have distinct
//! x coordinates; at equal x any slope satisfies it. It is sound only where
//! integer bounds prove distinct x for every Boolean assignment. The checked
//! adder constrains distinct x instead.

use core::array;

use ragu_core::{
    Error, Result,
    drivers::{Coeff, Driver},
    maybe::Maybe as _,
};
use ragu_primitives::{Boolean, Element};
use udon::field::Field as _;

use super::{super::super::pasta::Fp, Finite};

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

/// Three-gate incomplete addition. Caller proves distinct x coordinates.
fn add_incomplete<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    accumulator: &Finite<'dr, D>,
    digit: &Finite<'dr, D>,
) -> Result<Finite<'dr, D>> {
    let numerator = digit.y.sub(dr, &accumulator.y);
    let denominator = digit.x.sub(dr, &accumulator.x);
    let (slope, square) = slope(dr, &numerator, &denominator)?;
    let x = square.sub(dr, &accumulator.x).sub(dr, &digit.x);
    let difference = accumulator.x.sub(dr, &x);
    let y = slope.mul(dr, &difference)?.sub(dr, &accumulator.y);
    Ok(Finite { x, y })
}

/// Four-gate addition that constrains distinct x coordinates. Equal x means
/// equal or inverse operands, so every satisfying assignment adds distinct
/// finite points.
fn add_checked<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    accumulator: &Finite<'dr, D>,
    operand: &Finite<'dr, D>,
) -> Result<Finite<'dr, D>> {
    operand.x.sub(dr, &accumulator.x).enforce_nonzero(dr)?;
    add_incomplete(dr, accumulator, operand)
}

/// Multilinear coefficients of a function on $\{0, 1\}^3$, indexed by the bit
/// mask of each monomial.
#[expect(
    clippy::indexing_slicing,
    reason = "the Möbius transform indexes a fixed eight-entry array"
)]
fn monomials(mut values: [Fp; 8]) -> [Fp; 8] {
    for dimension in 0..3 {
        for index in 0..8 {
            if index & (1 << dimension) != 0 {
                values[index] -= values[index ^ (1 << dimension)];
            }
        }
    }
    values
}

/// Two-gate selection of one of eight fixed points by three little-endian
/// bits $b_0, b_1, b_2$.
///
/// $q = x_{012} y - y_{012} x$ has no $b_0 b_1 b_2$ term, where $x_S, y_S$ are
/// the coordinates' multilinear coefficients. The first gate realizes $q$'s
/// quadratic part as $p = (b_0 + \beta b_2)(q_{01} b_1 + q_{02} b_2)$; the
/// second is $c = b_2 (\lambda_0 b_0 + \lambda_1 b_1 + \rho p)$, which matches
/// $x$'s cubic and $b_0 b_2, b_1 b_2$ terms up to multiples of $q$. Both
/// coordinates are then affine in $(b_0, b_1, b_2, p, c)$. Construction checks
/// all eight entries, so selection is exact on every Boolean assignment.
pub(super) struct Window {
    left: [Fp; 3],
    right: [Fp; 3],
    inner: [Fp; 3],
    x: [Fp; 6],
    y: [Fp; 6],
}

impl Window {
    #[expect(
        clippy::indexing_slicing,
        reason = "fixed eight-entry cube and six-term basis"
    )]
    #[expect(
        clippy::expect_used,
        reason = "fixed tables must admit two-gate selection"
    )]
    pub(super) fn new(entries: &[(Fp, Fp); 8]) -> Self {
        let x = monomials(entries.map(|entry| entry.0));
        let y = monomials(entries.map(|entry| entry.1));
        let [q01, q02, q12] = [3, 5, 6].map(|mask| x[7] * y[mask] - y[7] * x[mask]);
        let inverse = q01
            .invert()
            .expect("q must have a b0 b1 term in a fixed window");
        let shift = x[3] * inverse;
        let rho = x[7] * inverse;
        let left = [Fp::ONE, Fp::ZERO, q12 * inverse];
        let right = [Fp::ZERO, q01, q02];
        let inner = [x[5] - (shift + rho) * q02, x[6] - (shift + rho) * q12, rho];

        let bit = |index: usize, position: usize| Fp::from(u64::from(index & (1 << position) != 0));
        let linear = |coefficients: &[Fp; 3], terms: [Fp; 3]| {
            coefficients
                .iter()
                .zip(terms)
                .fold(Fp::ZERO, |sum, (coefficient, term)| {
                    sum + *coefficient * term
                })
        };
        let basis: [[Fp; 6]; 8] = array::from_fn(|index| {
            let bits = [bit(index, 0), bit(index, 1), bit(index, 2)];
            let quadratic = linear(&left, bits) * linear(&right, bits);
            let cubic = bits[2] * linear(&inner, [bits[0], bits[1], quadratic]);
            [Fp::ONE, bits[0], bits[1], bits[2], quadratic, cubic]
        });
        let quadratic = monomials(basis.map(|row| row[4]));
        let cubic = monomials(basis.map(|row| row[5]));
        let cubic_inverse = cubic[7]
            .invert()
            .expect("x must have a b0 b1 b2 term in a fixed window");
        let quadratic_inverse = quadratic[3]
            .invert()
            .expect("p must have a b0 b1 term in a fixed window");
        let solve = |coordinate: [Fp; 8]| {
            let gamma = coordinate[7] * cubic_inverse;
            let alpha = (coordinate[3] - gamma * cubic[3]) * quadratic_inverse;
            let rest =
                |mask: usize| coordinate[mask] - alpha * quadratic[mask] - gamma * cubic[mask];
            [rest(0), rest(1), rest(2), rest(4), alpha, gamma]
        };
        let window = Self {
            left,
            right,
            inner,
            x: solve(x),
            y: solve(y),
        };
        for (row, entry) in basis.iter().zip(*entries) {
            let evaluate = |coefficients: &[Fp; 6]| {
                coefficients
                    .iter()
                    .zip(row)
                    .fold(Fp::ZERO, |sum, (coefficient, term)| {
                        sum + *coefficient * *term
                    })
            };
            assert_eq!(
                (evaluate(&window.x), evaluate(&window.y)),
                entry,
                "two-gate selection must reproduce every fixed entry"
            );
        }
        window
    }
}

fn combine<'dr, D: Driver<'dr, F = Fp>, const N: usize>(
    dr: &mut D,
    coefficients: &[Fp; N],
    elements: [&Element<'dr, D>; N],
) -> Element<'dr, D> {
    let mut sum = Element::zero(dr);
    for (element, coefficient) in elements.into_iter().zip(coefficients) {
        sum = sum.add_coeff(dr, element, Coeff::Arbitrary(*coefficient));
    }
    sum
}

/// Selects a window's entry in two gates. Caller supplies Boolean bits.
fn select<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    window: &Window,
    bits: [&Boolean<'dr, D>; 3],
) -> Result<Finite<'dr, D>> {
    let [low, middle, high] = bits.map(Boolean::element);
    let left = combine(dr, &window.left, [&low, &middle, &high]);
    let right = combine(dr, &window.right, [&low, &middle, &high]);
    let quadratic = left.mul(dr, &right)?;
    let inner = combine(dr, &window.inner, [&low, &middle, &quadratic]);
    let cubic = high.mul(dr, &inner)?;
    let one = Element::one();
    let basis = [&one, &low, &middle, &high, &quadratic, &cubic];
    Ok(Finite {
        x: combine(dr, &window.x, basis),
        y: combine(dr, &window.y, basis),
    })
}

pub(crate) mod unsigned;
