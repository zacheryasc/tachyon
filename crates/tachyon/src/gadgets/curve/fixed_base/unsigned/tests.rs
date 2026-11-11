use alloc::format;
use core::array;

use ragu_core::maybe::Maybe as _;
use ragu_primitives::{Element, Simulator};

use super::*;
use crate::{constants::MAX_MONEY, gadgets::arithmetic};

fn check_counts(before: (usize, usize), dr: &Simulator<Fp>, expected: (usize, usize)) {
    assert_eq!(
        (dr.num_gates() - before.0, dr.num_constraints() - before.1),
        expected
    );
}

fn alloc_bits<'dr, const N: usize>(
    dr: &mut Simulator<Fp>,
    bits: [bool; N],
) -> Result<FixedVec<Boolean<'dr, Simulator<Fp>>, ConstLen<N>>> {
    FixedVec::try_from_fn(|index| {
        Boolean::alloc(dr, &mut (), Simulator::<Fp>::just(|| bits[index]))
    })
}

fn native(point: &Finite<'_, Simulator<Fp>>) -> Ep {
    EpAffine::from_xy(*point.x.value().take(), *point.y.value().take())
        .unwrap()
        .to_projective()
}

fn alloc_finite<'dr>(dr: &mut Simulator<Fp>, native: Ep) -> Result<Finite<'dr, Simulator<Fp>>> {
    let point = Point::alloc(dr, Simulator::<Fp>::just(|| native.to_affine()))?;
    let [x, y] = super::super::super::coordinates(dr, &point)?;
    Ok(Finite { x, y })
}

fn walk<const W: usize, const N: usize>(table: &Table<W>, bits: [bool; N]) -> Result<Ep> {
    let mut output = Ep::identity();
    Simulator::<Fp>::simulate((), |dr, _| {
        let allocated = alloc_bits(dr, bits)?;
        output = native(&table.walk(dr, &allocated)?);
        Ok(())
    })?;
    Ok(output)
}

fn scalar<const N: usize>(bits: [bool; N]) -> Fq {
    bits.iter().rev().fold(Fq::ZERO, |acc, bit| {
        acc.double() + Fq::from(u64::from(*bit))
    })
}

/// A walk whose result is the identity is unsatisfiable; any other result
/// matches native arithmetic.
fn check_walk<const W: usize, const N: usize>(
    table: &Table<W>,
    base: Ep,
    correction: Ep,
    bits: [bool; N],
) {
    let expected = base * scalar(bits) + correction;
    let output = walk(table, bits);
    if expected.is_identity() {
        output.expect_err("an identity walk must be unsatisfiable");
    } else {
        assert_eq!(output.unwrap(), expected);
    }
}

fn raw_bits(value: Fq) -> [bool; 255] {
    array::from_fn(|index| value.to_le_bits().as_ref()[index])
}

fn amount_bits(amount: u64) -> [bool; 51] {
    array::from_fn(|index| amount & (1 << index) != 0)
}

/// Bits whose interior prefix equals the top entry: the low digits read
/// $k_{W-1} 8^{W-1} - 4 (8^{W-1} - 1) / 7 \bmod q$.
fn doubling_bits<const N: usize>(top: u8) -> [bool; N] {
    let low_width = N - 3;
    let power = (0..low_width).fold(Fq::ONE, |power, _| power.double());
    let low = Fq::from(u64::from(top)) * power
        - Fq::from(4) * (power - Fq::ONE) * Fq::from(7).invert().unwrap();
    let low_bits = raw_bits(low);
    assert!(!low_bits[low_width..].contains(&true));
    array::from_fn(|index| {
        if index < low_width {
            low_bits[index]
        } else {
            top & (1 << (index - low_width)) != 0
        }
    })
}

/// Hand-chosen inverses for an x difference of zero violate the nonzero
/// constraint, so no assignment satisfies the checked addition.
fn assert_no_inverse(dr: &mut Simulator<Fp>, difference: &Element<'_, Simulator<Fp>>) {
    assert_eq!(*difference.value().take(), Fp::ZERO);
    for advice in [Fp::ZERO, Fp::ONE, -Fp::ONE, Fp::from(7)] {
        let error = difference
            .enforce_invertible_with(dr, Simulator::<Fp>::just(|| advice))
            .err()
            .expect("a zero difference has no inverse");
        assert!(
            format!("{error}").contains("gate check failed"),
            "unexpected error: {error}"
        );
    }
}

#[test]
fn walk_counts() {
    let wide = Table::<85>::new(*orchard::VALUE_COMMIT_R, Ep::identity());
    let short = Table::<17>::new(*orchard::VALUE_COMMIT_V, Ep::identity());
    Simulator::<Fp>::simulate((), |dr, _| {
        let bits = alloc_bits(dr, raw_bits(Fq::ONE))?;
        let mut before = (dr.num_gates(), dr.num_constraints());
        let blind = wide.walk(dr, &bits)?;
        check_counts(before, dr, (423, 846));
        let amount = alloc_bits(dr, [true; 51])?;
        before = (dr.num_gates(), dr.num_constraints());
        short.walk_onto(dr, &amount, &blind)?;
        check_counts(before, dr, (87, 174));
        Ok(())
    })
    .unwrap();
}

#[test]
fn walks_match_native() {
    let half = Fq::from(2).invert().unwrap();
    let mut cases = Vec::from([
        raw_bits(Fq::ZERO),
        raw_bits(Fq::ONE),
        raw_bits(-Fq::ONE),
        raw_bits(half),
        raw_bits(Fq::from_bytes((-Fp::ONE).to_bytes()).unwrap()),
        raw_bits(Fq::from(2).pow_u64(254)),
        [true; 255],
    ]);
    for bit in 0..255 {
        cases.push(array::from_fn(|index| index == bit));
    }
    let digits: Vec<[bool; 3]> = (0..8u8)
        .map(|digit| [0, 1, 2].map(|position| digit & (1 << position) != 0))
        .collect();
    for window in &digits {
        cases.push([*window; 85].as_flattened().try_into().unwrap());
    }
    for (base, correction) in [
        (*orchard::VALUE_COMMIT_R, Ep::identity()),
        (*ACTION_AUTH_GENERATOR, Ep::identity()),
    ] {
        let wide = Table::<85>::new(base, correction);
        for bits in &cases {
            check_walk(&wide, base, correction, *bits);
        }
    }
    let value_base = *orchard::VALUE_COMMIT_V;
    for (base, correction) in [
        (value_base, Ep::identity()),
        (-value_base, Ep::identity()),
        (value_base, -value_base * Fq::from(MAX_MONEY)),
    ] {
        let short = Table::<17>::new(base, correction);
        let amounts = [0u64, 1, 2, 3, MAX_MONEY].map(amount_bits);
        let repeated = digits
            .iter()
            .map(|window| <[bool; 51]>::try_from([*window; 17].as_flattened()).unwrap());
        for bits in amounts.into_iter().chain(repeated) {
            check_walk(&short, base, correction, bits);
        }
    }
}

#[test]
fn top_addition_rejects_inverse_and_doubling() {
    // With all digits zero the prefix is [2]B and the top is [-2]B + C:
    // C=0 makes inverses, C=[4]B equal points, C=[5]B a generic sum.
    let base = EpAffine::generator().to_projective();
    for coefficient in [0u64, 4] {
        let table = Table::<2>::new(base, base * Fq::from(coefficient));
        walk(&table, [false; 6]).expect_err("inverse and equal top operands must be unsatisfiable");
    }
    let correction = base * Fq::from(5);
    check_walk(
        &Table::<2>::new(base, correction),
        base,
        correction,
        [false; 6],
    );

    for top in [1, 5] {
        let bits = doubling_bits::<255>(top);
        walk(&R_TABLE, bits).expect_err("a doubling blind must be unsatisfiable");
        walk(&G_TABLE, bits).expect_err("a doubling randomizer must be unsatisfiable");
    }
    walk(&V_TABLE, doubling_bits::<51>(1))
        .expect_err("a doubling value walk must be unsatisfiable");
    walk(&NEG_V_TABLE, doubling_bits::<51>(1))
        .expect_err("a doubling value walk must be unsatisfiable");
}

#[test]
fn zero_and_doubling_blinds_have_no_satisfying_inverse() {
    let doubling = doubling_bits::<255>(1);
    assert!(scalar(doubling) != Fq::ZERO);
    for bits in [raw_bits(Fq::ZERO), doubling] {
        Simulator::<Fp>::simulate((), |dr, _| {
            let allocated = alloc_bits(dr, bits)?;
            let (prefix, top) = R_TABLE.prefix_and_top(dr, &allocated)?;
            let difference = top.x.sub(dr, &prefix.x);
            assert_no_inverse(dr, &difference);
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn joins_onto_a_prefix_point_have_no_satisfying_inverse() {
    // With v = 0 the prefix is [2(8^16 - 1)/7]V, so a start of ± that point
    // meets the first join at equal x.
    let prefix_scalar =
        Fq::from(2) * (Fq::from(8).pow_u64(16) - Fq::ONE) * Fq::from(7).invert().unwrap();
    for sign in [Fq::ONE, -Fq::ONE] {
        let start_point = *orchard::VALUE_COMMIT_V * (prefix_scalar * sign);
        Simulator::<Fp>::simulate((), |dr, _| {
            let allocated = alloc_bits(dr, amount_bits(0))?;
            let start = alloc_finite(dr, start_point)?;
            let (prefix, _) = V_TABLE.prefix_and_top(dr, &allocated)?;
            let difference = start.x.sub(dr, &prefix.x);
            assert_no_inverse(dr, &difference);
            Ok(())
        })
        .unwrap();
        let rejected = Simulator::<Fp>::simulate((), |dr, _| {
            let allocated = alloc_bits(dr, amount_bits(0))?;
            let start = alloc_finite(dr, start_point)?;
            V_TABLE.walk_onto(dr, &allocated, &start)?;
            Ok(())
        });
        rejected
            .err()
            .expect("a join at equal x must be unsatisfiable");
    }
}

#[test]
fn commitments_match_native() {
    let value_base = *orchard::VALUE_COMMIT_V;
    let blind_base = *orchard::VALUE_COMMIT_R;
    for (amount, blind) in [
        (0u64, Fq::ONE),
        (1, -Fq::ONE),
        (2, Fq::from(3)),
        (MAX_MONEY, Fq::from(2).pow_u64(254)),
    ] {
        let expected = -value_base * Fq::from(amount) + blind_base * blind;
        Simulator::<Fp>::simulate((amount, blind), |dr, witness| {
            let element =
                Element::alloc(dr, &mut (), witness.as_ref().map(|pair| Fp::from(pair.0)))?;
            let amount_bits = arithmetic::Bits::<_, 51>::bounded(dr, &element, MAX_MONEY)?;
            let bits = arithmetic::Bits::<_, 255>::free(dr, &witness.as_ref().map(|pair| pair.1))?;
            let point = NEG_V_TABLE.commitment(dr, &amount_bits, &bits)?;
            assert_eq!(point.value().take().to_projective(), expected);
            Ok(())
        })
        .unwrap();
    }
    for amount in [0u64, 1] {
        let rejected = Simulator::<Fp>::simulate(Fq::ZERO, |dr, witness| {
            let element = Element::constant(dr, Fp::from(amount));
            let amount_bits = arithmetic::Bits::<_, 51>::bounded(dr, &element, MAX_MONEY)?;
            let bits = arithmetic::Bits::<_, 255>::free(dr, &witness)?;
            NEG_V_TABLE.commitment(dr, &amount_bits, &bits)?;
            Ok(())
        });
        rejected.err().expect("rcv = 0 must be unsatisfiable");
    }
}

#[test]
fn zero_maximum_fee_commitment_is_the_blind_point() {
    let value_base = *orchard::VALUE_COMMIT_V;
    let fee_table = Table::<17>::new(value_base, -value_base * Fq::from(MAX_MONEY));
    let blind = Fq::from(11);
    for maximum in [0u64, 1, MAX_MONEY] {
        let expected = *orchard::VALUE_COMMIT_R * blind - value_base * Fq::from(maximum);
        Simulator::<Fp>::simulate((), |dr, _| {
            let blind_bits = alloc_bits(dr, raw_bits(blind))?;
            let slack_bits = alloc_bits(dr, amount_bits(MAX_MONEY - maximum))?;
            let blind_point = R_TABLE.walk(dr, &blind_bits)?;
            let cv = fee_table.walk_onto(dr, &slack_bits, &blind_point)?;
            assert_eq!(native(&cv), expected);
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn digest_walks_match_native() {
    let generator = *ACTION_AUTH_GENERATOR;
    for digest in [Fp::ZERO, Fp::ONE, -Fp::ONE, Fp::from(2).pow_u64(254)] {
        let expected = generator * Fq::from_bytes(digest.to_bytes()).unwrap();
        let output = Simulator::<Fp>::simulate(digest, |dr, witness| {
            let element = Element::alloc(dr, &mut (), witness)?;
            let bits = arithmetic::Bits::<_, 255>::new(dr, &element)?;
            let output = G_TABLE.walk(dr, &bits)?;
            assert_eq!(native(&output), expected);
            Ok(())
        });
        assert_eq!(output.is_ok(), !expected.is_identity());
    }
}
