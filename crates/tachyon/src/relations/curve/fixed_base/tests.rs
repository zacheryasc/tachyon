use core::array;

use ragu_primitives::Simulator;

use super::{super::super::arithmetic, *};
use crate::constants::MAX_MONEY;

fn check_counts(before: (usize, usize), dr: &Simulator<Fp>, expected: (usize, usize)) {
    assert_eq!(
        (dr.num_gates() - before.0, dr.num_constraints() - before.1),
        expected
    );
}

#[test]
fn walk_counts() {
    Simulator::<Fp>::simulate((), |dr, _| {
        let value = Element::constant(dr, Fp::from(17));
        let bits = arithmetic::bits::<_, 255>(dr, &value)?;
        let mut before = (dr.num_gates(), dr.num_constraints());
        walk(dr, &R_TABLE, &bits)?;
        check_counts(before, dr, (516, 1032));
        let amount = arithmetic::bounded::<_, 51>(dr, &value, MAX_MONEY)?;
        before = (dr.num_gates(), dr.num_constraints());
        walk(dr, &V_TABLE, &amount)?;
        check_counts(before, dr, (108, 216));

        // W=1 has one low selector, one top selector and the finite adder.
        // W=2 adds exactly one low selector and one incomplete interior add.
        let short = table::<1>(*value::VALUE_COMMIT_R, Ep::identity());
        let zero = Element::zero(dr);
        let short_bits = arithmetic::bits::<_, 5>(dr, &zero)?;
        before = (dr.num_gates(), dr.num_constraints());
        walk(dr, &short, &short_bits)?;
        check_counts(before, dr, (16, 32));
        let longer = table::<2>(*value::VALUE_COMMIT_R, Ep::identity());
        let longer_bits = arithmetic::bits::<_, 7>(dr, &zero)?;
        before = (dr.num_gates(), dr.num_constraints());
        walk(dr, &longer, &longer_bits)?;
        check_counts(before, dr, (20, 40));
        Ok(())
    })
    .unwrap();
}

fn raw_bits(value: Fq) -> [bool; 255] {
    array::from_fn(|index| value.to_le_bits().as_ref()[index])
}

fn check_walk<const W: usize, const N: usize>(
    table: &Table<W>,
    base: Ep,
    correction: Ep,
    bits: [bool; N],
) {
    let scalar = bits.iter().rev().fold(Fq::ZERO, |acc, bit| {
        acc.double() + Fq::from(u64::from(*bit))
    });
    let expected = base * scalar + correction;
    Simulator::<Fp>::simulate(bits, |dr, witness| {
        let allocated = FixedVec::<_, ConstLen<N>>::try_from_fn(|index| {
            Boolean::alloc(
                dr,
                &mut (),
                witness.as_ref().map(|assignment| assignment[index]),
            )
        })?;
        let output = walk(dr, table, &allocated)?;
        let actual = if output.infinity.value().take() {
            Ep::identity()
        } else {
            EpAffine::from_xy(*output.x.value().take(), *output.y.value().take())
                .unwrap()
                .to_projective()
        };
        assert_eq!(actual, expected);
        Ok(())
    })
    .unwrap();
}

#[expect(
    clippy::missing_asserts_for_indexing,
    reason = "the low selector input has ConstLen<2>"
)]
fn check_table<const W: usize>(table: &Table<W>, base: Ep, correction: Ep) {
    let mut power = Fq::ONE;
    let mut offset = Fq::ZERO;
    for row in &table.low {
        for (digit, coordinates) in [2u64, 3, 4, 5].into_iter().zip(row) {
            let point = base * (Fq::from(digit) * power);
            assert_eq!(*coordinates, point.to_affine().coordinates().unwrap());
            Simulator::<Fp>::simulate((), |dr, _| {
                let bits = FixedVec::<_, ConstLen<2>>::try_from_fn(|index| {
                    Boolean::alloc(
                        dr,
                        &mut (),
                        Simulator::<Fp>::just(|| (digit - 2) & (1 << index) != 0),
                    )
                })?;
                let before = (dr.num_gates(), dr.num_constraints());
                let selected = select_low(dr, row, [&bits[0], &bits[1]])?;
                check_counts(before, dr, (1, 2));
                assert_eq!(
                    (*selected.x.value().take(), *selected.y.value().take()),
                    *coordinates
                );
                Ok(())
            })
            .unwrap();
        }
        offset += Fq::from(2) * power;
        power *= Fq::from(4);
    }
    // Exercise each real top entry through the complete top boundary of a
    // one-window walk, with its low digit fixed to the first finite entry.
    let first = *table.low.first().unwrap();
    let prefix = EpAffine::from_xy(first[0].0, first[0].1)
        .unwrap()
        .to_projective();
    let boundary = Table::<1> {
        low: alloc::vec![first],
        top: table.top,
    };
    for (digit, coordinates) in (0u64..8).zip(table.top) {
        let point = base * (Fq::from(digit) * power - offset) + correction;
        assert_eq!(coordinates, point.to_affine().coordinates().unwrap());
        let bits = [false, false, digit & 1 != 0, digit & 2 != 0, digit & 4 != 0];
        // The test boundary's top is copied from the full table, so its
        // expected correction is the difference from a normal W=1 walk.
        let expected_correction = prefix + point - base * Fq::from(4 * digit);
        check_walk(&boundary, base, expected_correction, bits);
    }
}

#[test]
fn tables_and_walks() {
    let power = Fq::from(4).pow_u64(126);
    let third = Fq::from(3).invert().unwrap();
    let deep_dive = -Fq::from(2) * (Fq::from(4).pow_u64(127) - Fq::ONE) * third;
    let doubles = (Fq::from(2) * power + Fq::from(4)) * third + Fq::from(2) * power;
    let mut modulus = raw_bits(-Fq::ONE);
    for bit in &mut modulus {
        *bit = !*bit;
        if *bit {
            break;
        }
    }
    let low = raw_bits(Fq::from(12) * power - Fq::from(4) * (power - Fq::ONE) * third);
    let mut carry = false;
    let noncanonical = array::from_fn(|index| {
        let sum = u8::from(low[index]) + u8::from(modulus[index]) + u8::from(carry);
        carry = sum >= 2;
        sum & 1 == 1
    });
    assert!(!carry);
    let p_minus_one = Fq::from_bytes((-Fp::ONE).to_bytes()).unwrap();
    let mut cases = Vec::from([
        raw_bits(Fq::ZERO),
        raw_bits(Fq::ONE),
        raw_bits(p_minus_one),
        raw_bits(-Fq::ONE),
        raw_bits(Fq::from(2).pow_u64(254)),
        raw_bits(deep_dive),
        raw_bits(doubles),
        [true; 255],
        modulus,
        noncanonical,
    ]);
    for bit in 0..255 {
        let mut bits = [false; 255];
        bits[bit] = true;
        cases.push(bits);
    }
    for (table, base) in [
        (&*R_TABLE, *value::VALUE_COMMIT_R),
        (&*G_TABLE, ACTION_AUTH_GENERATOR.to_projective()),
    ] {
        check_table(table, base, Ep::identity());
        for bits in &cases {
            check_walk(table, base, Ep::identity(), *bits);
        }
    }
    let fee_correction = -*value::VALUE_COMMIT_V * Fq::from(MAX_MONEY);
    let corrected = table::<24>(*value::VALUE_COMMIT_V, fee_correction);
    for (table, base, correction) in [
        (&*V_TABLE, *value::VALUE_COMMIT_V, Ep::identity()),
        (&*NEG_V_TABLE, -*value::VALUE_COMMIT_V, Ep::identity()),
        (&corrected, *value::VALUE_COMMIT_V, fee_correction),
    ] {
        check_table(table, base, correction);
        for amount in [0u64, 1, MAX_MONEY, (1 << 51) - 1] {
            let bits: [bool; 51] = array::from_fn(|index| amount & (1 << index) != 0);
            check_walk(table, base, correction, bits);
        }
    }
}

#[test]
fn finite_addition_exceptions_at_top_boundary() {
    let base = EpAffine::generator().to_projective();
    // With all digits zero, the prefix is [2]B and the top is [-2]B + C.
    // C=0 makes inverses, C=[4]B makes equal points, C=[5]B is generic.
    for coefficient in [0u64, 4, 5] {
        let correction = base * Fq::from(coefficient);
        let boundary = table::<1>(base, correction);
        Simulator::<Fp>::simulate((), |dr, _| {
            let zero = Element::zero(dr);
            let bits = arithmetic::bits::<_, 5>(dr, &zero)?;
            let before = (dr.num_gates(), dr.num_constraints());
            let output = walk(dr, &boundary, &bits)?;
            check_counts(before, dr, (16, 32));
            assert_eq!(output.infinity.value().take(), coefficient == 0);
            let point = Point::constant(dr, base.to_affine())?;
            let third = super::super::from_point(dr, &point)?;
            let sum = super::super::add_complete(dr, &output, &third)?;
            let result = super::super::finish(dr, &sum)?;
            assert_eq!(result.value().take().to_projective(), correction + base);
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn zero_value_and_blind_reject_at_finite_export() {
    let result = Simulator::<Fp>::simulate(Fq::ZERO, |dr, witness| {
        let zero = Element::zero(dr);
        let amount = arithmetic::bounded::<_, 51>(dr, &zero, MAX_MONEY)?;
        let blind = free_bits(dr, &witness)?;
        commitment(dr, &NEG_V_TABLE, &amount, &blind)?;
        Ok(())
    });
    assert!(result.is_err());
}
