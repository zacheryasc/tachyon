use core::array;

use ragu_primitives::{Element, Simulator};

use super::*;
use crate::{constants::MAX_MONEY, relations::arithmetic};

fn check_counts(before: (usize, usize), dr: &Simulator<Fp>, expected: (usize, usize)) {
    assert_eq!(
        (dr.num_gates() - before.0, dr.num_constraints() - before.1),
        expected
    );
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
    Simulator::<Fp>::simulate((), |dr, _| {
        let allocated = FixedVec::<_, ConstLen<N>>::try_from_fn(|index| {
            Boolean::alloc(dr, &mut (), Simulator::<Fp>::just(|| bits[index]))
        })?;
        let output = walk(dr, table, &allocated)?;
        assert_eq!(output.infinity.value().take(), expected.is_identity());
        if !expected.is_identity() {
            assert_eq!(
                EpAffine::from_xy(*output.x.value().take(), *output.y.value().take())
                    .unwrap()
                    .to_projective(),
                expected
            );
        }
        Ok(())
    })
    .unwrap();
}

fn raw_bits(value: Fq) -> [bool; 255] {
    array::from_fn(|index| value.to_le_bits().as_ref()[index])
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

#[test]
fn walk_counts() {
    let wide = table::<85>(*orchard::VALUE_COMMIT_R, Ep::identity());
    let short = table::<17>(*orchard::VALUE_COMMIT_V, Ep::identity());
    Simulator::<Fp>::simulate((), |dr, _| {
        let bits = FixedVec::<_, ConstLen<255>>::try_from_fn(|_| {
            Boolean::alloc(dr, &mut (), Simulator::<Fp>::just(|| false))
        })?;
        let mut before = (dr.num_gates(), dr.num_constraints());
        walk(dr, &wide, &bits)?;
        check_counts(before, dr, (430, 860));
        let amount = FixedVec::<_, ConstLen<51>>::try_from_fn(|_| {
            Boolean::alloc(dr, &mut (), Simulator::<Fp>::just(|| true))
        })?;
        before = (dr.num_gates(), dr.num_constraints());
        walk(dr, &short, &amount)?;
        check_counts(before, dr, (90, 180));
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
        (ACTION_AUTH_GENERATOR.to_projective(), Ep::identity()),
    ] {
        let wide = table::<85>(base, correction);
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
        let short = table::<17>(base, correction);
        let amounts = [0u64, 1, 2, 3, MAX_MONEY]
            .map(|amount| array::from_fn::<bool, 51, _>(|index| amount & (1 << index) != 0));
        let repeated = digits
            .iter()
            .map(|window| <[bool; 51]>::try_from([*window; 17].as_flattened()).unwrap());
        for bits in amounts.into_iter().chain(repeated) {
            check_walk(&short, base, correction, bits);
        }
    }
}

#[test]
fn top_addition_inverse_and_doubling() {
    // With all digits zero the prefix is [2]B and the top is [-2]B + C:
    // C=0 makes inverses, C=[4]B equal points, C=[5]B a generic sum.
    let base = EpAffine::generator().to_projective();
    for coefficient in [0u64, 4, 5] {
        let correction = base * Fq::from(coefficient);
        check_walk(&table::<2>(base, correction), base, correction, [false; 6]);
    }

    for top in [1, 5] {
        let bits = doubling_bits::<255>(top);
        check_walk(&R_TABLE, *orchard::VALUE_COMMIT_R, Ep::identity(), bits);
        let generator = ACTION_AUTH_GENERATOR.to_projective();
        check_walk(&G_TABLE, generator, Ep::identity(), bits);
    }
    let value_base = *orchard::VALUE_COMMIT_V;
    check_walk(&V_TABLE, value_base, Ep::identity(), doubling_bits::<51>(1));
    check_walk(
        &NEG_V_TABLE,
        -value_base,
        Ep::identity(),
        doubling_bits::<51>(1),
    );
}

#[test]
fn commitment_and_digest_walks_match_native() {
    let value_base = *orchard::VALUE_COMMIT_V;
    let blind_base = *orchard::VALUE_COMMIT_R;
    for (amount, blind) in [
        (0u64, Fq::ONE),
        (1, Fq::ZERO),
        (2, -Fq::ONE),
        (MAX_MONEY, Fq::from(2).pow_u64(254)),
    ] {
        let expected = -value_base * Fq::from(amount) + blind_base * blind;
        Simulator::<Fp>::simulate((amount, blind), |dr, witness| {
            let element =
                Element::alloc(dr, &mut (), witness.as_ref().map(|pair| Fp::from(pair.0)))?;
            let amount_bits = arithmetic::bounded::<_, 51>(dr, &element, MAX_MONEY)?;
            let bits = free_bits(dr, &witness.as_ref().map(|pair| pair.1))?;
            let point = commitment(dr, &NEG_V_TABLE, &amount_bits, &bits)?;
            assert_eq!(point.value().take().to_projective(), expected);
            Ok(())
        })
        .unwrap();
    }
    let identity = Simulator::<Fp>::simulate(Fq::ZERO, |dr, witness| {
        let zero = Element::zero(dr);
        let amount_bits = arithmetic::bounded::<_, 51>(dr, &zero, MAX_MONEY)?;
        let bits = free_bits(dr, &witness)?;
        commitment(dr, &NEG_V_TABLE, &amount_bits, &bits)?;
        Ok(())
    });
    assert!(identity.is_err());

    let generator = ACTION_AUTH_GENERATOR.to_projective();
    for digest in [Fp::ZERO, Fp::ONE, -Fp::ONE, Fp::from(2).pow_u64(254)] {
        let expected = generator * Fq::from_bytes(digest.to_bytes()).unwrap();
        Simulator::<Fp>::simulate(digest, |dr, witness| {
            let element = Element::alloc(dr, &mut (), witness)?;
            let bits = arithmetic::bits::<_, 255>(dr, &element)?;
            let output = walk(dr, &G_TABLE, &bits)?;
            assert_eq!(output.infinity.value().take(), expected.is_identity());
            if !expected.is_identity() {
                assert_eq!(
                    EpAffine::from_xy(*output.x.value().take(), *output.y.value().take())
                        .unwrap()
                        .to_projective(),
                    expected
                );
            }
            Ok(())
        })
        .unwrap();
    }
}
