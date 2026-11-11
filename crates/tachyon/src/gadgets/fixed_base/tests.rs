use alloc::{format, vec::Vec};

use ragu_primitives::Simulator;

use super::*;
use crate::constants::MAX_MONEY;

fn scalar(bits: &[bool]) -> Fq {
    bits.iter().rev().fold(Fq::ZERO, |acc, bit| {
        acc.double() + Fq::from(u64::from(*bit))
    })
}

fn alloc_bits<'dr, const N: usize>(
    dr: &mut Simulator<Fp>,
    bits: [bool; N],
) -> Result<FixedVec<Boolean<'dr, Simulator<Fp>>, ConstLen<N>>> {
    FixedVec::try_from_fn(|index| {
        Boolean::alloc(dr, &mut (), Simulator::<Fp>::just(|| bits[index]))
    })
}

fn walk<const W: usize, const N: usize>(table: &Table<W>, bits: [bool; N]) -> Result<(Fp, Fp)> {
    let mut output = (Fp::ZERO, Fp::ZERO);
    Simulator::<Fp>::simulate((), |dr, _| {
        let allocated = alloc_bits(dr, bits)?;
        let [x, y] = table.walk(dr, &allocated, None)?;
        output = (*x.value().take(), *y.value().take());
        Ok(())
    })?;
    Ok(output)
}

#[test]
fn walks_compute_the_binary_value() {
    let digits: [[bool; 3]; 8] =
        array::from_fn(|digit| array::from_fn(|position| digit & (1 << position) != 0));
    let mut wide = Vec::from([
        [false; 255],
        [true; 255],
        array::from_fn(|index| (-Fq::ONE).to_le_bits().as_ref()[index]),
        array::from_fn(|index| (-Fp::ONE).to_le_bits().as_ref()[index]),
    ]);
    wide.extend((0..255).map(|bit| array::from_fn(|index| index == bit)));
    wide.extend(digits.map(|digit| <[bool; 255]>::try_from([digit; 85].as_flattened()).unwrap()));
    for (base, table) in [
        (*orchard::VALUE_COMMIT_R, &*R_TABLE),
        (*ACTION_AUTH_GENERATOR, &*G_TABLE),
    ] {
        for bits in &wide {
            let expected = base * scalar(bits);
            let output = walk(table, *bits);
            if expected.is_identity() {
                assert!(output.is_err());
            } else {
                assert_eq!(output.unwrap(), expected.to_affine().coordinates().unwrap());
            }
        }
    }

    let value_base = *orchard::VALUE_COMMIT_V;
    let mut short: Vec<[bool; 51]> = [0u64, 1, 2, 3, MAX_MONEY]
        .map(|amount| array::from_fn(|index| amount & (1 << index) != 0))
        .into();
    short.extend(digits.map(|digit| <[bool; 51]>::try_from([digit; 17].as_flattened()).unwrap()));
    for (base, correction) in [
        (value_base, Ep::identity()),
        (-value_base, Ep::identity()),
        (value_base, -value_base * Fq::from(MAX_MONEY)),
    ] {
        let table = Table::<17>::new(base, correction);
        for bits in &short {
            let expected = base * scalar(bits) + correction;
            let output = walk(&table, *bits);
            if expected.is_identity() {
                assert!(output.is_err());
            } else {
                assert_eq!(output.unwrap(), expected.to_affine().coordinates().unwrap());
            }
        }
    }
}

/// A checked addition discharges its x difference through an inverse, so a
/// zero difference leaves no satisfying assignment, whatever inverse is chosen.
#[test]
fn exceptional_additions_have_no_satisfying_inverse() {
    // Zero digits make the prefix and top entry inverses. Low digits reading
    // 8^84 - 4 (8^84 - 1) / 7 under a top digit of one make them equal.
    let power = (0..84).fold(Fq::ONE, |acc, _| acc * Fq::from(8));
    let interior = (0..84).fold(Fq::ZERO, |acc, _| acc * Fq::from(8) + Fq::ONE);
    let doubling = power - Fq::from(4) * interior;
    let mut doubling_bits: [bool; 255] =
        array::from_fn(|index| doubling.to_le_bits().as_ref()[index]);
    assert!(!doubling_bits[252..].contains(&true));
    doubling_bits[252] = true;
    for table in [&*R_TABLE, &*G_TABLE] {
        for bits in [[false; 255], doubling_bits] {
            Simulator::<Fp>::simulate((), |dr, _| {
                let allocated = alloc_bits(dr, bits)?;
                let (prefix, [top_x, _]) = table.prefix_and_top(dr, &allocated)?;
                let difference = top_x.sub(dr, &prefix.x);
                assert_eq!(*difference.value().take(), Fp::ZERO);
                for advice in [Fp::ZERO, Fp::ONE, -Fp::ONE, Fp::from(7)] {
                    let rejection = difference
                        .enforce_invertible_with(dr, Simulator::<Fp>::just(|| advice))
                        .err();
                    assert!(
                        rejection
                            .is_some_and(|error| format!("{error}").contains("gate check failed"))
                    );
                }
                Ok(())
            })
            .unwrap();
        }
    }

    // With v = 0 the value prefix is [2 (8^16 - 1) / 7]V, so a blind point of
    // ± that point meets the join at equal x.
    let value_prefix = (0..16).fold(Fq::ZERO, |acc, _| acc * Fq::from(8) + Fq::from(2));
    for sign in [Fq::ONE, -Fq::ONE] {
        let (blind_x, _) = (*orchard::VALUE_COMMIT_V * (value_prefix * sign))
            .to_affine()
            .coordinates()
            .unwrap();
        Simulator::<Fp>::simulate((), |dr, _| {
            let allocated = alloc_bits(dr, [false; 51])?;
            let start_x = Element::constant(dr, blind_x);
            let (prefix, _) = V_TABLE.prefix_and_top(dr, &allocated)?;
            let difference = start_x.sub(dr, &prefix.x);
            assert_eq!(*difference.value().take(), Fp::ZERO);
            for advice in [Fp::ZERO, Fp::ONE, -Fp::ONE, Fp::from(7)] {
                let rejection = difference
                    .enforce_invertible_with(dr, Simulator::<Fp>::just(|| advice))
                    .err();
                assert!(
                    rejection.is_some_and(|error| format!("{error}").contains("gate check failed"))
                );
            }
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn value_commitments_accept_zero_and_reject_wide_values() {
    for (amount, blind, valid) in [
        (Fp::ZERO, Fq::ONE, true),
        (Fp::ONE, -Fq::ONE, true),
        (Fp::from(MAX_MONEY), Fq::from(2).pow_u64(254), true),
        (Fp::from(2).pow_u64(51), Fq::ONE, false),
        (-Fp::ONE, Fq::ONE, false),
    ] {
        let result = Simulator::<Fp>::simulate((amount, blind), |dr, witness| {
            let value = Element::alloc(dr, &mut (), witness.as_ref().map(|pair| pair.0))?;
            let blind_point = R_TABLE.mul_free(dr, &witness.as_ref().map(|pair| pair.1))?;
            let [cv_x, cv_y] = NEG_V_TABLE.mul_bounded(dr, &value, &blind_point)?;
            let expected = *orchard::VALUE_COMMIT_R * blind
                - *orchard::VALUE_COMMIT_V * scalar(&amount.to_le_bits().as_ref()[..51]);
            assert_eq!(
                (*cv_x.value().take(), *cv_y.value().take()),
                expected.to_affine().coordinates().unwrap()
            );
            Ok(())
        });
        assert_eq!(result.is_ok(), valid);
    }
}

#[test]
fn fee_commitment_accepts_a_zero_maximum() {
    let value_base = *orchard::VALUE_COMMIT_V;
    let fee_table = Table::<17>::new(value_base, -value_base * Fq::from(MAX_MONEY));
    for maximum in [0u64, 1, MAX_MONEY] {
        Simulator::<Fp>::simulate((), |dr, _| {
            let digest = Element::constant(dr, Fp::from(11));
            let slack = Element::constant(dr, Fp::from(MAX_MONEY - maximum));
            let blind_point = R_TABLE.mul_canonical(dr, &digest, None)?;
            let [cv_x, cv_y] = fee_table.mul_bounded(dr, &slack, &blind_point)?;
            let expected = *orchard::VALUE_COMMIT_R * Fq::from(11) - value_base * Fq::from(maximum);
            assert_eq!(
                (*cv_x.value().take(), *cv_y.value().take()),
                expected.to_affine().coordinates().unwrap()
            );
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn digest_walks_use_the_canonical_value() {
    let ak = *ACTION_AUTH_GENERATOR * Fq::from(5);
    let (ak_x, ak_y) = ak.to_affine().coordinates().unwrap();
    for digest in [Fp::ONE, -Fp::ONE, Fp::from(2).pow_u64(254)] {
        Simulator::<Fp>::simulate(digest, |dr, witness| {
            let element = Element::alloc(dr, &mut (), witness)?;
            let start = [Element::constant(dr, ak_x), Element::constant(dr, ak_y)];
            let [rk_x, rk_y] = G_TABLE.mul_canonical(dr, &element, Some(&start))?;
            let expected =
                *ACTION_AUTH_GENERATOR * scalar(&digest.to_le_bits().as_ref()[..255]) + ak;
            assert_eq!(
                (*rk_x.value().take(), *rk_y.value().take()),
                expected.to_affine().coordinates().unwrap()
            );
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn comparator_rejects_every_encoding_above_the_modulus() {
    let compare = |candidate: [bool; 255]| {
        Simulator::<Fp>::simulate(candidate, |dr, witness| {
            let allocated = FixedVec::<_, ConstLen<255>>::try_from_fn(|index| {
                Boolean::alloc(dr, &mut (), witness.as_ref().map(|bits| bits[index]))
            })?;
            Table::<85>::enforce_canonical(dr, &allocated)
        })
        .map(|_| ())
    };
    let maximum: [bool; 255] = array::from_fn(|index| (-Fp::ONE).to_le_bits().as_ref()[index]);
    compare(maximum).unwrap();
    for index in 0..254 {
        if !maximum[index] {
            let mut greater = maximum;
            greater[index] = true;
            assert!(compare(greater).is_err());
            let prior_one = (index + 1..255)
                .find(|position| maximum[*position])
                .unwrap();
            greater[prior_one] = false;
            compare(greater).unwrap();
        }
    }
}
