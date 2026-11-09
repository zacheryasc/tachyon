use core::{array, iter};

use ragu_primitives::Simulator;

use super::*;
use crate::{constants::MAX_MONEY, keys::public::ACTION_AUTH_GENERATOR, radix8, value};

lazy_static::lazy_static! {
    static ref R_TABLE: Table<85> = table(*value::VALUE_COMMIT_R, None);
    static ref G_TABLE: Table<85> = table(ACTION_AUTH_GENERATOR.to_projective(), None);
    static ref V_TABLE: Table<17> = amount_table(*value::VALUE_COMMIT_V, Ep::identity());
    static ref NEG_V_TABLE: Table<17> = amount_table(-*value::VALUE_COMMIT_V, Ep::identity());
}

fn check_counts(before: (usize, usize), dr: &Simulator<Fp>, expected: (usize, usize)) {
    assert_eq!(
        (dr.num_gates() - before.0, dr.num_constraints() - before.1),
        expected
    );
}

fn native(output: &CompletePoint<'_, Simulator<Fp>>) -> Ep {
    if output.infinity.value().take() {
        Ep::identity()
    } else {
        EpAffine::from_xy(*output.x.value().take(), *output.y.value().take())
            .unwrap()
            .to_projective()
    }
}

fn alloc_bits<'dr, const N: usize>(
    dr: &mut Simulator<Fp>,
    bits: [bool; N],
) -> Result<FixedVec<Boolean<'dr, Simulator<Fp>>, ConstLen<N>>> {
    FixedVec::try_from_fn(|index| {
        Boolean::alloc(dr, &mut (), Simulator::<Fp>::just(|| bits[index]))
    })
}

fn decode(bits: &[bool]) -> Fq {
    bits.as_chunks::<3>()
        .0
        .iter()
        .rev()
        .fold(Fq::ZERO, |acc, &[sign, low, high]| {
            let magnitude = Fq::from(1 + 2 * u64::from(low) + 4 * u64::from(high));
            acc * Fq::from(8) + if sign { magnitude } else { -magnitude }
        })
}

/// Deterministic scalars from xorshift-filled wide bytes.
fn scalars(count: usize) -> Vec<Fq> {
    let mut state = 0x0008_5260u64;
    iter::repeat_with(|| {
        let mut wide = [0u8; 64];
        for chunk in wide.chunks_mut(8) {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            chunk.copy_from_slice(&state.to_le_bytes());
        }
        Fq::from_uniform_bytes(&wide)
    })
    .take(count)
    .collect()
}

#[test]
fn walk_counts() {
    Simulator::<Fp>::simulate((), |dr, _| {
        let value = Element::constant(dr, Fp::from(17));
        let mut before = (dr.num_gates(), dr.num_constraints());
        let digest = arithmetic::bits::<_, 255>(dr, &value)?;
        check_counts(before, dr, (325, 676));
        before = (dr.num_gates(), dr.num_constraints());
        walk(dr, &R_TABLE, &digest)?;
        check_counts(before, dr, (430, 860));
        before = (dr.num_gates(), dr.num_constraints());
        let digits = amount_digits(dr, &value)?;
        check_counts(before, dr, (68, 137));
        before = (dr.num_gates(), dr.num_constraints());
        walk(dr, &V_TABLE, &digits)?;
        check_counts(before, dr, (93, 186));
        Ok(())
    })
    .unwrap();
}

#[test]
fn encoder_decoder_and_free_walk_match_native() {
    let half = Fq::from(2).invert().unwrap();
    let mut cases = Vec::from([
        Fq::ZERO,
        Fq::ONE,
        Fq::from(2),
        Fq::from(3),
        -Fq::ONE,
        -Fq::from(2),
        Fq::from_bytes((-Fp::ONE).to_bytes()).unwrap(),
        Fq::from(2).pow_u64(254),
        Fq::from(2).pow_u64(254) + Fq::ONE,
        -half,
        half,
    ]);
    cases.extend(scalars(32));
    for scalar in cases {
        assert_eq!(decode(&encode(scalar)), scalar);
        for (table, base) in [
            (&*R_TABLE, *value::VALUE_COMMIT_R),
            (&*G_TABLE, ACTION_AUTH_GENERATOR.to_projective()),
        ] {
            Simulator::<Fp>::simulate(scalar, |dr, witness| {
                let bits = free_bits(dr, &witness)?;
                let output = walk(dr, table, &bits)?;
                assert_eq!(output.infinity.value().take(), scalar == Fq::ZERO);
                assert_eq!(native(&output), base * scalar);
                Ok(())
            })
            .unwrap();
        }
    }
}

#[test]
fn selector_matches_shared_digit_definition() {
    for (index, digit) in DIGITS.into_iter().enumerate() {
        let magnitude = *value::VALUE_COMMIT_R * Fq::from(u64::from(digit.unsigned_abs()));
        let expected = if digit > 0 { magnitude } else { -magnitude };
        Simulator::<Fp>::simulate((), |dr, _| {
            let bits = alloc_bits::<3>(dr, array::from_fn(|bit| index & (1 << bit) != 0))?;
            assert_eq!(bits.len(), 3);
            let selected = select(dr, &R_TABLE.rows[0], [&bits[0], &bits[1], &bits[2]])?;
            assert_eq!(
                (*selected.x.value().take(), *selected.y.value().take()),
                expected.to_affine().coordinates().unwrap()
            );
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn top_window_inverse_and_doubling() {
    let zero = encode(Fq::ZERO);
    let mut doubling = zero;
    doubling[252] = !doubling[252];
    let power = Fq::from(8).pow_u64(84);
    for (bits, inverse) in [(zero, true), (doubling, false)] {
        let prefix = decode(&bits[..252]);
        let top = decode(&bits[252..]) * power;
        assert_eq!(prefix, if inverse { -top } else { top });
        let expected = *value::VALUE_COMMIT_R * decode(&bits);
        Simulator::<Fp>::simulate((), |dr, _| {
            let allocated = alloc_bits(dr, bits)?;
            let output = walk(dr, &R_TABLE, &allocated)?;
            assert_eq!(output.infinity.value().take(), inverse);
            assert_eq!(native(&output), expected);
            Ok(())
        })
        .unwrap();
    }
}

fn add_bits<const N: usize>(left: [bool; N], right: [bool; N]) -> Option<[bool; N]> {
    let mut carry = false;
    let sum = array::from_fn(|index| {
        let total = u8::from(left[index]) + u8::from(right[index]) + u8::from(carry);
        carry = total >= 2;
        total & 1 == 1
    });
    (!carry).then_some(sum)
}

#[test]
fn digest_walk_matches_native_signed_reading() {
    let mut digests = Vec::from([
        Fp::ZERO,
        Fp::ONE,
        Fp::from(2),
        -Fp::ONE,
        Fp::from(2).pow_u64(254),
    ]);
    digests.extend(scalars(16).into_iter().map(|scalar| {
        let mut bytes = scalar.to_bytes();
        bytes[31] &= 0x3f;
        Fp::from_bytes(bytes).unwrap()
    }));
    let canonical = |digest: Fp| -> [bool; 255] {
        let bits = digest.to_le_bits();
        array::from_fn(|index| bits.as_ref()[index])
    };
    let modulus = add_bits(canonical(-Fp::ONE), array::from_fn(|index| index == 0)).unwrap();
    let base = ACTION_AUTH_GENERATOR.to_projective();
    for digest in digests {
        let expected = base * radix8::fp_to_fq(digest);
        Simulator::<Fp>::simulate(digest, |dr, witness| {
            let element = Element::alloc(dr, &mut (), witness)?;
            let bits = arithmetic::bits::<_, 255>(dr, &element)?;
            assert_eq!(native(&walk(dr, &G_TABLE, &bits)?), expected);
            Ok(())
        })
        .unwrap();
        // h + p recomposes to h but denotes a different scalar: keep the comparator.
        if let Some(wide) = add_bits(canonical(digest), modulus) {
            assert_ne!(decode(&wide), radix8::fp_to_fq(digest));
        }
    }
}

#[test]
fn amount_walks_match_native() {
    let base = *value::VALUE_COMMIT_V;
    let fee = amount_table(base, -base * Fq::from(MAX_MONEY));
    for amount in [0u64, 1, 2, 3, 6, 7, 1 << 50, MAX_MONEY - 1, MAX_MONEY] {
        Simulator::<Fp>::simulate(amount, |dr, witness| {
            let element = Element::alloc(dr, &mut (), witness.map(Fp::from))?;
            let digits = bounded_amount(dr, &element, MAX_MONEY)?;
            let scalar = Fq::from(amount);
            for (table, expected) in [
                (&*V_TABLE, base * scalar),
                (&*NEG_V_TABLE, -base * scalar),
                (&fee, base * (scalar - Fq::from(MAX_MONEY))),
            ] {
                let output = walk(dr, table, &digits)?;
                assert_eq!(output.infinity.value().take(), expected.is_identity());
                assert_eq!(native(&output), expected);
            }
            Ok(())
        })
        .unwrap();
    }
    let amount = (1u64 << 51) - 1;
    Simulator::<Fp>::simulate((), |dr, _| {
        let element = Element::constant(dr, Fp::from(amount));
        let digits = amount_digits(dr, &element)?;
        assert_eq!(
            native(&walk(dr, &V_TABLE, &digits)?),
            base * Fq::from(amount)
        );
        Ok(())
    })
    .unwrap();
}

#[test]
fn amount_digits_reject_out_of_range() {
    for (amount, digits_exist) in [
        (Fp::from((1 << 51) - 1), true),
        (Fp::from(1 << 51), false),
        (-Fp::ONE, false),
    ] {
        let digits = Simulator::<Fp>::simulate(amount, |dr, witness| {
            let element = Element::alloc(dr, &mut (), witness)?;
            amount_digits(dr, &element)?;
            Ok(())
        });
        assert_eq!(digits.is_ok(), digits_exist);
        let bounded = Simulator::<Fp>::simulate(amount, |dr, witness| {
            let element = Element::alloc(dr, &mut (), witness)?;
            bounded_amount(dr, &element, MAX_MONEY)?;
            Ok(())
        });
        assert!(bounded.is_err());
    }
}

#[test]
fn commitment_matches_native_and_rejects_identity() {
    let value_base = *value::VALUE_COMMIT_V;
    let blind_base = *value::VALUE_COMMIT_R;
    for (amount, blind) in [
        (0u64, Fq::ONE),
        (1, Fq::ZERO),
        (MAX_MONEY, -Fq::ONE),
        (12_345, scalars(1)[0]),
    ] {
        let expected = -value_base * Fq::from(amount) + blind_base * blind;
        Simulator::<Fp>::simulate((amount, blind), |dr, witness| {
            let element =
                Element::alloc(dr, &mut (), witness.as_ref().map(|pair| Fp::from(pair.0)))?;
            let digits = bounded_amount(dr, &element, MAX_MONEY)?;
            let bits = free_bits(dr, &witness.as_ref().map(|pair| pair.1))?;
            let point = commitment(dr, &NEG_V_TABLE, &R_TABLE, &digits, &bits)?;
            assert_eq!(point.value().take().to_projective(), expected);
            Ok(())
        })
        .unwrap();
    }
    let identity = Simulator::<Fp>::simulate(Fq::ZERO, |dr, witness| {
        let zero = Element::zero(dr);
        let digits = bounded_amount(dr, &zero, MAX_MONEY)?;
        let bits = free_bits(dr, &witness)?;
        commitment(dr, &NEG_V_TABLE, &R_TABLE, &digits, &bits)?;
        Ok(())
    });
    assert!(identity.is_err());
}
