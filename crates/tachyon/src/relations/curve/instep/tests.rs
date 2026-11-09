use core::assert_matches;

use ragu_primitives::Simulator;

use super::*;

fn check_counts(before: (usize, usize), dr: &Simulator<Fp>, expected: (usize, usize)) {
    assert_eq!(
        (dr.num_gates() - before.0, dr.num_constraints() - before.1),
        expected
    );
}

#[test]
fn unit_counts() {
    initialize();
    Simulator::<Fp>::simulate((), |dr, _| {
        let left = constant(dr, EpAffine::generator())?;
        let right = constant(
            dr,
            EpAffine::generator().to_projective().double().to_affine(),
        )?;
        let mut before = (dr.num_gates(), dr.num_constraints());
        add_incomplete(dr, &left, &right)?;
        check_counts(before, dr, (3, 6));
        before = (dr.num_gates(), dr.num_constraints());
        add_finite(dr, &left, &right)?;
        check_counts(before, dr, (11, 22));
        let value = Element::constant(dr, Fp::from(17));
        before = (dr.num_gates(), dr.num_constraints());
        let bits = hash_bits(dr, &value)?;
        check_counts(before, dr, (325, 676));
        before = (dr.num_gates(), dr.num_constraints());
        walk(dr, &R_TABLE, &bits)?;
        check_counts(before, dr, (516, 1032));
        let maximum = Element::constant(dr, Fp::from(1000));
        before = (dr.num_gates(), dr.num_constraints());
        let (_, amount) = slacks(dr, &maximum, &value)?;
        check_counts(before, dr, (153, 309));
        before = (dr.num_gates(), dr.num_constraints());
        walk(dr, &FEE_V, &amount)?;
        check_counts(before, dr, (108, 216));
        Ok(())
    })
    .unwrap();
}

fn raw_bits(value: Fq) -> [bool; 255] {
    array::from_fn(|index| value.to_le_bits().as_ref()[index])
}

fn modulus_bits() -> [bool; 255] {
    let mut bits = raw_bits(-Fq::ONE);
    for bit in &mut bits {
        *bit = !*bit;
        if *bit {
            break;
        }
    }
    bits
}

fn add_bits(left: [bool; 255], right: [bool; 255]) -> [bool; 255] {
    let mut carry = false;
    let out = array::from_fn(|index| {
        let sum = u8::from(left[index]) + u8::from(right[index]) + u8::from(carry);
        carry = sum >= 2;
        sum & 1 == 1
    });
    assert!(!carry);
    out
}

fn reduced(bits: &[bool]) -> Fq {
    bits.iter().rev().fold(Fq::ZERO, |acc, bit| {
        acc.double() + Fq::from(u64::from(*bit))
    })
}

fn check_walk<const W: usize>(table: &Table<W>, base: Ep, correction: Ep, bits: [bool; 255]) {
    let expected = base * reduced(&bits[..2 * W + 3]) + correction;
    Simulator::<Fp>::simulate(bits, |dr, witness| {
        let allocated = FixedVec::<_, ConstLen<255>>::try_from_fn(|index| {
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
    reason = "selector inputs have ConstLen<2> and ConstLen<3>"
)]
fn check_table<const W: usize>(table: &Table<W>, base: Ep, correction: Ep) {
    let mut power = Fq::ONE;
    let mut offset = Fq::ZERO;
    for row in &table.low {
        for (digit, point) in row.iter().enumerate() {
            assert_eq!(
                point.to_projective(),
                base * (Fq::from(u64::try_from(digit + 2).unwrap()) * power)
            );
            assert!(!point.is_identity());
            Simulator::<Fp>::simulate((), |dr, _| {
                let bits = FixedVec::<_, ConstLen<2>>::try_from_fn(|index| {
                    Boolean::alloc(
                        dr,
                        &mut (),
                        Simulator::<Fp>::just(|| digit & (1 << index) != 0),
                    )
                })?;
                let before = (dr.num_gates(), dr.num_constraints());
                let selected = select_low(dr, row, [&bits[0], &bits[1]])?;
                check_counts(before, dr, (1, 2));
                let expected = point.coordinates().unwrap();
                assert_eq!(
                    (*selected.x.value().take(), *selected.y.value().take()),
                    expected
                );
                Ok(())
            })
            .unwrap();
        }
        offset += Fq::from(2) * power;
        power *= Fq::from(4);
    }
    for (digit, point) in table.top.iter().enumerate() {
        let native = base * (Fq::from(u64::try_from(digit).unwrap()) * power - offset) + correction;
        assert!(!native.is_identity());
        assert_eq!(point.to_projective(), native);
        Simulator::<Fp>::simulate((), |dr, _| {
            let bits = FixedVec::<_, ConstLen<3>>::try_from_fn(|index| {
                Boolean::alloc(
                    dr,
                    &mut (),
                    Simulator::<Fp>::just(|| digit & (1 << index) != 0),
                )
            })?;
            let before = (dr.num_gates(), dr.num_constraints());
            let selected = select_top(dr, &table.top, [&bits[0], &bits[1], &bits[2]])?;
            check_counts(before, dr, (4, 8));
            let expected = point.coordinates().unwrap();
            assert_eq!(
                (*selected.x.value().take(), *selected.y.value().take()),
                expected
            );
            Ok(())
        })
        .unwrap();
    }
}

#[test]
fn tables_and_walks() {
    initialize();
    for (width, shift) in [(126, 0), (24, 0), (24, MAX_MONEY)] {
        let place = Fq::from(4).pow_u64(width);
        let offset = Fq::from(2) * (place - Fq::ONE) * Fq::from(3).invert().unwrap();
        for digit in 0..8 {
            assert_ne!(Fq::from(digit) * place - offset - Fq::from(shift), Fq::ZERO);
        }
    }
    let power = Fq::from(4).pow_u64(126);
    let third = Fq::from(3).invert().unwrap();
    let deep_dive = -Fq::from(2) * (Fq::from(4).pow_u64(127) - Fq::ONE) * third;
    let doubles = (Fq::from(2) * power + Fq::from(4)) * third + Fq::from(2) * power;
    let noncanonical = add_bits(
        raw_bits(Fq::from(12) * power - Fq::from(4) * (power - Fq::ONE) * third),
        modulus_bits(),
    );
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
        modulus_bits(),
        noncanonical,
    ]);
    for bit in 0..255 {
        let mut bits = [false; 255];
        bits[bit] = true;
        cases.push(bits);
        if bit & 1 == 0 {
            let one_hot = Fq::from(2).pow_u64(u64::try_from(bit).unwrap());
            cases.push(raw_bits(one_hot - Fq::ONE));
            cases.push(raw_bits(one_hot + Fq::ONE));
        }
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
    for (table, base, correction) in [
        (&*V_TABLE, *value::VALUE_COMMIT_V, Ep::identity()),
        (&*NEG_V, -*value::VALUE_COMMIT_V, Ep::identity()),
        (
            &*FEE_V,
            *value::VALUE_COMMIT_V,
            -*value::VALUE_COMMIT_V * Fq::from(MAX_MONEY),
        ),
    ] {
        check_table(table, base, correction);
        for amount in [0, 1, MAX_MONEY, (1 << 51) - 1] {
            check_walk(table, base, correction, raw_bits(Fq::from(amount)));
        }
    }
    assert_eq!(cases.len(), 521);
}

#[test]
fn finite_addition_exceptions() {
    let base = EpAffine::generator();
    for other in [base, -base, base.to_projective().double().to_affine()] {
        Simulator::<Fp>::simulate((), |dr, _| {
            let left = constant(dr, base)?;
            let right = constant(dr, other)?;
            let before = (dr.num_gates(), dr.num_constraints());
            let output = add_finite(dr, &left, &right)?;
            check_counts(before, dr, (11, 22));
            let one = Element::one();
            let third = CompletePoint {
                x: left.x.clone(),
                y: left.y.clone(),
                infinity: one.is_zero(dr, &mut ())?,
            };
            let sum = super::super::add_complete(dr, &output, &third)?;
            let actual = if sum.infinity.value().take() {
                Ep::identity()
            } else {
                EpAffine::from_xy(*sum.x.value().take(), *sum.y.value().take())
                    .unwrap()
                    .to_projective()
            };
            assert_eq!(
                actual,
                base.to_projective().double() + other.to_projective()
            );
            Ok(())
        })
        .unwrap();
    }
}

fn compare(bits: [bool; 255], expected_value: Option<Fp>) -> Result<()> {
    Simulator::simulate(bits, |dr, witness| {
        let allocated = FixedVec::<_, ConstLen<255>>::try_from_fn(|index| {
            Boolean::alloc(
                dr,
                &mut (),
                witness.as_ref().map(|assignment| assignment[index]),
            )
        })?;
        if let Some(value) = expected_value {
            let mut sum = Element::zero(dr);
            for bit in allocated.iter().rev() {
                sum = sum.double(dr).add(dr, &bit.element());
            }
            let expected = Element::constant(dr, value);
            sum.enforce_equal(dr, &expected)?;
        }
        canonical(dr, &allocated)
    })
    .map(|_| ())
}

#[test]
fn zero_run_comparator_attacks() {
    let maximum: [bool; 255] = array::from_fn(|index| (-Fp::ONE).to_le_bits().as_ref()[index]);
    compare(maximum, Some(-Fp::ONE)).unwrap();
    let modulus = raw_bits(Fq::from_bytes((-Fp::ONE).to_bytes()).unwrap() + Fq::ONE);
    assert_matches!(compare(modulus, Some(Fp::ZERO)), Err(_));
    let alias = add_bits(modulus, raw_bits(Fq::from(17)));
    assert_matches!(compare(alias, Some(Fp::from(17))), Err(_));
    let mut count = 0;
    for index in 0..254 {
        if !maximum[index] {
            let mut greater = maximum;
            greater[index] = true;
            assert_matches!(compare(greater, None), Err(_));
            let prior_one = (index + 1..255)
                .find(|position| maximum[*position])
                .unwrap();
            greater[prior_one] = false;
            compare(greater, None).unwrap();
            count += 1;
        }
    }
    assert_eq!(count, 209);
}

#[test]
fn slack_boundaries() {
    for (maximum, fee, valid) in [
        (0, 0, true),
        (1000, 1000, true),
        (MAX_MONEY, 0, true),
        (MAX_MONEY, MAX_MONEY, true),
        (7, 8, false),
        (MAX_MONEY + 1, 0, false),
    ] {
        let result = Simulator::<Fp>::simulate((), |dr, _| {
            let maximum_element = Element::constant(dr, Fp::from(maximum));
            let fee_element = Element::constant(dr, Fp::from(fee));
            slacks(dr, &maximum_element, &fee_element)?;
            Ok(())
        });
        assert_eq!(result.is_ok(), valid);
    }
    Simulator::<Fp>::simulate((), |dr, _| {
        let zero = Element::zero(dr);
        let hash = hash_bits(dr, &zero)?;
        let scalar = walk(dr, &R_TABLE, &hash)?;
        let maximum = Element::constant(dr, Fp::from(MAX_MONEY));
        let slack = arithmetic::bits::<_, 51>(dr, &maximum)?;
        let value = walk(dr, &FEE_V, &slack)?;
        let sum = super::super::add_complete(dr, &scalar, &value)?;
        assert_matches!(super::super::finish(dr, &sum).map(|_| ()), Err(_));
        Ok(())
    })
    .unwrap();
}
