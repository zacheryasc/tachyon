use core::{array, assert_matches};

use ragu_primitives::Simulator;

use super::*;
use crate::{constants::MAX_MONEY, pasta::Fq};

#[test]
fn bounded_amount_rejects_raw_out_of_range_assignments() {
    for (amount, valid) in [
        (Fp::ZERO, true),
        (Fp::from(MAX_MONEY), true),
        (-Fp::ONE, false),
        (Fp::from(MAX_MONEY + 1), false),
        (Fp::from(2).pow_u64(51), false),
    ] {
        let result = Simulator::<Fp>::simulate(amount, |dr, assignment| {
            let element = Element::alloc(dr, &mut (), assignment)?;
            Bits::<_, 51>::bounded(dr, &element, MAX_MONEY)?;
            Ok(())
        });
        assert_eq!(result.is_ok(), valid);
    }
}

#[test]
fn epoch_successor_rejects_raw_final_and_out_of_domain_assignments() {
    for (index, valid) in [
        (Fp::ZERO, true),
        (Fp::from(u64::from(EPOCH_MAX - 1)), true),
        (-Fp::ONE, false),
        (Fp::from(u64::from(EPOCH_MAX)), false),
        (Fp::from(u64::from(EPOCH_MAX) + 1), false),
    ] {
        let result = Simulator::<Fp>::simulate(index, |driver, assignment| {
            let epoch = Element::alloc(driver, &mut (), assignment)?;
            EpochIndex::new(driver, &epoch)?.next(driver)?;
            Ok(())
        });
        assert_eq!(result.is_ok(), valid);
    }
}

#[test]
fn canonical_field_bits_cost() {
    Simulator::<Fp>::simulate(Fp::from(17), |dr, assignment| {
        let value = Element::alloc(dr, &mut (), assignment)?;
        let before = (dr.num_gates(), dr.num_constraints());
        Bits::<_, 255>::new(dr, &value)?;
        assert_eq!(
            (dr.num_gates() - before.0, dr.num_constraints() - before.1),
            (325, 676)
        );
        Ok(())
    })
    .unwrap();
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
        Bits(allocated).enforce_canonical(dr)
    })
    .map(|_| ())
}

#[test]
fn zero_run_comparator_attacks() {
    let maximum: [bool; 255] = array::from_fn(|index| (-Fp::ONE).to_le_bits().as_ref()[index]);
    compare(maximum, Some(-Fp::ONE)).unwrap();
    let modulus = Fq::from_bytes((-Fp::ONE).to_bytes()).unwrap() + Fq::ONE;
    let modulus_bits = array::from_fn(|index| modulus.to_le_bits().as_ref()[index]);
    assert_matches!(compare(modulus_bits, Some(Fp::ZERO)), Err(_));
    let alias = modulus + Fq::from(17);
    let alias_bits = array::from_fn(|index| alias.to_le_bits().as_ref()[index]);
    assert_matches!(compare(alias_bits, Some(Fp::from(17))), Err(_));
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
        }
    }
}
