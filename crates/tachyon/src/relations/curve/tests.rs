use ragu_primitives::Simulator;

use super::*;
use crate::{pasta::Fq, relations::arithmetic::scalar_bits};

#[test]
fn complete_curve_addition_handles_inverse_points() {
    let generator = EpAffine::generator();
    Simulator::<Fp>::simulate((generator, -generator), |dr, assignment| {
        let left = Point::alloc(dr, assignment.as_ref().map(|candidate| candidate.0))?;
        let right = Point::alloc(dr, assignment.as_ref().map(|candidate| candidate.1))?;
        let left_complete = from_point(dr, &left)?;
        let right_complete = from_point(dr, &right)?;
        assert!(
            add_complete(dr, &left_complete, &right_complete)?
                .infinity
                .value()
                .take()
        );
        Ok(())
    })
    .unwrap();
}

#[test]
fn scalar_multiplication_accepts_scalars_above_the_circuit_field_modulus() {
    Simulator::<Fp>::simulate(-Fq::ONE, |dr, assignment| {
        let bits = scalar_bits(dr, &assignment)?;
        let base = Point::constant(dr, EpAffine::generator())?;
        let scaled = scale(dr, &base, &bits)?;
        assert_eq!(
            scaled.value().take().to_projective(),
            EpAffine::generator().to_projective() * assignment.take()
        );
        Ok(())
    })
    .unwrap();
}

#[test]
fn fixed_value_product_matches_bit_loop() {
    Simulator::<Fp>::simulate(Fq::from(23), |dr, assignment| {
        let amount = Element::constant(dr, Fp::from(17));
        let amount_bits = instep::amount_bits(dr, &amount)?;
        let blind_bits = scalar_bits(dr, &assignment)?;
        let reference = commitment(dr, &amount_bits, &blind_bits, true)?;
        let product = instep::walk(dr, &instep::NEG_V, &amount_bits)?;
        let blind = Point::constant(dr, (*value::VALUE_COMMIT_R * Fq::from(23)).to_affine())?;
        let complete_blind = from_point(dr, &blind)?;
        let computed = add_complete(dr, &product, &complete_blind)?;
        let result = finish(dr, &computed)?;
        assert_eq!(result.value().take(), reference.value().take());
        Ok(())
    })
    .unwrap();
}
