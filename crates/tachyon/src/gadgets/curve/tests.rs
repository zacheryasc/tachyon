use ragu_primitives::Simulator;

use super::*;

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
