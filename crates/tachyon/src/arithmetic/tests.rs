use rand::{Rng as _, SeedableRng as _, rngs::StdRng};

use super::*;
#[cfg(feature = "std")]
use crate::bench;

fn points(count: usize) -> Vec<(Fp, Fp)> {
    let rng = &mut StdRng::seed_from_u64(0);
    (0..count)
        .map(|index| {
            (
                Fp::from(u64::try_from(index).unwrap()),
                Fp::random(|bytes| rng.fill_bytes(bytes)),
            )
        })
        .collect()
}

#[test]
fn interpolation_recovers_varied_values() {
    for count in [1, 2, 7, 64, 129] {
        let input = points(count);
        let coefficients = interpolate(&input).unwrap();
        for (at, value) in input {
            assert_eq!(evaluate_iter(&coefficients, at), value);
        }
    }
}

#[test]
fn interpolation_boundaries() {
    assert_eq!(interpolate(&[]).unwrap(), [Fp::ZERO]);
    assert_eq!(
        interpolate(&[(Fp::ZERO, Fp::from(17))]).unwrap(),
        [Fp::from(17)]
    );
    let input = points(7);
    for repeated in [(Fp::ZERO, Fp::ONE), input[3]] {
        let mut duplicate = input.clone();
        duplicate.push(repeated);
        assert!(interpolate(&duplicate).is_none());
    }
    assert_eq!(
        interpolate(&[(Fp::ZERO, Fp::ZERO), (Fp::ONE, Fp::ZERO)]).unwrap(),
        [Fp::ZERO; 2]
    );
}

#[cfg(feature = "std")]
#[test]
#[ignore = "release-mode benchmark; run with just bench"]
fn bench_interpolation() {
    for count in [64, 256, 1024] {
        let input = points(count);
        bench::median(&alloc::format!("interpolation/{count}"), || {
            interpolate(&input)
        });
    }
}
