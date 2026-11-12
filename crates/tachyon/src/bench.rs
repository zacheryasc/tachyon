//! Release-only, opt-in microbenchmarks; fixture generation stays outside
//! timing.

use core::{hint::black_box, time::Duration};
use std::time::Instant;

pub(crate) fn median<T>(name: &str, mut run: impl FnMut() -> T) {
    assert!(!cfg!(debug_assertions), "benchmarks require --release");
    drop(black_box(run())); // Warm caches and lazy initialization before sampling.
    let mut samples = [Duration::ZERO; 9];
    for sample in &mut samples {
        let start = Instant::now();
        drop(black_box(run()));
        *sample = start.elapsed();
    }
    let (_, median, _) = samples.select_nth_unstable(4);
    std::println!("{name}: median={} us", median.as_micros());
}
