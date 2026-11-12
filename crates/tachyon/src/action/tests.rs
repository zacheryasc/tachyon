use alloc::{collections::BTreeSet, format, vec::Vec};

use rand::{SeedableRng as _, rngs::StdRng};

use super::*;
use crate::bench;

fn descriptors(count: usize, mixed: bool) -> Vec<Descriptor> {
    let rng = &mut StdRng::seed_from_u64(0);
    let shared_cv = value::Trapdoor::random(rng).commit(value::Positive::ZERO);
    (0..count)
        .map(|index| {
            let cv = value::Trapdoor::random(rng).commit(value::Positive::ZERO);
            let rk = public::ActionVerificationKey::try_from(EpAffine::from(cv)).unwrap();
            Descriptor {
                cv: if mixed && index.is_multiple_of(2) {
                    shared_cv
                } else {
                    cv
                },
                rk,
            }
        })
        .collect()
}

#[test]
fn descriptor_sets_preserve_canonical_order_and_duplicates() {
    for mixed in [false, true] {
        let mut input = descriptors(32, mixed);
        input.extend_from_within(..8);
        let mut expected: Vec<[u8; 64]> = input.iter().copied().collect();
        expected.sort_unstable();
        let mut sorted = input.clone();
        sorted.sort_unstable();
        assert_eq!(Vec::<[u8; 64]>::from_iter(sorted), expected);
        expected.dedup();
        let unique: BTreeSet<_> = input.into_iter().collect();
        assert_eq!(Vec::<[u8; 64]>::from_iter(unique), expected);
    }
}

#[test]
#[ignore = "release-mode benchmark; run with just bench"]
fn bench_descriptor_ordering() {
    for count in [64, 256, 1024] {
        for mixed in [false, true] {
            let input = descriptors(count, mixed);
            bench::median(&format!("descriptor_sort/{count}/mixed={mixed}"), || {
                let mut sorted = input.clone();
                sorted.sort_unstable();
                sorted
            });
            bench::median(&format!("descriptor_set/{count}/mixed={mixed}"), || {
                input.iter().copied().collect::<BTreeSet<_>>()
            });
        }
    }
}
