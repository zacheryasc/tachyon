use super::*;

#[test]
fn epoch_from_field_rejects_out_of_range_and_truncated_values() {
    for index in [0, EPOCH_MAX] {
        assert_eq!(
            EpochIndex::try_from(Fp::from(u64::from(index))).unwrap(),
            EpochIndex(index)
        );
    }
    for value in [
        Fp::from(u64::from(EPOCH_MAX) + 1),
        Fp::from(1u64 << 32),
        -Fp::ONE,
    ] {
        EpochIndex::try_from(value).unwrap_err();
    }
}

#[test]
fn epoch_difference_counts_the_span() {
    assert_eq!(u64::from(EpochIndex(7) - EpochIndex(3)), 4);
    assert_eq!(u64::from(EpochIndex(3) - EpochIndex(3)), 0);
}

#[test]
#[should_panic(expected = "epoch difference is positive")]
fn epoch_difference_rejects_reversed_operands() {
    let _: EpochDiff = EpochIndex(3) - EpochIndex(7);
}
