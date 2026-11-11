#![allow(clippy::min_ident_chars, reason = "test code")]

use ragu_core::drivers::emulator::Emulator;
use udon::field::Field as _;

use super::*;
use crate::primitives::TachygramSetCommit;

#[test]
fn empty_stamp_bridge_hash_matches_application() {
    let prepared = empty_stamp_bridge_hash(pasta::baked()).unwrap();
    assert_eq!(*EMPTY_STAMP_BRIDGE_HASH, prepared);

    // Exercise synthesis without witness values before using the application.
    let mut counter = Emulator::counter();
    let epoch = Element::constant(&mut counter, pasta::Fp::ZERO);
    let hash = <[pasta::Fp; 2]>::from(pasta::EpAffine::from(prepared).coordinates().unwrap())
        .map(|value| Element::constant(&mut counter, value));
    enforce_stamp_domain(&mut counter, &epoch, &hash).unwrap();

    let expected = TachygramSetCommit::default().bridge().unwrap();
    assert_eq!(prepared, expected);
}
