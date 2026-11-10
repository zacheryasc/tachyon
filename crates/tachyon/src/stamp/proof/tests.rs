use ragu_core::drivers::emulator::Emulator;
use ragu_primitives::Element;
use udon::{
    curve::{Affine as _, Projective as _},
    field::Field as _,
};

use super::{
    super::{Tachygram, TachygramSetPoly},
    EMPTY_STAMP_BRIDGE_HASH, TachygramSetCommit, enforce_stamp_domain, new_application,
    pasta::{EpAffine, Eq, Fp},
};

#[test]
fn native_bridge_hash_matches_application() {
    let prepared = *EMPTY_STAMP_BRIDGE_HASH;
    let mut counter = Emulator::counter();
    let epoch = Element::constant(&mut counter, Fp::ZERO);
    let hash = <[Fp; 2]>::from(EpAffine::from(prepared).coordinates().unwrap())
        .map(|value| Element::constant(&mut counter, value));
    enforce_stamp_domain(&mut counter, &epoch, &hash).unwrap();

    let application = new_application().unwrap();
    for commitment in [
        TachygramSetCommit::default(),
        TachygramSetPoly::from_iter([Tachygram::from(Fp::from(7))]).commit(),
        TachygramSetPoly::from_iter([Tachygram::from(Fp::from(3)), Tachygram::from(Fp::from(19))])
            .commit(),
    ] {
        let expected = application
            .bridge_hash(commitment.as_ref().to_affine())
            .unwrap();
        assert_eq!(EpAffine::from(commitment.bridge()), expected);
    }
    assert_eq!(TachygramSetCommit::default().bridge(), prepared);
}

#[test]
#[should_panic(expected = "tachygram set commitment is not the identity")]
fn bridge_panics_on_the_identity_commitment() {
    let _bridge = TachygramSetCommit::from(Eq::identity()).bridge();
}
