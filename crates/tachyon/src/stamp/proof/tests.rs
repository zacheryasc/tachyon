use core::assert_matches;

use ragu_core::{Error, drivers::emulator::Emulator, pasta::Pasta};
use ragu_pcd::profile::{Profile, ProfiledCycle};
use ragu_primitives::Element;
use udon::{
    curve::{Affine as _, Projective as _},
    field::Field as _,
};

use super::{
    super::{Tachygram, TachygramSetPoly},
    EMPTY_STAMP_BRIDGE_HASH, TachygramSetCommit, enforce_stamp_domain, new_application,
    pasta::{Eq, Fp},
};

#[test]
fn application_profile_excludes_decompression() {
    // Ragu registers Decompress exactly when this statement circuit exists.
    // Its constant-one output slots do not preserve our non-membership checks.
    assert!(
        <<Pasta as ProfiledCycle>::Profile as Profile>::native_extension()
            .statement
            .is_none(),
        "Tachyon requires a profile without Decompress; statement support needs a slot-preservation audit",
    );
}

#[test]
fn native_bridge_hash_matches_application() {
    let prepared = *EMPTY_STAMP_BRIDGE_HASH;
    let mut counter = Emulator::counter();
    let epoch = Element::constant(&mut counter, Fp::ZERO);
    let hash = prepared
        .as_ref()
        .map(|value| Element::constant(&mut counter, value));
    enforce_stamp_domain(&mut counter, &epoch, &hash).unwrap();

    let application = new_application().unwrap();
    for commitment in [
        TachygramSetCommit::default(),
        TachygramSetPoly::from_iter([Tachygram::from(Fp::from(7))]).commit(),
        TachygramSetPoly::from_iter([Tachygram::from(Fp::from(3)), Tachygram::from(Fp::from(19))])
            .commit(),
    ] {
        let expected: [Fp; 2] = application
            .bridge_hash(commitment.as_ref().to_affine())
            .unwrap()
            .coordinates()
            .unwrap()
            .into();
        assert_eq!(*commitment.bridge().unwrap().as_ref(), expected);
    }
    assert_eq!(TachygramSetCommit::default().bridge().unwrap(), prepared);
    assert_matches!(
        TachygramSetCommit::from(Eq::identity()).bridge(),
        Err(Error::InvalidWitness(_))
    );
}
