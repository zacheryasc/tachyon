use core::assert_matches;

use ragu_core::{Error, drivers::emulator::Emulator};
use ragu_primitives::Element;
use udon::{curve::Affine as _, field::Field as _};

use super::{
    EMPTY_STAMP_BRIDGE_HASH, enforce_stamp_domain, new_application,
    pasta::{EqAffine, Fp},
    poseidon,
};

#[test]
fn native_bridge_hash_matches_application() {
    let prepared = *EMPTY_STAMP_BRIDGE_HASH;
    let mut counter = Emulator::counter();
    let epoch = Element::constant(&mut counter, Fp::ZERO);
    let hash = prepared.map(|value| Element::constant(&mut counter, value));
    enforce_stamp_domain(&mut counter, &epoch, &hash).unwrap();

    let application = new_application().unwrap();
    for coefficients in [
        &[Fp::ONE][..],
        &[Fp::from(7), Fp::from(11)][..],
        &[Fp::from(3), Fp::ZERO, Fp::from(19), Fp::ONE][..],
    ] {
        let commitment = application.commit(coefficients).unwrap();
        let expected: [Fp; 2] = application
            .bridge_hash(commitment)
            .unwrap()
            .coordinates()
            .unwrap()
            .into();
        assert_eq!(poseidon::bridge_hash(commitment).unwrap(), expected);
    }
    assert_eq!(
        poseidon::bridge_hash(application.commit(&[Fp::ONE]).unwrap()).unwrap(),
        prepared
    );
    assert_matches!(
        poseidon::bridge_hash(EqAffine::identity()),
        Err(Error::InvalidWitness(_))
    );
}
