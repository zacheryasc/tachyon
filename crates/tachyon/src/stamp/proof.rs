//! Tachyon proofs via Ragu PCD.
//!
//! Registers all PCD step types and provides accumulator helpers for
//! stamp construction and verification.
//!
//! `Step::INDEX` runs from zero without gaps, and [`make_app`] registers the
//! steps in that order; `ApplicationBuilder` rejects any other sequence.
//! `Header::SUFFIX` runs from zero without gaps too.
//!
//! A step is named "noun + verb", where the noun is the header it **emits**,
//! not the one it reads. Most fuse steps read and emit the same header, which
//! leaves the rule invisible until one does not: `EvidenceTreeFuse` emits an
//! `EvidenceTree` and reads two `EvidenceTreePair`s, and `EvidenceTreePairFuse`
//! emits the pair. Three steps whose output is a part of what they read are
//! named for the input instead: `QrIntakeSplit`, `QrSideDescend` and
//! `EvidenceTreeOpen`.

#![allow(missing_debug_implementations, missing_docs, reason = "todo")]

pub mod delegation;
pub mod evidence;
pub mod output;
pub mod pool;
pub mod qr;
pub mod spend;
pub mod spendable;
pub mod stamp;
pub mod summary;

use lazy_static::lazy_static;
use ragu::{Application, ApplicationBuilder, RegistryTags};
use ragu_circuits::{polynomials::ProductionRank, staging::wire_degree};
use ragu_core::{Cycle, FixedGenerators as _, drivers::Driver, pasta::Pasta};
use ragu_primitives::{ENDOSCALAR_BITS, ENDOSCALAR_PRODUCTS, Element};
use udon::curve::{Affine, Projective as _};

use crate::{
    constants::EPOCH_MAX,
    keys::public::ACTION_AUTH_GENERATOR,
    pasta,
    primitives::TachygramSetBridge,
    relations::{arithmetic::bounded, curve::fixed_base},
    value,
};

lazy_static! {
    static ref R_TABLE: fixed_base::Table<85> = fixed_base::table(*value::VALUE_COMMIT_R, None);
    static ref G_TABLE: fixed_base::Table<85> =
        fixed_base::table(ACTION_AUTH_GENERATOR.to_projective(), None);
    static ref V_TABLE: fixed_base::Table<17> =
        fixed_base::amount_table(*value::VALUE_COMMIT_V, pasta::Ep::identity());
    static ref NEG_V_TABLE: fixed_base::Table<17> =
        fixed_base::amount_table(-*value::VALUE_COMMIT_V, pasta::Ep::identity());
}

/// Prepares the constant-one commitment's bridge hash without an application.
fn empty_stamp_bridge_hash(
    params: &<Pasta as Cycle>::Params,
) -> ragu_core::Result<TachygramSetBridge> {
    let (x, y) = Pasta::host_generators(params)
        .g()
        .first()
        .and_then(Affine::coordinates)
        .ok_or_else(|| {
            ragu_core::Error::Initialization("constant-one commitment is not finite".into())
        })?;
    // The bridge point follows the hoisted endoscalar's bits and products,
    // starting at the next reserved gate (two stage wires per gate).
    let first_wire = (ENDOSCALAR_BITS + ENDOSCALAR_PRODUCTS).next_multiple_of(2);
    let generators = Pasta::nested_generators(params).g();
    let [left, right] = [first_wire, first_wire + 1].map(|wire| {
        generators
            .get(wire_degree::<ProductionRank>(wire))
            .ok_or_else(|| ragu_core::Error::Initialization("bridge generator is missing".into()))
    });
    let commitment = left?.to_projective() * x + right?.to_projective() * y;
    commitment
        .to_affine()
        .coordinates()
        .map(|coordinates| <[pasta::Fp; 2]>::from(coordinates).into())
        .ok_or_else(|| {
            ragu_core::Error::Initialization("constant-one bridge hash is not finite".into())
        })
}

/// Step admission checks for the stamp's epoch and nonempty tachygram set.
fn enforce_stamp_domain<'dr, D: Driver<'dr, F = pasta::Fp>>(
    dr: &mut D,
    epoch: &Element<'dr, D>,
    bridge_hash: &[Element<'dr, D>; 2],
) -> ragu_core::Result<()> {
    let &[low, high] = EMPTY_STAMP_BRIDGE_HASH.as_ref();
    let low_element = Element::constant(dr, low);
    let high_element = Element::constant(dr, high);
    let equal_low = bridge_hash[0].is_equal(dr, &mut (), &low_element)?;
    let equal_high = bridge_hash[1].is_equal(dr, &mut (), &high_element)?;
    equal_low
        .and(dr, &equal_high)?
        .element()
        .enforce_zero(dr)
        .map_err(|_err| ragu_core::Error::InvalidWitness("invalid anchor step".into()))?;
    bounded::<D, 32>(dr, epoch, u64::from(EPOCH_MAX))?;
    Ok(())
}

/// Eight payload elements for QR split, selection and bucket headers, plus one
/// suffix element.
pub const HEADER_SIZE: usize = 9;

fn make_app() -> Result<Application<'static, Pasta, ProductionRank, HEADER_SIZE>, ragu_core::Error>
{
    // Registry tags use the fixed Tachyon beacon and configuration digest.
    let manifest = blake2b_simd::Params::new()
        .hash_length(32)
        .hash(b"Tachyon PCD: Pasta, R13, H9, steps 0..38, ragu a73db816");
    let tags = RegistryTags::<Pasta>::from_beacon(b"Tachyon registry beacon", manifest.as_bytes());
    ApplicationBuilder::<Pasta, ProductionRank, HEADER_SIZE>::new()
        .with_registry_tags(tags, manifest.as_bytes())?
        .register(delegation::NoteSeed)?
        .register(delegation::NullifierDerive)?
        .register(pool::UnspentFuse)?
        .register(pool::UnspentBind)?
        .register(spendable::SpendableInit)?
        .register(spendable::SpendableLift)?
        .register(output::OutputBind)?
        .register(stamp::OutputAction)?
        .register(spend::SpendBind)?
        .register(stamp::SpendAction)?
        .register(stamp::StampMerge)?
        .register(stamp::StampLift)?
        .register(delegation::NullifierFuse)?
        .register(summary::SummarySeed)?
        .register(summary::SummaryAdvance)?
        .register(qr::QrSummaryIntake)?
        .register(qr::QrIntakeMerge)?
        .register(qr::QrIntakeSplit)?
        .register(qr::QrSideDescend)?
        .register(qr::QrUnspentInit)?
        .register(qr::QrBucketSeal)?
        .register(qr::QrStampIntakeSeed)?
        .register(spendable::QrSpendableInit)?
        .register(qr::QrEmptyIntakeSeed)?
        .register(pool::UnspentLift)?
        .register(evidence::EvidenceTreePairFuse)?
        .register(evidence::EvidenceTreeFuse)?
        .register(evidence::EvidenceTreeCap)?
        .register(evidence::EvidenceTreeDescend)?
        .register(evidence::EvidenceTreeOpen)?
        .register(evidence::EvidenceTreeLeafPair)?
        .register(pool::AnchorSpanSeed)?
        .register(pool::AnchorSpanFuse)?
        .register(stamp::FeeFuse)?
        .register(stamp::ActionMerge)?
        .register(stamp::ActionLift)?
        .register(stamp::FeeSeed)?
        .register(stamp::StampUnmerge)?
        .register(qr::QrSideSelect)?
        .finalize(pasta::baked())
}

lazy_static! {
    /// Fixed by the baked parameters and production rank, independently of PCD setup.
    static ref EMPTY_STAMP_BRIDGE_HASH: TachygramSetBridge = {
        #[expect(clippy::expect_used, reason = "the fixed setup has finite bridge generators")]
        empty_stamp_bridge_hash(pasta::baked()).expect("valid constant-one bridge hash")
    };

    /// A static ref to the mock ragu application.
    pub static ref PROOF_SYSTEM: Application<'static, Pasta, ProductionRank, HEADER_SIZE> = {
        #[expect(
            clippy::expect_used,
            reason = "hardcoded step ordering must register cleanly"
        )]
        make_app().expect("registration of fixed step list must succeed")
    };
}

#[cfg(test)]
mod tests {
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
        let hash = prepared
            .as_ref()
            .map(|value| Element::constant(&mut counter, value));
        enforce_stamp_domain(&mut counter, &epoch, &hash).unwrap();

        let expected = TachygramSetCommit::default().bridge().unwrap();
        assert_eq!(prepared, expected);
    }
}
