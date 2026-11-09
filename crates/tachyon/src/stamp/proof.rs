//! Tachyon proofs via Ragu PCD.
//!
//! Registers all PCD step types and provides accumulator helpers for
//! stamp construction and verification.
//!
//! `Step::INDEX` runs from zero without gaps, and [`new_application`] registers
//! the steps in that order; `ApplicationBuilder` rejects any other sequence.
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

use alloc::boxed::Box;
use core::mem;

use lazy_static::lazy_static;
use ragu::{Application, ApplicationBuilder, RegistryTags, step::Step};
use ragu_circuits::polynomials::ProductionRank;
use ragu_core::{drivers::Driver, pasta::Pasta};
use ragu_primitives::Element;

use crate::{
    constants::EPOCH_MAX,
    pasta,
    primitives::{TachygramSetBridge, TachygramSetCommit},
    relations::arithmetic::bounded,
};

/// Step admission checks for the stamp's epoch and nonempty tachygram set.
fn enforce_stamp_domain<'dr, D: Driver<'dr, F = pasta::Fp>>(
    dr: &mut D,
    epoch: &Element<'dr, D>,
    bridge_hash: &[Element<'dr, D>; 2],
) -> ragu_core::Result<()> {
    let (low, high) = EMPTY_STAMP_BRIDGE_HASH.coordinates();
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

/// Builds the Tachyon application with the baked setup and fixed registry tags.
///
/// # Errors
///
/// Returns an error if step registration or application finalization fails.
pub fn new_application()
-> Result<Box<Application<'static, Pasta, ProductionRank, HEADER_SIZE>>, ragu_core::Error> {
    // Registry tags use the fixed Tachyon beacon and configuration digest.
    let manifest = blake2b_simd::Params::new()
        .hash_length(32)
        .hash(b"Tachyon PCD: Pasta, R13, H9, steps 0..38, ragu a73db816");
    let tags = RegistryTags::<Pasta>::from_beacon(b"Tachyon registry beacon", manifest.as_bytes());
    let mut builder = ApplicationBuilder::<Pasta, ProductionRank, HEADER_SIZE>::new()
        .with_registry_tags(tags, manifest.as_bytes())?;
    register_step(&mut builder, delegation::NoteSeed)?;
    register_step(&mut builder, delegation::NullifierDerive)?;
    register_step(&mut builder, pool::UnspentFuse)?;
    register_step(&mut builder, pool::UnspentBind)?;
    register_step(&mut builder, spendable::SpendableInit)?;
    register_step(&mut builder, spendable::SpendableLift)?;
    register_step(&mut builder, output::OutputBind)?;
    register_step(&mut builder, stamp::OutputAction)?;
    register_step(&mut builder, spend::SpendBind)?;
    register_step(&mut builder, stamp::SpendAction)?;
    register_step(&mut builder, stamp::StampMerge)?;
    register_step(&mut builder, stamp::StampLift)?;
    register_step(&mut builder, delegation::NullifierFuse)?;
    register_step(&mut builder, summary::SummarySeed)?;
    register_step(&mut builder, summary::SummaryAdvance)?;
    register_step(&mut builder, qr::QrSummaryIntake)?;
    register_step(&mut builder, qr::QrIntakeMerge)?;
    register_step(&mut builder, qr::QrIntakeSplit)?;
    register_step(&mut builder, qr::QrSideDescend)?;
    register_step(&mut builder, qr::QrUnspentInit)?;
    register_step(&mut builder, qr::QrBucketSeal)?;
    register_step(&mut builder, qr::QrStampIntakeSeed)?;
    register_step(&mut builder, spendable::QrSpendableInit)?;
    register_step(&mut builder, qr::QrEmptyIntakeSeed)?;
    register_step(&mut builder, pool::UnspentLift)?;
    register_step(&mut builder, evidence::EvidenceTreePairFuse)?;
    register_step(&mut builder, evidence::EvidenceTreeFuse)?;
    register_step(&mut builder, evidence::EvidenceTreeCap)?;
    register_step(&mut builder, evidence::EvidenceTreeDescend)?;
    register_step(&mut builder, evidence::EvidenceTreeOpen)?;
    register_step(&mut builder, evidence::EvidenceTreeLeafPair)?;
    register_step(&mut builder, pool::AnchorSpanSeed)?;
    register_step(&mut builder, pool::AnchorSpanFuse)?;
    register_step(&mut builder, stamp::FeeFuse)?;
    register_step(&mut builder, stamp::ActionMerge)?;
    register_step(&mut builder, stamp::ActionLift)?;
    register_step(&mut builder, stamp::FeeSeed)?;
    register_step(&mut builder, stamp::StampUnmerge)?;
    register_step(&mut builder, qr::QrSideSelect)?;
    Ok(Box::new(builder.finalize(pasta::baked())?))
}

fn register_step<S: Step<Pasta> + 'static>(
    builder: &mut ApplicationBuilder<'static, Pasta, ProductionRank, HEADER_SIZE>,
    step: S,
) -> ragu_core::Result<()> {
    *builder = mem::take(builder).register(step)?;
    Ok(())
}

lazy_static! {
    /// Fixed by the baked parameters and production rank, independently of PCD setup.
    static ref EMPTY_STAMP_BRIDGE_HASH: TachygramSetBridge = {
        #[expect(clippy::expect_used, reason = "the fixed setup has finite bridge generators")]
        TachygramSetCommit::default().bridge().expect("valid constant-one bridge hash")
    };
}

#[cfg(test)]
mod tests;
