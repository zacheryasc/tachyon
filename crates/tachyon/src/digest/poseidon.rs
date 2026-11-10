//! Tachyon Poseidon digests.
//!
//! Each named function provides one protocol-defined hash.
//! The shared definitions live in [`with_driver`]; native entry points evaluate
//! those definitions on the wireless emulator.
//!
//! A tagged hash starts from a zero rate and the capacity element
//! $\mathsf{tag}$, the 16-byte domain read as a little-endian integer. It
//! absorbs only its data. Every Tachyon Poseidon hash is tagged this way.

use ragu_core::{
    Cycle as _, PoseidonPermutation as _, Result,
    drivers::{
        Driver,
        emulator::{Emulator, Wireless},
    },
    maybe::{Always, Maybe as _},
    pasta::{Pasta, PoseidonFp},
};
use ragu_primitives::{
    Element,
    poseidon::{Sponge, SpongeState},
    vec::FixedVec,
};
use udon::{curve::Affine as _, field::Field as _};

use crate::{
    constants::EVIDENCE_TREE_ARITY,
    pasta,
    pasta::{EpAffine, Fp},
};

#[expect(
    clippy::expect_used,
    reason = "fixed protocol hashes cannot fail on the wireless emulator"
)]
fn emulate<T>(hash: impl FnOnce(&mut Emulator<Wireless<Always<()>, Fp>>) -> Result<T>) -> T {
    hash(&mut Emulator::execute()).expect("infallible")
}

/// Opens the sponge of `domain` with capacity element $\mathsf{tag}$ over a
/// zero rate, then absorbs `input`.
fn tagged_sponge<'dr, D: Driver<'dr, F = Fp>, const L: usize>(
    driver: &mut D,
    domain: &[u8; 16],
    input: [&Element<'dr, D>; L],
) -> Result<Sponge<'dr, D, PoseidonFp>> {
    const { assert!(L > 0, "a tagged hash must absorb at least one element") };
    let capacity = Fp::from_u128(u128::from_le_bytes(*domain));

    let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
        let value = if index == PoseidonFp::RATE {
            capacity
        } else {
            Fp::ZERO
        };
        Element::constant(driver, value)
    }));
    let mut sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
    for value in input {
        sponge.absorb(driver, value)?;
    }
    Ok(sponge)
}

const FEE_BLIND_DOMAIN: &[u8; 16] = b"Tachyon-FeeBlind";

/// The feemax blind, the trapdoor of $\mathsf{cv}_\mathsf{feemax}$,
/// $r =\mathsf{Poseidon}_\texttt{Tachyon-FeeBlind}(\mathsf{pk}, \psi,
/// \mathsf{rcm})$.
#[must_use]
pub fn feemax_blind(pk: Fp, psi: Fp, rcm: Fp) -> Fp {
    *emulate(|driver| {
        let pk_element = Element::constant(driver, pk);
        let psi_element = Element::constant(driver, psi);
        let rcm_element = Element::constant(driver, rcm);
        with_driver::feemax_blind(driver, &pk_element, &psi_element, &rcm_element)
    })
    .value()
    .take()
}

const FEE_DIGEST_DOMAIN: &[u8; 16] = b"Tachyon-FeeDg\0\0\0";

/// A fee digest, $d_\mathsf{fee} = \mathsf{Poseidon}_\texttt{Tachyon-FeeDg}(
/// x(\mathsf{cv}_\mathsf{feemax}), y(\mathsf{cv}_\mathsf{feemax}),
/// \mathsf{fee})$.
///
/// # Panics
///
/// Panics if `cv_feemax` is the identity.
#[must_use]
pub fn fee_digest(cv_feemax: EpAffine, fee: u64) -> Fp {
    #[expect(clippy::expect_used, reason = "callers reject the identity")]
    let (x, y) = cv_feemax
        .coordinates()
        .expect("cv_feemax must not be the identity");
    *emulate(|driver| {
        let x_element = Element::constant(driver, x);
        let y_element = Element::constant(driver, y);
        let fee_element = Element::constant(driver, Fp::from(fee));
        with_driver::fee_digest(driver, (&x_element, &y_element), &fee_element)
    })
    .value()
    .take()
}

const ACTION_DIGEST_DOMAIN: &[u8; 16] = b"Tachyon-ActionDg";

/// Derives an action digest from action fields.
///
/// # Panics
///
/// Panics if `cv` or `rk` is the identity.
#[must_use]
#[expect(
    clippy::similar_names,
    reason = "x and y coordinate elements of each point"
)]
pub fn action_digest(cv: EpAffine, rk: EpAffine) -> Fp {
    #[expect(clippy::expect_used, reason = "callers reject the identity")]
    let (cv_x, cv_y) = cv.coordinates().expect("cv must not be the identity");
    #[expect(clippy::expect_used, reason = "callers reject the identity")]
    let (rk_x, rk_y) = rk.coordinates().expect("rk must not be the identity");
    *emulate(|driver| {
        let cv_x_element = Element::constant(driver, cv_x);
        let cv_y_element = Element::constant(driver, cv_y);
        let rk_x_element = Element::constant(driver, rk_x);
        let rk_y_element = Element::constant(driver, rk_y);
        with_driver::action_digest(
            driver,
            (&cv_x_element, &cv_y_element),
            (&rk_x_element, &rk_y_element),
        )
    })
    .value()
    .take()
}

const PAYMENT_KEY_DOMAIN: &[u8; 16] = b"Tachyon-PkDerive";

/// Derives a payment key from a spend validating key and nullifier key.
///
/// # Panics
///
/// Panics if `ak` is the identity.
#[must_use]
pub fn payment_key(ak: EpAffine, nk: Fp) -> Fp {
    #[expect(
        clippy::expect_used,
        reason = "ak = [ask]G for a PRF-derived ask is not the identity"
    )]
    let (x, y) = ak.coordinates().expect("ak must not be the identity");
    *emulate(|driver| {
        let x_element = Element::constant(driver, x);
        let y_element = Element::constant(driver, y);
        let nk_element = Element::constant(driver, nk);
        with_driver::payment_key(driver, (&x_element, &y_element), &nk_element)
    })
    .value()
    .take()
}

const NOTE_COMMITMENT_DOMAIN: &[u8; 16] = b"Tachyon-CmDerive";

/// Derives a note commitment from note fields.
#[must_use]
pub fn note_commitment(rcm: Fp, pk: Fp, value: u64, psi: Fp) -> Fp {
    *emulate(|driver| {
        let rcm_element = Element::constant(driver, rcm);
        let pk_element = Element::constant(driver, pk);
        let value_element = Element::constant(driver, Fp::from(value));
        let psi_element = Element::constant(driver, psi);
        with_driver::note_commitment(
            driver,
            &rcm_element,
            &pk_element,
            &value_element,
            &psi_element,
        )
    })
    .value()
    .take()
}

const PAD_COMMITMENT_DOMAIN: &[u8; 16] = b"Tachyon-CmOutPad";

/// Derives an output's padding tachygram from the same note fields
/// [`note_commitment`] commits to.
///
/// The preimage is the note opening rather than the commitment: both values are
/// published in one multiset, so a pad derived from $\mathsf{cm}$ would let an
/// observer pair them off and recover the output count.
#[must_use]
pub fn pad_tachygram(rcm: Fp, pk: Fp, value: u64, psi: Fp) -> Fp {
    *emulate(|driver| {
        let rcm_element = Element::constant(driver, rcm);
        let pk_element = Element::constant(driver, pk);
        let value_element = Element::constant(driver, Fp::from(value));
        let psi_element = Element::constant(driver, psi);
        with_driver::pad_tachygram(
            driver,
            &rcm_element,
            &pk_element,
            &value_element,
            &psi_element,
        )
    })
    .value()
    .take()
}

const NULLIFIER_MASTER_DOMAIN: &[u8; 16] = b"Tachyon-NfMaster";

/// Derives a note's master key from its trapdoor and the wallet nullifier key.
///
/// $$
///   \mathsf{mk} = \mathsf{Poseidon}_\texttt{Tachyon-NfMaster}(
///     \psi,\ \mathsf{nk}
///   )
/// $$
#[must_use]
pub fn nf_master(psi: Fp, nk: Fp) -> Fp {
    *emulate(|driver| {
        let psi_element = Element::constant(driver, psi);
        let nk_element = Element::constant(driver, nk);
        with_driver::nf_master(driver, &psi_element, &nk_element)
    })
    .value()
    .take()
}

const SPEND_ALPHA_DOMAIN: &[u8; 16] = b"Tachyon-Spend\0\0\0";

/// Derives a spend's $\alpha$ preimage from its entropy and note commitment.
///
/// $$
///   \mathsf{Poseidon}_\texttt{Tachyon-Spend}(\theta,\ \mathsf{cm})
/// $$
#[must_use]
pub fn alpha_spend(theta: Fp, cm: Fp) -> Fp {
    *emulate(|driver| {
        let theta_element = Element::constant(driver, theta);
        let cm_element = Element::constant(driver, cm);
        with_driver::alpha_spend(driver, &theta_element, &cm_element)
    })
    .value()
    .take()
}

const OUTPUT_ALPHA_DOMAIN: &[u8; 16] = b"Tachyon-Output\0\0";

/// Derives an output's $\alpha$ preimage from its entropy and note commitment.
///
/// $$
///   \mathsf{Poseidon}_\texttt{Tachyon-Output}(\theta,\ \mathsf{cm})
/// $$
#[must_use]
pub fn alpha_output(theta: Fp, cm: Fp) -> Fp {
    *emulate(|driver| {
        let theta_element = Element::constant(driver, theta);
        let cm_element = Element::constant(driver, cm);
        with_driver::alpha_output(driver, &theta_element, &cm_element)
    })
    .value()
    .take()
}

const NULLIFIER_DOMAIN: &[u8; 16] = b"Tachyon-NfDerive";

/// Derives the group of consecutive epoch nullifiers starting at the
/// group-aligned epoch `epoch_start` from the note's master key.
///
/// # Panics
///
/// Panics if the sponge rejects an absorb or a squeeze. The emulator is
/// native and the element count is fixed at `RATE`, so this is unreachable.
#[must_use]
pub fn nullifier_group(mk: Fp, epoch_start: Fp) -> [Fp; PoseidonFp::RATE] {
    emulate(|driver| {
        let master_element = Element::constant(driver, mk);
        let epoch_element = Element::constant(driver, epoch_start);
        with_driver::nullifier_group(driver, &master_element, &epoch_element)
    })
    .map(|element| *element.value().take())
}

const ANCHOR_STAMP_DOMAIN: &[u8; 16] = b"Tachyon-AnchorSt";

/// Advances the anchor with the stamp's epoch and tachygram-set bridge hash,
/// absorbing the point's affine coordinates.
///
/// # Panics
///
/// Panics if `stamp_hash` is the identity.
#[must_use]
#[expect(clippy::expect_used, reason = "a bridge hash is never the identity")]
pub fn anchor_next_stamp(anchor_prev: Fp, epoch: Fp, stamp_hash: EpAffine) -> Fp {
    let coordinates = <[Fp; 2]>::from(
        stamp_hash
            .coordinates()
            .expect("bridge hash must not be the identity point"),
    );
    *emulate(|driver| {
        let anchor_element = Element::constant(driver, anchor_prev);
        let epoch_element = Element::constant(driver, epoch);
        let bridge_hash = coordinates.map(|value| Element::constant(driver, value));
        with_driver::anchor_next_stamp(driver, &anchor_element, &epoch_element, &bridge_hash)
    })
    .value()
    .take()
}

const QR_BUCKET_DOMAIN: &[u8; 16] = b"Tachyon-QrBucket";
const EVIDENCE_NODE_DOMAIN: &[u8; 16] = b"Tachyon-EvidNode";

/// Digests a sealed bucket's metadata and contents bridge hash into a leaf,
/// absorbing the point's affine coordinates.
///
/// # Panics
///
/// Panics if `contents` is the identity.
#[must_use]
#[expect(clippy::expect_used, reason = "a bridge hash is never the identity")]
pub fn evidence_tree_leaf(
    epoch: Fp,
    anchor_start: Fp,
    anchor_next: Fp,
    discriminant: Fp,
    depth: Fp,
    bits: Fp,
    contents: EpAffine,
) -> Fp {
    let coordinates = <[Fp; 2]>::from(
        contents
            .coordinates()
            .expect("bridge hash must not be the identity point"),
    );
    *emulate(|driver| {
        let epoch_element = Element::constant(driver, epoch);
        let start_element = Element::constant(driver, anchor_start);
        let next_element = Element::constant(driver, anchor_next);
        let discriminant_element = Element::constant(driver, discriminant);
        let depth_element = Element::constant(driver, depth);
        let bits_element = Element::constant(driver, bits);
        let bridge_hash = coordinates.map(|value| Element::constant(driver, value));
        with_driver::evidence_tree_leaf(
            driver,
            &epoch_element,
            &start_element,
            &next_element,
            &discriminant_element,
            (&depth_element, &bits_element),
            &bridge_hash,
        )
    })
    .value()
    .take()
}

/// Folds four subtree roots into their parent node of a evidence tree.
///
/// $$
///   \mathsf{node} = \mathsf{Poseidon}_\texttt{Tachyon-EvidNode}(
///     c_0,\ c_1,\ c_2,\ c_3
///   )
/// $$
#[must_use]
pub fn evidence_tree_node(children: [Fp; EVIDENCE_TREE_ARITY]) -> Fp {
    *emulate(|driver| {
        let elements = children.map(|value| Element::constant(driver, value));
        with_driver::evidence_tree_node(driver, &elements)
    })
    .value()
    .take()
}

const ANCHOR_EPOCH_DOMAIN: &[u8; 16] = b"Tachyon-AnchorEp";

/// Computes the boundary digest of `anchor_prev` into `epoch`.
///
/// Produces the entry anchor of `epoch` when `anchor_prev` is the final
/// anchor of the epoch before.
#[must_use]
pub fn anchor_next_epoch(anchor_prev: Fp, epoch: Fp) -> Fp {
    *emulate(|driver| {
        let anchor_element = Element::constant(driver, anchor_prev);
        let epoch_element = Element::constant(driver, epoch);
        with_driver::anchor_next_epoch(driver, &anchor_element, &epoch_element)
    })
    .value()
    .take()
}

/// Protocol hash definitions shared by steps and the native emulator wrappers.
pub(crate) mod with_driver {
    use ragu_core::{PoseidonPermutation as _, Result, drivers::Driver, pasta::PoseidonFp};
    use ragu_primitives::Element;

    use super::{
        ACTION_DIGEST_DOMAIN, ANCHOR_EPOCH_DOMAIN, ANCHOR_STAMP_DOMAIN, EVIDENCE_NODE_DOMAIN,
        FEE_BLIND_DOMAIN, FEE_DIGEST_DOMAIN, NOTE_COMMITMENT_DOMAIN, NULLIFIER_DOMAIN,
        NULLIFIER_MASTER_DOMAIN, OUTPUT_ALPHA_DOMAIN, PAD_COMMITMENT_DOMAIN, PAYMENT_KEY_DOMAIN,
        QR_BUCKET_DOMAIN, SPEND_ALPHA_DOMAIN, tagged_sponge,
    };
    use crate::{constants::EVIDENCE_TREE_ARITY, pasta::Fp};

    pub(crate) fn feemax_blind<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        pk: &Element<'dr, D>,
        psi: &Element<'dr, D>,
        rcm: &Element<'dr, D>,
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, FEE_BLIND_DOMAIN, [pk, psi, rcm])?.squeeze(dr)
    }

    pub(crate) fn fee_digest<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        cv: (&Element<'dr, D>, &Element<'dr, D>),
        fee: &Element<'dr, D>,
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, FEE_DIGEST_DOMAIN, [cv.0, cv.1, fee])?.squeeze(dr)
    }

    pub(crate) fn action_digest<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        cv: (&Element<'dr, D>, &Element<'dr, D>),
        rk: (&Element<'dr, D>, &Element<'dr, D>),
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, ACTION_DIGEST_DOMAIN, [cv.0, cv.1, rk.0, rk.1])?.squeeze(dr)
    }

    pub(crate) fn payment_key<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        ak: (&Element<'dr, D>, &Element<'dr, D>),
        nk: &Element<'dr, D>,
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, PAYMENT_KEY_DOMAIN, [ak.0, ak.1, nk])?.squeeze(dr)
    }

    pub(crate) fn note_commitment<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        rcm: &Element<'dr, D>,
        pk: &Element<'dr, D>,
        value: &Element<'dr, D>,
        psi: &Element<'dr, D>,
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, NOTE_COMMITMENT_DOMAIN, [rcm, pk, value, psi])?.squeeze(dr)
    }

    pub(crate) fn pad_tachygram<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        rcm: &Element<'dr, D>,
        pk: &Element<'dr, D>,
        value: &Element<'dr, D>,
        psi: &Element<'dr, D>,
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, PAD_COMMITMENT_DOMAIN, [rcm, pk, value, psi])?.squeeze(dr)
    }

    pub(crate) fn nf_master<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        psi: &Element<'dr, D>,
        nk: &Element<'dr, D>,
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, NULLIFIER_MASTER_DOMAIN, [psi, nk])?.squeeze(dr)
    }

    pub(crate) fn alpha_spend<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        theta: &Element<'dr, D>,
        cm: &Element<'dr, D>,
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, SPEND_ALPHA_DOMAIN, [theta, cm])?.squeeze(dr)
    }

    pub(crate) fn alpha_output<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        theta: &Element<'dr, D>,
        cm: &Element<'dr, D>,
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, OUTPUT_ALPHA_DOMAIN, [theta, cm])?.squeeze(dr)
    }

    pub(crate) fn nullifier_group<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        master: &Element<'dr, D>,
        epoch_start: &Element<'dr, D>,
    ) -> Result<[Element<'dr, D>; PoseidonFp::RATE]> {
        let mut sponge = tagged_sponge(dr, NULLIFIER_DOMAIN, [master, epoch_start])?;
        Ok([
            sponge.squeeze(dr)?,
            sponge.squeeze(dr)?,
            sponge.squeeze(dr)?,
            sponge.squeeze(dr)?,
        ])
    }

    pub(crate) fn anchor_next_stamp<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        anchor_prev: &Element<'dr, D>,
        epoch: &Element<'dr, D>,
        bridge_hash: &[Element<'dr, D>; 2],
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(
            dr,
            ANCHOR_STAMP_DOMAIN,
            [anchor_prev, epoch, &bridge_hash[0], &bridge_hash[1]],
        )?
        .squeeze(dr)
    }

    pub(crate) fn anchor_next_epoch<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        anchor_prev: &Element<'dr, D>,
        epoch: &Element<'dr, D>,
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, ANCHOR_EPOCH_DOMAIN, [anchor_prev, epoch])?.squeeze(dr)
    }

    pub(crate) fn evidence_tree_leaf<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        epoch: &Element<'dr, D>,
        anchor_start: &Element<'dr, D>,
        anchor_next: &Element<'dr, D>,
        discriminant: &Element<'dr, D>,
        profile: (&Element<'dr, D>, &Element<'dr, D>),
        bridge_hash: &[Element<'dr, D>; 2],
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(
            dr,
            QR_BUCKET_DOMAIN,
            [
                epoch,
                anchor_start,
                anchor_next,
                discriminant,
                profile.0,
                profile.1,
                &bridge_hash[0],
                &bridge_hash[1],
            ],
        )?
        .squeeze(dr)
    }

    pub(crate) fn evidence_tree_node<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        children: &[Element<'dr, D>; EVIDENCE_TREE_ARITY],
    ) -> Result<Element<'dr, D>> {
        tagged_sponge(dr, EVIDENCE_NODE_DOMAIN, children.each_ref())?.squeeze(dr)
    }
}
