//! Tachyon Poseidon digests.
//!
//! Each named function provides one protocol-defined hash.
//!
//! A tagged hash starts from a zero rate and the capacity element
//! $\mathsf{tag}$, the 16-byte domain read as a little-endian integer. It
//! absorbs only its data. Every Tachyon Poseidon hash is tagged this way.

use core::array;

use ragu_core::{
    PoseidonPermutation as _, Result,
    drivers::emulator::{Emulator, Wireless},
    maybe::{Always, Maybe as _},
    pasta::PoseidonFp,
};
use ragu_primitives::{Element, poseidon::Sponge};
use udon::curve::Affine as _;

use crate::{
    constants::EVIDENCE_TREE_ARITY,
    pasta::{EpAffine, Fp},
};

/// The wireless emulator that evaluates the real in-circuit sponge natively:
/// witness values are always present and no wires are tracked, so absorb and
/// squeeze compute field values without building constraints.
type Emu = Emulator<Wireless<Always<()>, Fp>>;

#[expect(
    clippy::expect_used,
    reason = "sponge squeeze cannot fail in wireless `Always` mode"
)]
fn squeeze(emulator: &mut Emu, sponge: &mut Sponge<'static, Emu, PoseidonFp>) -> Fp {
    let squeezed = sponge.squeeze(emulator).expect("infallible");
    *squeezed.value().take()
}

fn native_sponge<const L: usize>(
    input: [Fp; L],
    build: impl FnOnce(
        &mut Emu,
        [&Element<'static, Emu>; L],
    ) -> Result<Sponge<'static, Emu, PoseidonFp>>,
) -> (Emu, Sponge<'static, Emu, PoseidonFp>) {
    let mut emulator = Emu::execute();
    let elements = input.map(|value| Element::constant(&mut emulator, value));
    #[expect(
        clippy::expect_used,
        reason = "sponge absorb cannot fail in wireless `Always` mode"
    )]
    let sponge = build(&mut emulator, elements.each_ref()).expect("infallible");
    (emulator, sponge)
}

fn hash<const L: usize>(
    input: [Fp; L],
    build: impl FnOnce(
        &mut Emu,
        [&Element<'static, Emu>; L],
    ) -> Result<Sponge<'static, Emu, PoseidonFp>>,
) -> Fp {
    let (mut emulator, mut sponge) = native_sponge(input, build);
    squeeze(&mut emulator, &mut sponge)
}

const FEE_BLIND_DOMAIN: &[u8; 16] = b"Tachyon-FeeBlind";

/// The feemax blind, the trapdoor of $\mathsf{cv}_\mathsf{feemax}$,
/// $r = \mathsf{Poseidon}_\texttt{Tachyon-FeeBlind}(\mathsf{pk}, \psi,
/// \mathsf{rcm})$.
#[must_use]
pub fn feemax_blind(pk: Fp, psi: Fp, rcm: Fp) -> Fp {
    hash(
        [pk, psi, rcm],
        |dr, [pk_element, psi_element, rcm_element]| {
            with_sponge::feemax_blind(dr, pk_element, psi_element, rcm_element)
        },
    )
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
    hash(
        [x, y, Fp::from(fee)],
        |dr, [x_element, y_element, fee_element]| {
            with_sponge::fee_digest(dr, (x_element, y_element), fee_element)
        },
    )
}

const ACTION_DIGEST_DOMAIN: &[u8; 16] = b"Tachyon-ActionDg";

/// Derives an action digest from action fields.
///
/// # Panics
///
/// Panics if `cv` or `rk` is the identity.
#[must_use]
pub fn action_digest(cv: EpAffine, rk: EpAffine) -> Fp {
    #[expect(clippy::expect_used, reason = "callers reject the identity")]
    let (cv_x, cv_y) = cv.coordinates().expect("cv must not be the identity");
    #[expect(clippy::expect_used, reason = "callers reject the identity")]
    let (rk_x, rk_y) = rk.coordinates().expect("rk must not be the identity");
    hash(
        [cv_x, cv_y, rk_x, rk_y],
        |dr, [cv_x_element, cv_y_element, rk_x_element, rk_y_element]| {
            with_sponge::action_digest(
                dr,
                (cv_x_element, cv_y_element),
                (rk_x_element, rk_y_element),
            )
        },
    )
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
    hash([x, y, nk], |dr, [x_element, y_element, nk_element]| {
        with_sponge::payment_key(dr, (x_element, y_element), nk_element)
    })
}

const NOTE_COMMITMENT_DOMAIN: &[u8; 16] = b"Tachyon-CmDerive";

/// Derives a note commitment from note fields.
#[must_use]
pub fn note_commitment(rcm: Fp, pk: Fp, value: u64, psi: Fp) -> Fp {
    hash(
        [rcm, pk, Fp::from(value), psi],
        |dr, [rcm_element, pk_element, value_element, psi_element]| {
            with_sponge::note_commitment(dr, rcm_element, pk_element, value_element, psi_element)
        },
    )
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
    hash(
        [rcm, pk, Fp::from(value), psi],
        |dr, [rcm_element, pk_element, value_element, psi_element]| {
            with_sponge::pad_tachygram(dr, rcm_element, pk_element, value_element, psi_element)
        },
    )
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
    hash([psi, nk], |dr, [psi_element, nk_element]| {
        with_sponge::nf_master(dr, psi_element, nk_element)
    })
}

const SPEND_ALPHA_DOMAIN: &[u8; 16] = b"Tachyon-Spend\0\0\0";

/// Derives a spend's $\alpha$ preimage from its entropy and note commitment.
///
/// $$
///   \mathsf{Poseidon}_\texttt{Tachyon-Spend}(\theta,\ \mathsf{cm})
/// $$
#[must_use]
pub fn alpha_spend(theta: Fp, cm: Fp) -> Fp {
    hash([theta, cm], |dr, [theta_element, cm_element]| {
        with_sponge::alpha_spend(dr, theta_element, cm_element)
    })
}

const OUTPUT_ALPHA_DOMAIN: &[u8; 16] = b"Tachyon-Output\0\0";

/// Derives an output's $\alpha$ preimage from its entropy and note commitment.
///
/// $$
///   \mathsf{Poseidon}_\texttt{Tachyon-Output}(\theta,\ \mathsf{cm})
/// $$
#[must_use]
pub fn alpha_output(theta: Fp, cm: Fp) -> Fp {
    hash([theta, cm], |dr, [theta_element, cm_element]| {
        with_sponge::alpha_output(dr, theta_element, cm_element)
    })
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
    let (mut emulator, mut sponge) = native_sponge(
        [mk, epoch_start],
        |dr, [mk_element, epoch_start_element]| {
            with_sponge::nullifier_group(dr, mk_element, epoch_start_element)
        },
    );
    array::from_fn(|_| squeeze(&mut emulator, &mut sponge))
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
    let (x, y) = stamp_hash
        .coordinates()
        .expect("bridge hash must not be the identity point");
    hash(
        [anchor_prev, epoch, x, y],
        |dr, [anchor_prev_element, epoch_element, x_element, y_element]| {
            with_sponge::anchor_next_stamp(
                dr,
                anchor_prev_element,
                epoch_element,
                &[x_element.clone(), y_element.clone()],
            )
        },
    )
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
    let (contents_x, contents_y) = contents
        .coordinates()
        .expect("bridge hash must not be the identity point");
    hash(
        [
            epoch,
            anchor_start,
            anchor_next,
            discriminant,
            depth,
            bits,
            contents_x,
            contents_y,
        ],
        |dr,
         [
            epoch_element,
            anchor_start_element,
            anchor_next_element,
            discriminant_element,
            depth_element,
            bits_element,
            contents_x_element,
            contents_y_element,
        ]| {
            with_sponge::evidence_tree_leaf(
                dr,
                epoch_element,
                anchor_start_element,
                anchor_next_element,
                discriminant_element,
                (depth_element, bits_element),
                &[contents_x_element.clone(), contents_y_element.clone()],
            )
        },
    )
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
    hash(children, |dr, children_elements| {
        with_sponge::evidence_tree_node(dr, &children_elements.map(Clone::clone))
    })
}

const ANCHOR_EPOCH_DOMAIN: &[u8; 16] = b"Tachyon-AnchorEp";

/// Computes the boundary digest of `anchor_prev` into `epoch`.
///
/// Produces the entry anchor of `epoch` when `anchor_prev` is the final
/// anchor of the epoch before.
#[must_use]
pub fn anchor_next_epoch(anchor_prev: Fp, epoch: Fp) -> Fp {
    hash(
        [anchor_prev, epoch],
        |dr, [anchor_prev_element, epoch_element]| {
            with_sponge::anchor_next_epoch(dr, anchor_prev_element, epoch_element)
        },
    )
}

/// Builds domain-tagged sponges and absorbs protocol inputs.
/// The caller performs every squeeze.
pub(crate) mod with_sponge {
    use ragu_core::{
        Cycle as _, PoseidonPermutation as _, Result,
        drivers::Driver,
        pasta::{Pasta, PoseidonFp},
    };
    use ragu_primitives::{
        Element,
        poseidon::{Sponge, SpongeState},
        vec::FixedVec,
    };
    use udon::field::Field as _;

    use super::{
        ACTION_DIGEST_DOMAIN, ANCHOR_EPOCH_DOMAIN, ANCHOR_STAMP_DOMAIN, EVIDENCE_NODE_DOMAIN,
        FEE_BLIND_DOMAIN, FEE_DIGEST_DOMAIN, NOTE_COMMITMENT_DOMAIN, NULLIFIER_DOMAIN,
        NULLIFIER_MASTER_DOMAIN, OUTPUT_ALPHA_DOMAIN, PAD_COMMITMENT_DOMAIN, PAYMENT_KEY_DOMAIN,
        QR_BUCKET_DOMAIN, SPEND_ALPHA_DOMAIN,
    };
    use crate::{constants::EVIDENCE_TREE_ARITY, pasta, pasta::Fp};

    fn absorb<'dr, D: Driver<'dr, F = Fp>, const L: usize>(
        dr: &mut D,
        mut sponge: Sponge<'dr, D, PoseidonFp>,
        input: [&Element<'dr, D>; L],
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        for value in input {
            sponge.absorb(dr, value)?;
        }
        Ok(sponge)
    }

    pub(crate) fn feemax_blind<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        pk: &Element<'dr, D>,
        psi: &Element<'dr, D>,
        rcm: &Element<'dr, D>,
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*FEE_BLIND_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [pk, psi, rcm])
    }

    pub(crate) fn fee_digest<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        cv: (&Element<'dr, D>, &Element<'dr, D>),
        fee: &Element<'dr, D>,
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*FEE_DIGEST_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [cv.0, cv.1, fee])
    }

    pub(crate) fn action_digest<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        cv: (&Element<'dr, D>, &Element<'dr, D>),
        rk: (&Element<'dr, D>, &Element<'dr, D>),
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*ACTION_DIGEST_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [cv.0, cv.1, rk.0, rk.1])
    }

    pub(crate) fn payment_key<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        ak: (&Element<'dr, D>, &Element<'dr, D>),
        nk: &Element<'dr, D>,
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*PAYMENT_KEY_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [ak.0, ak.1, nk])
    }

    pub(crate) fn note_commitment<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        rcm: &Element<'dr, D>,
        pk: &Element<'dr, D>,
        value: &Element<'dr, D>,
        psi: &Element<'dr, D>,
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*NOTE_COMMITMENT_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let initial = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, initial)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [rcm, pk, value, psi])
    }

    pub(crate) fn pad_tachygram<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        rcm: &Element<'dr, D>,
        pk: &Element<'dr, D>,
        value: &Element<'dr, D>,
        psi: &Element<'dr, D>,
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*PAD_COMMITMENT_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let initial = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, initial)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [rcm, pk, value, psi])
    }

    pub(crate) fn nf_master<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        psi: &Element<'dr, D>,
        nk: &Element<'dr, D>,
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*NULLIFIER_MASTER_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [psi, nk])
    }

    pub(crate) fn alpha_spend<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        theta: &Element<'dr, D>,
        cm: &Element<'dr, D>,
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*SPEND_ALPHA_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [theta, cm])
    }

    pub(crate) fn alpha_output<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        theta: &Element<'dr, D>,
        cm: &Element<'dr, D>,
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*OUTPUT_ALPHA_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [theta, cm])
    }

    pub(crate) fn nullifier_group<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        master: &Element<'dr, D>,
        epoch_start: &Element<'dr, D>,
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*NULLIFIER_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [master, epoch_start])
    }

    pub(crate) fn anchor_next_stamp<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        anchor_prev: &Element<'dr, D>,
        epoch: &Element<'dr, D>,
        bridge_hash: &[Element<'dr, D>; 2],
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*ANCHOR_STAMP_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(
            dr,
            sponge,
            [anchor_prev, epoch, &bridge_hash[0], &bridge_hash[1]],
        )
    }

    pub(crate) fn anchor_next_epoch<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        anchor_prev: &Element<'dr, D>,
        epoch: &Element<'dr, D>,
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*ANCHOR_EPOCH_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, [anchor_prev, epoch])
    }

    pub(crate) fn evidence_tree_leaf<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        epoch: &Element<'dr, D>,
        anchor_start: &Element<'dr, D>,
        anchor_next: &Element<'dr, D>,
        discriminant: &Element<'dr, D>,
        profile: (&Element<'dr, D>, &Element<'dr, D>),
        bridge_hash: &[Element<'dr, D>; 2],
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*QR_BUCKET_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(
            dr,
            sponge,
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
        )
    }

    pub(crate) fn evidence_tree_node<'dr, D: Driver<'dr, F = Fp>>(
        dr: &mut D,
        children: &[Element<'dr, D>; EVIDENCE_TREE_ARITY],
    ) -> Result<Sponge<'dr, D, PoseidonFp>> {
        let capacity = Fp::from_u128(u128::from_le_bytes(*EVIDENCE_NODE_DOMAIN));
        let state = SpongeState::from_elements(FixedVec::from_fn(|index| {
            let value = if index == PoseidonFp::RATE {
                capacity
            } else {
                Fp::ZERO
            };
            Element::constant(dr, value)
        }));
        let sponge = Sponge::resume(state, Pasta::circuit_poseidon(pasta::baked()));
        absorb(dr, sponge, children.each_ref())
    }
}
