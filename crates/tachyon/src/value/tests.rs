use alloc::collections::BTreeSet;

use rand::{SeedableRng as _, rngs::StdRng};

use super::*;
use crate::{
    entropy::ActionEntropy,
    fee,
    keys::{PaymentKey, private},
    note::{self, Note},
    nullifier,
    pasta::Fp,
    primitives::{ActionDigest, Anchor, effect},
    stamp::proof::{
        new_application,
        output::OutputBind,
        stamp::{FeeFuse, OutputAction},
    },
    witness,
};

#[test]
fn debug_value_trapdoor_redacts_scalar() {
    let rcv = ValueTrapdoor(Fq::from(0xFACEu64));
    assert_eq!(alloc::format!("{rcv:?}"), "ValueTrapdoor(..)");
}

#[test]
fn positive_spans_zero_to_max_money() {
    for (input, accepted) in [
        (Positive::try_from(0u64), true),
        (Positive::try_from(MAX_MONEY), true),
        (Positive::try_from(MAX_MONEY + 1), false),
        (Positive::try_from(-1i64), false),
    ] {
        assert_eq!(input.is_ok(), accepted);
    }
}

#[test]
fn fee_fuse_rejects_maximum_above_max_money() {
    let application = new_application().unwrap();
    let rng = &mut StdRng::seed_from_u64(0);
    let note = Note {
        pk: PaymentKey::from(Fp::from(11)),
        value: Positive::try_from(1u64).unwrap(),
        psi: nullifier::Trapdoor::from(Fp::from(13)),
        rcm: note::CommitmentTrapdoor::from(Fp::from(17)),
    };
    let (output, ()) = application
        .seed(rng, OutputBind, (note, ValueTrapdoor(Fq::ONE)))
        .unwrap();
    let theta = ActionEntropy(Fp::from(7));
    let (cm, pad, cv) = *output.data();
    let alpha = theta.randomizer::<effect::Output>(note.commitment());
    let digest = ActionDigest::new(
        cv,
        private::ActionSigningKey::new(&alpha).derive_action_public(),
    )
    .unwrap();
    let (actions, ()) = application
        .fuse(
            rng,
            OutputAction,
            witness::output_action((*output.data(), ()), theta, Anchor::default()),
            output,
            application.bootstrap_proof().clone().carry::<()>(()),
        )
        .unwrap();

    // Bypass Positive's cap but keep the change in range. Match the fee digest
    // to the walk's low 51 slack bits, even for field -1, so the action-set check
    // passes independently of slack reconstruction. Only that bound rejects.
    for maximum in [MAX_MONEY, MAX_MONEY + 1] {
        let fee_note = Note {
            value: Value(i64::try_from(maximum).unwrap()),
            ..note
        };
        let mut fee_witness = witness::fee_fuse(
            (*actions.data(), ()),
            fee_note,
            Positive::try_from(1u64).unwrap(),
            &BTreeSet::from([digest]),
            &BTreeSet::from([cm, pad]),
        );
        let slack = Fp::from(MAX_MONEY) - Fp::from(maximum);
        let truncated_slack = slack
            .to_le_bits()
            .as_ref()
            .iter()
            .take(51)
            .enumerate()
            .fold(0u64, |value, (index, bit)| {
                value | (u64::from(*bit) << index)
            });
        let walk_value =
            Balance::try_from(i128::from(truncated_slack) - i128::from(MAX_MONEY)).unwrap();
        let walk_digest = fee::Descriptor {
            cv_feemax: fee_note.derive_feemax_blind().commit(walk_value),
            v_fee: fee_witness.1,
        }
        .digest()
        .unwrap();
        fee_witness.2.0 = [digest, walk_digest].into_iter().collect();
        let (pcd, ()) = application
            .fuse(
                rng,
                FeeFuse,
                fee_witness,
                actions.clone(),
                application.bootstrap_proof().clone().carry::<()>(()),
            )
            .unwrap();
        assert_eq!(
            application.verify_uncompressed(&pcd, &mut *rng).unwrap(),
            maximum == MAX_MONEY,
        );
    }
}
