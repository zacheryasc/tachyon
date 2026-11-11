//! Spend nullifier-binding header and step.

extern crate alloc;

use ragu_core::{
    drivers::{Driver, DriverValue},
    gadgets::{Bound, Gadget, Kind},
    maybe::Maybe as _,
    pasta::Pasta,
};
use ragu_pcd::{
    header::{Header, Suffix},
    step::{Encoded, Index, Oracles, Step},
};
use ragu_primitives::{
    Boolean, Element, GadgetExt as _,
    allocator::Allocator,
    io::Write,
    multipack,
    vec::{ConstLen, FixedVec},
};
use udon::{curve::Affine as _, field::Field as _};

use super::{ValueCommitment, delegation::NoteSecret, spendable::NoteSpendable};
use crate::{
    constants::MAX_MONEY,
    digest::poseidon,
    gadgets::{arithmetic as circuit, fixed_base},
    keys::PaymentKey,
    note,
    nullifier::Nullifier,
    pasta::{EpAffine, Fp, Fq},
    primitives::Anchor,
    value,
};

/// Header binding a spend to its lineage note, epoch nullifier pair and value
/// commitment.
///
/// Carries the note commitment `cm`, the lineage's nullifier and its
/// neighbour `(nf_current, nf_next)` derived from the note's master key, the
/// pool `anchor`, the note's payment key `pk` and the value commitment `cv`.
/// [`SpendAction`](super::stamp::SpendAction) publishes the pair unordered,
/// ties its `ak` to `pk`, and produces `rk`.
#[derive(Debug)]
pub struct SpendHeader;

#[derive(Gadget, Write)]
pub struct SpendHeaderOutput<'dr, D: Driver<'dr>> {
    pub cm: Element<'dr, D>,
    pub nf_current: Element<'dr, D>,
    pub nf_next: Element<'dr, D>,
    pub anchor: Element<'dr, D>,
    pub pk: Element<'dr, D>,
    pub cv: ValueCommitment<'dr, D>,
}

impl Header<Fp> for SpendHeader {
    /// `(cm, nf_current, nf_next, anchor, pk, cv)`
    type Data = (
        note::Commitment,
        Nullifier,
        Nullifier,
        Anchor,
        PaymentKey,
        value::Commitment,
    );
    type Output = Kind![Fp; SpendHeaderOutput<'_, _>];

    const SUFFIX: Suffix = Suffix::new(5);

    fn encode<'dr, D: Driver<'dr, F = Fp>, A: Allocator<'dr, D>>(
        dr: &mut D,
        allocator: &mut A,
        witness: DriverValue<D, Self::Data>,
    ) -> ragu_core::Result<Bound<'dr, D, Self::Output>> {
        Ok(SpendHeaderOutput {
            cm: Element::alloc(
                dr,
                allocator,
                witness.as_ref().map(|fields| Fp::from(fields.0)),
            )?,
            nf_current: Element::alloc(
                dr,
                allocator,
                witness.as_ref().map(|fields| Fp::from(fields.1)),
            )?,
            nf_next: Element::alloc(
                dr,
                allocator,
                witness.as_ref().map(|fields| Fp::from(fields.2)),
            )?,
            anchor: Element::alloc(
                dr,
                allocator,
                witness.as_ref().map(|fields| Fp::from(fields.3)),
            )?,
            pk: Element::alloc(
                dr,
                allocator,
                witness.as_ref().map(|fields| Fp::from(fields.4)),
            )?,
            cv: ValueCommitment::alloc(dr, allocator, witness.as_ref().map(|fields| fields.5))?,
        })
    }
}

/// Derives a spend's epoch nullifier pair from the note's master key, commits
/// the note's value, and binds both to the spendable lineage.
///
/// The secret is tied to the lineage's note by `secret_cm == spendable_cm`.
/// The pair is `mk`'s nullifiers at the lineage's epoch $e$ and at $e + 1$,
/// one group sponge each. Both are emitted on the [`SpendHeader`] for the
/// action-producing step to publish, with the note's `pk` and
/// $\mathsf{cv} = \[v\]\mathcal{V} + \[\mathsf{rcv}\]\mathcal{R}$.
///
/// Two permutations (the pair) and two scalar multiplications (`cv`).
///
/// # Soundness
///
/// [`NoteSeed`](super::delegation::NoteSeed) proves that the input master key,
/// commitment and note belong together. The spendable proof supplies the epoch;
/// the circuit checks that its successor remains in range. The nullifier pair,
/// payment key and value all come from these proved inputs. Only the value
/// commitment's blinding scalar `rcv` is freely chosen.
///
/// Two sponges run whether or not $e$ and $e + 1$ share a group.
#[derive(Debug)]
pub struct SpendBind;

#[expect(
    clippy::indexing_slicing,
    clippy::missing_asserts_for_indexing,
    reason = "the epoch decomposition has exactly 32 bits"
)]
fn derive_nullifier<'dr, D: Driver<'dr, F = Fp>>(
    dr: &mut D,
    master: &Element<'dr, D>,
    epoch: &Element<'dr, D>,
) -> ragu_core::Result<Element<'dr, D>> {
    let bits = FixedVec::<_, ConstLen<32>>::try_from_fn(|index| {
        Boolean::alloc(
            dr,
            &mut (),
            epoch
                .value()
                .map(|candidate| candidate.to_le_bits().as_ref()[index]),
        )
    })?;
    multipack(dr, &bits)?[0].enforce_equal(dr, epoch)?;
    let low = &bits[0];
    let high = &bits[1];
    let twice_high = high.element().double(dr);
    let group = epoch.sub(dr, &low.element()).sub(dr, &twice_high);
    let mut sponge = poseidon::with_sponge::nullifier_group(dr, master, &group)?;
    let [first, second, third, fourth] = [
        sponge.squeeze(dr)?,
        sponge.squeeze(dr)?,
        sponge.squeeze(dr)?,
        sponge.squeeze(dr)?,
    ];
    let lower = low.conditional_select(dr, &first, &second)?;
    let upper = low.conditional_select(dr, &third, &fourth)?;
    high.conditional_select(dr, &lower, &upper)
}

impl Step<Pasta> for SpendBind {
    type Aux<'source> = ();
    type Left = NoteSpendable;
    type Output = SpendHeader;
    type Right = NoteSecret;
    /// `(rcv,)`
    type Witness<'source> = (value::Trapdoor,);

    const INDEX: Index = Index::new(8);

    fn witness<'dr, 'source: 'dr, D: Driver<'dr, F = Fp>, const HEADER_SIZE: usize>(
        &self,
        dr: &mut D,
        _oracles: &mut Oracles<'_, 'dr, D>,
        witness: DriverValue<D, Self::Witness<'source>>,
        left: DriverValue<D, <Self::Left as Header<Fp>>::Data>,
        right: DriverValue<D, <Self::Right as Header<Fp>>::Data>,
    ) -> ragu_core::Result<(
        (
            Encoded<'dr, D, Self::Left, HEADER_SIZE>,
            Encoded<'dr, D, Self::Right, HEADER_SIZE>,
            Encoded<'dr, D, Self::Output, HEADER_SIZE>,
        ),
        DriverValue<D, <Self::Output as Header<Fp>>::Data>,
        DriverValue<D, Self::Aux<'source>>,
    )>
    where
        Self: 'dr,
    {
        let left_encoded = Encoded::<D, Self::Left, HEADER_SIZE>::new(dr, &mut (), left.clone())?;
        let right_encoded =
            Encoded::<D, Self::Right, HEADER_SIZE>::new(dr, &mut (), right.clone())?;
        let cm = left_encoded.as_gadget().cm.clone();
        let secret_cm = right_encoded.as_gadget().cm.clone();
        cm.enforce_equal(dr, &secret_cm).map_err(|_err| {
            ragu_core::Error::InvalidWitness("SpendBind: secret does not match note".into())
        })?;
        let value = right_encoded.as_gadget().value.clone();
        let bound = Element::constant(dr, Fp::from(MAX_MONEY));
        let slack = bound.sub(dr, &value);
        #[expect(clippy::indexing_slicing, reason = "fixed 51-bit decomposition")]
        let slack_bits = FixedVec::<_, ConstLen<51>>::try_from_fn(|index| {
            Boolean::alloc(
                dr,
                &mut (),
                slack
                    .value()
                    .map(|candidate| candidate.to_le_bits().as_ref()[index]),
            )
        })?;
        #[expect(
            clippy::indexing_slicing,
            reason = "multipack packs 51 bits into one chunk"
        )]
        multipack(dr, &slack_bits)?[0].enforce_equal(dr, &slack)?;
        let epoch = left_encoded.as_gadget().epoch_current.clone();
        let one = Element::constant(dr, Fp::ONE);
        let next = epoch.add(dr, &one);
        circuit::EpochIndex::new(dr, &next).map_err(|_err| {
            ragu_core::Error::InvalidWitness("SpendBind: no epoch follows the spend epoch".into())
        })?;
        let nf_current = derive_nullifier(dr, &right_encoded.as_gadget().mk, &epoch)?;
        let nf_next = derive_nullifier(dr, &right_encoded.as_gadget().mk, &next)?;
        nf_current.clone().enforce_nonzero(dr).map_err(|_err| {
            ragu_core::Error::InvalidWitness("SpendBind: current-epoch nullifier is zero".into())
        })?;
        nf_next.clone().enforce_nonzero(dr).map_err(|_err| {
            ragu_core::Error::InvalidWitness("SpendBind: next-epoch nullifier is zero".into())
        })?;

        let blind_point =
            fixed_base::R_TABLE.mul_free(dr, &witness.as_ref().map(|data| Fq::from(data.0)))?;
        let cv = fixed_base::V_TABLE.mul_bounded(dr, &value, &blind_point)?;
        let [cv_x, cv_y] = cv.each_ref().map(Element::value);
        let output = D::try_just(|| {
            let (spendable_cm, _, anchor) = left.take();
            let (_, note, _) = right.take();
            let commitment = EpAffine::from_xy(*cv_x.take(), *cv_y.take()).ok_or_else(|| {
                ragu_core::Error::InvalidWitness("SpendBind: cv is not on the curve".into())
            })?;
            Ok((
                spendable_cm,
                Nullifier::from(*nf_current.value().take()),
                Nullifier::from(*nf_next.value().take()),
                anchor,
                note.pk,
                value::Commitment::from(commitment),
            ))
        })?;
        let fields = SpendHeaderOutput {
            cm,
            nf_current,
            nf_next,
            anchor: left_encoded.as_gadget().anchor.clone(),
            pk: right_encoded.as_gadget().pk.clone(),
            cv: ValueCommitment { coordinates: cv },
        };
        Ok((
            (left_encoded, right_encoded, Encoded::from_gadget(fields)),
            output,
            D::unit(),
        ))
    }
}
