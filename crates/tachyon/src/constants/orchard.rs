//! Orchard-derived generators shared by native code and circuit gadgets.

use group::GroupEncoding as _;
use lazy_static::lazy_static;
use pasta_curves::{arithmetic::CurveExt as _, pallas::Point};
use udon::curve::Affine as _;

use crate::pasta::{Ep, EpAffine};

/// Orchard's value-commitment domain (§5.4.8.3).
const VALUE_COMMITMENT_DOMAIN: &str = "z.cash:Orchard-cv";

/// Orchard's spend-authorization domain, also used for Tachyon actions.
const ACTION_AUTH_DOMAIN: &str = "z.cash:Orchard";

lazy_static! {
    /// Generator $\mathcal{V}$ for value commitments.
    pub(crate) static ref VALUE_COMMIT_V: Ep = {
        #[expect(clippy::expect_used, reason = "the fixed generator has a canonical encoding")]
        EpAffine::from_bytes(Point::hash_to_curve(VALUE_COMMITMENT_DOMAIN)(b"v").to_bytes())
            .expect("valid Orchard generator")
            .to_projective()
    };

    /// Generator $\mathcal{R}$ for value commitments and binding signatures.
    pub(crate) static ref VALUE_COMMIT_R: Ep = {
        #[expect(clippy::expect_used, reason = "the fixed generator has a canonical encoding")]
        EpAffine::from_bytes(Point::hash_to_curve(VALUE_COMMITMENT_DOMAIN)(b"r").to_bytes())
            .expect("valid Orchard generator")
            .to_projective()
    };

    /// Orchard RedPallas action-authorizing generator.
    pub(crate) static ref ACTION_AUTH_GENERATOR: Ep = {
        #[expect(clippy::expect_used, reason = "the fixed generator has a canonical encoding")]
        EpAffine::from_bytes(Point::hash_to_curve(ACTION_AUTH_DOMAIN)(b"G").to_bytes())
            .expect("valid Orchard generator")
            .to_projective()
    };
}

#[cfg(test)]
mod tests {
    use udon::field::Field as _;

    use super::*;
    use crate::{keys::public::ActionVerificationKey, pasta::Fq, reddsa};

    #[test]
    fn action_auth_generator_matches_reddsa() {
        let scalar_one =
            reddsa::SigningKey::<reddsa::ActionAuth>::try_from(Fq::ONE.to_bytes()).unwrap();
        let expected = EpAffine::from(ActionVerificationKey(reddsa::VerificationKey::from(
            &scalar_one,
        )));
        assert_eq!(*ACTION_AUTH_GENERATOR, expected.to_projective());
    }
}
