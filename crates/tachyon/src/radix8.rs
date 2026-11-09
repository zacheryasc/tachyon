//! Signed odd-digit radix-8 encoding of canonical field element bits.

use core::array;

use udon::field::Field as _;

use crate::pasta::{Fp, Fq};

/// Digits indexed by the little-endian window (sign, low, high).
pub(crate) const DIGITS: [i8; 8] = [-1, 1, -3, 3, -5, 5, -7, 7];

/// The scalar a field element $h$ denotes, read as a signed odd-digit radix-8
/// sum:
///
/// $$
///   \sum_{i=0}^{84} (2 s_i - 1)(1 + 2 m_i + 4 n_i) \cdot 8^i \bmod q,
/// $$
///
/// where $(s_i, m_i, n_i)$ are bits $3i$, $3i + 1$ and $3i + 2$ of the
/// canonical little-endian encoding of $h$.
#[expect(
    clippy::indexing_slicing,
    reason = "three bits index the eight signed digits"
)]
pub(crate) fn fp_to_fq(element: Fp) -> Fq {
    let bits = element
        .to_bytes()
        .map(|byte| array::from_fn::<u8, 8, _>(|shift| (byte >> shift) & 1));
    let (windows, _) = bits.as_flattened().as_chunks::<3>();
    windows
        .iter()
        .rev()
        .fold(Fq::ZERO, |acc, &[sign, low, high]| {
            let digit = DIGITS[usize::from(sign + 2 * low + 4 * high)];
            let magnitude = Fq::from(u64::from(digit.unsigned_abs()));
            acc * Fq::from(8u64) + if digit > 0 { magnitude } else { -magnitude }
        })
}

#[cfg(test)]
mod tests;
