//! Primitives used in endoscaling.

use group::{Curve, Group};
use pasta_curves::arithmetic::{CurveAffine, FieldExt};

use std::collections::{BTreeMap, BTreeSet};
use std::convert::TryInto;
use subtle::CtOption;

/// Lookup table mapping endoscalars to their corresponding K-bit representations.
#[allow(dead_code)]
#[allow(clippy::type_complexity)]
fn lookup_table<F: FieldExt, const K: usize, const N: usize>(
) -> ([([bool; K], F); N], BTreeMap<F, [bool; K]>) {
    assert_eq!(1 << K, N);

    let mut endoscalars = BTreeSet::new();
    let mut table = Vec::new();
    let mut inv_table = BTreeMap::new();
    let num_rows = 1 << K;

    for row in 0..num_rows {
        let bits = i2lebsp(row as u64);
        let scalar = endoscale_scalar(F::zero(), &bits);

        assert!(endoscalars.insert(scalar));

        table.push((bits, scalar));
        inv_table.insert(scalar, bits);
    }

    (table.try_into().unwrap(), inv_table)
}

/// Maps a pair of bits to a multiple of a scalar using endoscaling.
pub(crate) fn endoscale_pair_scalar<F: FieldExt>(bits: (bool, bool)) -> F {
    // [2 * bits.0 - 1]
    let mut scalar = F::from(bits.0).double() - F::one();

    if bits.1 {
        scalar *= F::ZETA;
    }

    scalar
}

/// Maps a K-bit bitstring to a scalar.
///
/// This corresponds to Algorithm 1 from [BGH2019], where `F` corresponds to $F_q$, the
/// scalar field of $P$. Where Algorithm 1 computes $Acc = [scalar] P$, this function
/// computes `scalar`.
///
/// [BGH2019]: https://eprint.iacr.org/2019/1021.pdf
#[allow(dead_code)]
pub(crate) fn endoscale_scalar<F: FieldExt>(acc: F, bits: &[bool]) -> F {
    assert_eq!(bits.len() % 2, 0);

    let mut acc = acc;
    for j in 0..(bits.len() / 2) {
        let pair = (bits[2 * j], bits[2 * j + 1]);
        acc = endoscale_pair_scalar::<F>(pair) + acc.double();
    }
    acc
}

/// Maps an arbitrary-length bitstring to an endoscalar. Uses zero padding if necessary.
#[allow(dead_code)]
pub(crate) fn endoscale_scalar_with_lookup<F: FieldExt, const K: usize>(bits: &[bool]) -> F {
    assert_eq!(bits.len() % K, 0);

    let mut acc = (F::ZETA + F::one()).double();
    for chunk_idx in 0..(bits.len() / K) {
        let idx = chunk_idx * K;
        acc = endoscale_scalar(acc, &bits[idx..(idx + K)]);
    }
    acc
}

/// Maps a pair of bits to a multiple of a base using endoscaling.
pub(crate) fn endoscale_pair<C: CurveAffine>(bits: (bool, bool), base: C) -> CtOption<C> {
    let mut base = {
        let base = base.coordinates();
        (*base.unwrap().x(), *base.unwrap().y())
    };
    if bits.0 {
        base.1 = -base.1;
    }

    if bits.1 {
        base.0 *= C::Base::ZETA;
    }

    C::from_xy(base.0, base.1)
}

/// Maps a K-bit bitstring to a multiple of a given base.
///
/// This is Algorithm 1 from [BGH2019](https://eprint.iacr.org/2019/1021.pdf).
#[allow(dead_code)]
pub(crate) fn endoscale<C: CurveAffine, const K: usize>(
    bits: [bool; K],
    base: C,
) -> (C::Base, C::Base) {
    assert_eq!(K % 2, 0);

    // Initialise accumulator to [2](φ(P) + P)
    let mut acc = base.to_curve() + base * C::Scalar::ZETA;

    for j in 0..(K / 2) {
        let pair = (bits[2 * j], bits[2 * j + 1]);
        let endo = endoscale_pair::<C>(pair, base);
        acc = acc.double();
        acc += endo.unwrap();
    }

    let acc = acc.to_affine().coordinates();
    (*acc.unwrap().x(), *acc.unwrap().y())
}

#[allow(dead_code)]
pub(crate) fn i2lebsp<const NUM_BITS: usize>(int: u64) -> [bool; NUM_BITS] {
    assert!(NUM_BITS <= 64);

    fn gen_const_array<Output: Copy + Default, const LEN: usize>(
        closure: impl FnMut(usize) -> Output,
    ) -> [Output; LEN] {
        fn gen_const_array_with_default<Output: Copy, const LEN: usize>(
            default_value: Output,
            mut closure: impl FnMut(usize) -> Output,
        ) -> [Output; LEN] {
            let mut ret: [Output; LEN] = [default_value; LEN];
            for (bit, val) in ret.iter_mut().zip((0..LEN).map(|idx| closure(idx))) {
                *bit = val;
            }
            ret
        }
        gen_const_array_with_default(Default::default(), closure)
    }

    gen_const_array(|mask: usize| (int & (1 << mask)) != 0)
}
