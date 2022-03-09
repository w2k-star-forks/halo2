//! Gadget for endoscaling.

use ff::PrimeFieldBits;
use halo2_gadgets::utilities::decompose_running_sum::be;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::Error,
};
use pasta_curves::arithmetic::CurveAffine;

mod chip;
pub mod primitive;

/// Instructions to map bitstrings to and from endoscalars.
pub trait EndoscaleInstructions<C: CurveAffine>
where
    C::Base: PrimeFieldBits,
{
    /// Computes commitment (Alg 1) to a variable-length bitstring using the endoscaling
    /// algorithm.
    ///
    /// The bitstring is decomposed into pairs of bits using a running sum outside of
    /// this gadget.
    #[allow(clippy::type_complexity)]
    fn endoscale_base<L: Layouter<C::Base>, const NUM_BITS: usize, const NUM_WINDOWS: usize>(
        &self,
        layouter: L,
        base: C,
        bitstring: &be::RunningSum<C::Base, 2, NUM_WINDOWS>,
    ) -> Result<
        (
            AssignedCell<C::Base, C::Base>,
            AssignedCell<C::Base, C::Base>,
        ),
        Error,
    >;

    /// Computes endoscalar (Alg 2) mapping to a variable-length bitstring using
    /// the endoscaling algorithm.
    ///
    /// The bitstring is decomposed into windows using a running sum outside of
    /// this gadget.
    fn endoscale_scalar<
        L: Layouter<C::Base>,
        const BITSTRING_NUM_BITS: usize,
        const WINDOW_NUM_BITS: usize,
        const NUM_WINDOWS: usize,
    >(
        &self,
        layouter: L,
        bitstring: &be::RunningSum<C::Base, WINDOW_NUM_BITS, NUM_WINDOWS>,
    ) -> Result<AssignedCell<C::Base, C::Base>, Error>;

    /// Check that a witnessed bitstring corresponds to a range of endoscalars
    /// provided as public inputs.
    fn recover_bitstring<
        L: Layouter<C::Base>,
        const BITSTRING_NUM_BITS: usize,
        const WINDOW_NUM_BITS: usize,
        const NUM_WINDOWS: usize,
    >(
        &self,
        layouter: L,
        bitstring: &be::RunningSum<C::Base, WINDOW_NUM_BITS, NUM_WINDOWS>,
        pub_input_rows: [usize; NUM_WINDOWS],
    ) -> Result<(), Error>;
}
