//! Little-endian running sum decomposition.
//!
//! Decomposes an $n$-bit field element $\alpha$ into $W$ windows, each window
//! being a $K$-bit word, using a running sum $z$.
//! We constrain $K \leq 3$ for this helper.
//!     $$\alpha = k_0 + (2^K) k_1 + (2^{2K}) k_2 + ... + (2^{(W-1)K}) k_{W-1}$$
//! $z_0$ is initialized as $\alpha$. Each successive $z_{i+1}$ is computed as
//!                $$z_{i+1} = (z_{i} - k_i) / (2^K).$$
//! $z_W$ is constrained to be zero in `strict` mode.
//! The difference between each interstitial running sum output is constrained
//! to be $K$ bits, i.e.
//!                      `range_check`($k_i$, $2^K$),
//! where
//! ```text
//!   range_check(word, range)
//!     = word * (1 - word) * (2 - word) * ... * ((range - 1) - word)
//! ```
//!
//! Given that the `range_check` constraint will be toggled by a selector, in
//! practice we will have a `selector * range_check(word, range)` expression
//! of degree `range + 1`.
//!
//! This means that $2^K$ has to be at most `degree_bound - 1` in order for
//! the range check constraint to stay within the degree bound.

use ff::PrimeFieldBits;
use halo2_proofs::{
    circuit::{AssignedCell, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};

use super::{decompose_element_le, range_check, RunningSumConfig, Window};
use pasta_curves::arithmetic::FieldExt;
use std::{convert::TryInto, marker::PhantomData};

/// The running sum decomposition in little-endian windows.
#[derive(Clone, Debug)]
pub struct RunningSum<F, const W: usize>
where
    F: FieldExt + PrimeFieldBits,
{
    /// $z_0$, the original value decomposed by this helper.
    value: AssignedCell<F, F>,
    /// The windows [z_1, ..., z_W]. If created in strict mode, $z_W = 0$.
    windows: [AssignedCell<F, F>; W],
}

impl<F, const W: usize> RunningSum<F, W>
where
    F: FieldExt + PrimeFieldBits,
{
    /// The original value that was decomposed.
    pub fn value(&self) -> &AssignedCell<F, F> {
        &self.value
    }

    /// The windows of the running sum decomposition.
    pub fn windows(&self) -> &[AssignedCell<F, F>; W] {
        &self.windows
    }
}

/// Config for little-endian running sum decomposition.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Config<F, const WINDOW_NUM_BITS: usize>(RunningSumConfig<F, WINDOW_NUM_BITS>)
where
    F: FieldExt + PrimeFieldBits;
impl<F: FieldExt, const WINDOW_NUM_BITS: usize> std::ops::Deref for Config<F, WINDOW_NUM_BITS>
where
    F: FieldExt + PrimeFieldBits,
{
    type Target = RunningSumConfig<F, WINDOW_NUM_BITS>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F, const WINDOW_NUM_BITS: usize> Config<F, WINDOW_NUM_BITS>
where
    F: FieldExt + PrimeFieldBits,
{
    /// Returns the q_range_check selector of this [`RunningSumConfig`].
    pub(crate) fn q_range_check(&self) -> Selector {
        self.q_range_check
    }

    /// The advice column `z` MUST be equality-enabled.
    ///
    /// # Panics
    ///
    /// Panics if WINDOW_NUM_BITS > 3.
    ///
    /// # Side-effects
    ///
    /// `z` will be equality-enabled.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_range_check: Selector,
        z: Column<Advice>,
    ) -> Self {
        assert!(WINDOW_NUM_BITS <= 3);

        meta.enable_equality(z);

        let config = RunningSumConfig {
            q_range_check,
            z,
            _marker: PhantomData,
        };

        meta.create_gate("range check", |meta| {
            let q_range_check = meta.query_selector(config.q_range_check);
            let z_cur = meta.query_advice(config.z, Rotation::cur());
            let z_next = meta.query_advice(config.z, Rotation::next());
            //    z_i = 2^{K}⋅z_{i + 1} + k_i
            // => k_i = z_i - 2^{K}⋅z_{i + 1}
            let word = z_cur - z_next * F::from(1 << WINDOW_NUM_BITS);

            vec![q_range_check * range_check(word, 1 << WINDOW_NUM_BITS)]
        });

        Self(config)
    }

    /// Decompose a field element alpha that is witnessed in this helper.
    ///
    /// `strict` = true constrains the final running sum to be zero, i.e.
    /// constrains alpha to be within WINDOW_NUM_BITS * num_windows bits.
    pub fn witness_decompose<const WORD_NUM_BITS: usize, const NUM_WINDOWS: usize>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        alpha: Option<F>,
        strict: bool,
    ) -> Result<RunningSum<F, NUM_WINDOWS>, Error> {
        let z_0 = region.assign_advice(
            || "z_0 = alpha",
            self.z,
            offset,
            || alpha.ok_or(Error::Synthesis),
        )?;
        self.decompose::<WORD_NUM_BITS, NUM_WINDOWS>(region, offset, z_0, strict)
    }

    /// Decompose an existing variable alpha that is copied into this helper.
    ///
    /// `strict` = true constrains the final running sum to be zero, i.e.
    /// constrains alpha to be within WINDOW_NUM_BITS * num_windows bits.
    pub fn copy_decompose<const WORD_NUM_BITS: usize, const NUM_WINDOWS: usize>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        alpha: AssignedCell<F, F>,
        strict: bool,
    ) -> Result<RunningSum<F, NUM_WINDOWS>, Error> {
        let z_0 = alpha.copy_advice(|| "copy z_0 = alpha", region, self.z, offset)?;
        self.decompose::<WORD_NUM_BITS, NUM_WINDOWS>(region, offset, z_0, strict)
    }

    /// `z_0` must be the cell at `(self.z, offset)` in `region`.
    ///
    /// # Panics
    ///
    /// Panics if there are too many windows for the given word size.
    fn decompose<const WORD_NUM_BITS: usize, const NUM_WINDOWS: usize>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        z_0: AssignedCell<F, F>,
        strict: bool,
    ) -> Result<RunningSum<F, NUM_WINDOWS>, Error> {
        // Make sure that we do not have more windows than required for the number
        // of bits in the word. In other words, every window must contain at least
        // one bit of the word (no empty windows).
        //
        // For example, let:
        //      - WORD_NUM_BITS = 64
        //      - WINDOW_NUM_BITS = 3
        // In this case, the maximum allowed num_windows is 22:
        //                    3 * 22 < 64 + 3
        //
        assert!(WINDOW_NUM_BITS * NUM_WINDOWS < WORD_NUM_BITS + WINDOW_NUM_BITS);

        // Enable selectors
        for idx in 0..NUM_WINDOWS {
            self.q_range_check.enable(region, offset + idx)?;
        }

        // Decompose base field element into little-endian K-bit words.
        let words: Vec<Option<Window<WINDOW_NUM_BITS>>> = {
            let words = z_0
                .value()
                .map(|word| decompose_element_le::<F, WORD_NUM_BITS, WINDOW_NUM_BITS>(word));

            if let Some(words) = words {
                words.into_iter().map(Some).collect()
            } else {
                vec![None; NUM_WINDOWS]
            }
        };

        // Initialize empty vector to store running sum values [z_0, ..., z_W].
        let mut zs: Vec<AssignedCell<F, F>> = vec![z_0.clone()];
        let mut z = z_0;

        // Assign running sum `z_{i+1}` = (z_i - k_i) / (2^K) for i = 0..=n-1.
        // Outside of this helper, z_0 = alpha must have already been loaded into the
        // `z` column at `offset`.
        let two_pow_k_inv = F::from(1 << WINDOW_NUM_BITS as u64).invert().unwrap();
        for (i, word) in words.iter().enumerate() {
            // z_next = (z_cur - word) / (2^K)
            let z_next = {
                let word: Option<F> = word.map(|word| word.value_field());
                let z_next_val = z
                    .value()
                    .zip(word)
                    .map(|(z_cur_val, word)| (*z_cur_val - word) * two_pow_k_inv);
                region.assign_advice(
                    || format!("z_{:?}", i + 1),
                    self.z,
                    offset + i + 1,
                    || z_next_val.ok_or(Error::Synthesis),
                )?
            };

            // Update `z`.
            z = z_next;
            zs.push(z.clone());
        }
        assert_eq!(zs.len(), NUM_WINDOWS + 1);

        if strict {
            // Constrain the final running sum output to be zero.
            region.constrain_constant(zs.last().unwrap().cell(), F::zero())?;
        }

        Ok(RunningSum {
            value: zs[0].clone(),
            windows: zs[1..].to_vec().try_into().unwrap(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use group::ff::{Field, PrimeField};
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure},
        plonk::{Any, Circuit, ConstraintSystem, Error},
    };
    use pasta_curves::{arithmetic::FieldExt, pallas};
    use proptest::prelude::*;
    use rand::rngs::OsRng;

    use crate::ecc::chip::{
        FIXED_BASE_WINDOW_SIZE, L_SCALAR_SHORT as L_SHORT, NUM_WINDOWS, NUM_WINDOWS_SHORT,
    };

    const L_BASE: usize = pallas::Base::NUM_BITS as usize;

    #[test]
    fn test_running_sum_le() {
        struct MyCircuit<
            F: FieldExt + PrimeFieldBits,
            const WORD_NUM_BITS: usize,
            const WINDOW_NUM_BITS: usize,
            const NUM_WINDOWS: usize,
        > {
            alpha: Option<F>,
            strict: bool,
        }

        impl<
                F: FieldExt + PrimeFieldBits,
                const WORD_NUM_BITS: usize,
                const WINDOW_NUM_BITS: usize,
                const NUM_WINDOWS: usize,
            > Circuit<F> for MyCircuit<F, WORD_NUM_BITS, WINDOW_NUM_BITS, NUM_WINDOWS>
        {
            type Config = Config<F, WINDOW_NUM_BITS>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self {
                    alpha: None,
                    strict: self.strict,
                }
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let z = meta.advice_column();
                let q_range_check = meta.selector();
                let constants = meta.fixed_column();
                meta.enable_constant(constants);

                Config::<F, WINDOW_NUM_BITS>::configure(meta, q_range_check, z)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                layouter.assign_region(
                    || "decompose",
                    |mut region| {
                        let offset = 0;
                        let zs = config.witness_decompose::<WORD_NUM_BITS, NUM_WINDOWS>(
                            &mut region,
                            offset,
                            self.alpha,
                            self.strict,
                        )?;
                        let alpha = zs.value().clone();

                        let offset = offset + NUM_WINDOWS + 1;

                        config.copy_decompose::<WORD_NUM_BITS, NUM_WINDOWS>(
                            &mut region,
                            offset,
                            alpha,
                            self.strict,
                        )?;

                        Ok(())
                    },
                )
            }
        }

        // Random base field element
        {
            let alpha = pallas::Base::random(OsRng);

            // Strict full decomposition should pass.
            let circuit: MyCircuit<pallas::Base, L_BASE, FIXED_BASE_WINDOW_SIZE, { NUM_WINDOWS }> =
                MyCircuit {
                    alpha: Some(alpha),
                    strict: true,
                };
            let prover = MockProver::<pallas::Base>::run(8, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), Ok(()));
        }

        // Random 64-bit word
        {
            let alpha = pallas::Base::from(rand::random::<u64>());

            // Strict full decomposition should pass.
            let circuit: MyCircuit<
                pallas::Base,
                L_SHORT,
                FIXED_BASE_WINDOW_SIZE,
                { NUM_WINDOWS_SHORT },
            > = MyCircuit {
                alpha: Some(alpha),
                strict: true,
            };
            let prover = MockProver::<pallas::Base>::run(8, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), Ok(()));
        }

        // 2^66
        {
            let alpha = pallas::Base::from_u128(1 << 66);

            // Strict partial decomposition should fail.
            let circuit: MyCircuit<
                pallas::Base,
                L_SHORT,
                FIXED_BASE_WINDOW_SIZE,
                { NUM_WINDOWS_SHORT },
            > = MyCircuit {
                alpha: Some(alpha),
                strict: true,
            };
            let prover = MockProver::<pallas::Base>::run(8, &circuit, vec![]).unwrap();
            assert_eq!(
                prover.verify(),
                Err(vec![
                    VerifyFailure::Permutation {
                        column: (Any::Fixed, 0).into(),
                        row: 0
                    },
                    VerifyFailure::Permutation {
                        column: (Any::Fixed, 0).into(),
                        row: 1
                    },
                    VerifyFailure::Permutation {
                        column: (Any::Advice, 0).into(),
                        row: 22
                    },
                    VerifyFailure::Permutation {
                        column: (Any::Advice, 0).into(),
                        row: 45
                    },
                ])
            );

            // Non-strict partial decomposition should pass.
            let circuit: MyCircuit<
                pallas::Base,
                { L_SHORT },
                FIXED_BASE_WINDOW_SIZE,
                { NUM_WINDOWS_SHORT },
            > = MyCircuit {
                alpha: Some(alpha),
                strict: false,
            };
            let prover = MockProver::<pallas::Base>::run(8, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), Ok(()));
        }
    }

    prop_compose! {
        fn arb_scalar()(bytes in prop::array::uniform32(0u8..)) -> pallas::Scalar {
            // Instead of rejecting out-of-range bytes, let's reduce them.
            let mut buf = [0; 64];
            buf[..32].copy_from_slice(&bytes);
            pallas::Scalar::from_bytes_wide(&buf)
        }
    }

    proptest! {
        #[test]
        fn test_decompose_element_le(
            scalar in arb_scalar(),
        ) {
            fn test_inner<const WINDOW_NUM_BITS: usize>(scalar: pallas::Scalar)  {
                // Get decomposition into `WINDOW_NUM_BITS` little-endian windows
                let decomposed = decompose_element_le::<_, {pallas::Scalar::NUM_BITS as usize}, {WINDOW_NUM_BITS}>(&scalar);

                // Flatten bits
                let bits = decomposed.into_iter().flat_map(|window|window.0.to_vec());

                // Pad or truncate bits to 32 bytes
                let bits: Vec<bool> = bits.chain(std::iter::repeat(false)).take(32*8).collect();

                let bytes: Vec<u8> = bits.chunks_exact(8).map(|chunk| chunk.iter().rev().fold(0, |acc, &b| (acc << 1) + (b as u8))).collect();

                // Check that original scalar is recovered from decomposition
                assert_eq!(scalar, pallas::Scalar::from_repr(bytes.try_into().unwrap()).unwrap());
            }

            test_inner::<1>(scalar);
            test_inner::<2>(scalar);
            test_inner::<3>(scalar);
            test_inner::<4>(scalar);
            test_inner::<5>(scalar);
            test_inner::<6>(scalar);
            test_inner::<7>(scalar);
            test_inner::<8>(scalar);
        }
    }
}
