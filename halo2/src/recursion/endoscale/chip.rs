use super::{
    primitive::{endoscale_pair, endoscale_scalar, i2lebsp},
    EndoscaleInstructions,
};
use ff::{Field, PrimeFieldBits};
use group::Curve;
use halo2_gadgets::{
    ecc::chip::{double_and_add, witness_point},
    utilities::{bool_check, boolean::Bit, decompose_running_sum::be, UtilitiesInstructions},
};
use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Instance, Selector, TableColumn},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

/// Configuration for endoscalar table.
#[derive(Copy, Clone, Debug)]
pub(crate) struct TableConfig<F: FieldExt, const K: usize> {
    pub(in crate::recursion) bits: TableColumn,
    pub(in crate::recursion) endoscalar: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const K: usize> TableConfig<F, K> {
    #[allow(dead_code)]
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        TableConfig {
            bits: meta.lookup_table_column(),
            endoscalar: meta.lookup_table_column(),
            _marker: PhantomData,
        }
    }

    #[allow(dead_code)]
    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "endoscalar_map",
            |mut table| {
                for index in 0..(1 << K) {
                    table.assign_cell(|| "bits", self.bits, index, || Ok(F::from(index as u64)))?;
                    table.assign_cell(
                        || "endoscalar",
                        self.endoscalar,
                        index,
                        || Ok(endoscale_scalar(F::zero(), &i2lebsp::<K>(index as u64))),
                    )?;
                }
                Ok(())
            },
        )
    }
}

/// Columns used in processing endoscalars.
#[derive(Clone, Debug)]
pub struct EndoscaleConfig<C: CurveAffine, const K: usize>
where
    C::Base: PrimeFieldBits,
{
    // Selector enabling a lookup in the (bitstring, endoscalar) table.
    q_lookup: Selector,
    // Selector enabling endoscaling commitment (Alg 1).
    q_endoscale_base: Selector,
    // Selector enabling the scalar version of the endoscaling algorithm (Alg 2).
    q_endoscale_scalar: Selector,
    // Public inputs are provided as endoscalars. Each endoscalar corresponds
    // to a K-bit chunk.
    endoscalars: Column<Instance>,
    // An additional advice column where endoscalar values are copied and used
    // in the lookup argument.
    endoscalars_copy: Column<Advice>,
    // The K-bit chunk representations of the public inputs.
    // These are used in-circuit for scalar multiplication.
    word: Column<Advice>,
    // Accumulator used in committing to a word by the endoscaling algorithm.
    // (x, y) coordinates
    acc: (Column<Advice>, Column<Advice>),
    // Point that is added to the accumulator.
    point: (Column<Advice>, Column<Advice>),
    // Fixed that is used in endoscaling.
    base: (Column<Advice>, Column<Advice>),
    // Configuration for running sum decomposition into pairs of bits.
    running_sum_pairs: be::Config<C::Base, 2>,
    // Configuration for running sum decomposition into K-bit chunks.
    running_sum_chunks: be::Config<C::Base, K>,
    // Bits used in endoscaling. These are in (b_0, b_1) pairs.
    pair: (Column<Advice>, Column<Advice>),
    // Table mapping words to their corresponding endoscalars.
    pub(in crate::recursion) table: TableConfig<C::Base, K>,
    // Config used in double-and-add on the accumulator.
    dbl_and_add_config: double_and_add::Config<C>,
    // Config used in witnessing accumulator points.
    acc_point_config: witness_point::Config<C>,
    // Config used in witnessing endoscaled points.
    endo_point_config: witness_point::Config<C>,
}

impl<C: CurveAffine, const K: usize> UtilitiesInstructions<C::Base> for EndoscaleConfig<C, K>
where
    C::Base: PrimeFieldBits,
{
    type Var = AssignedCell<C::Base, C::Base>;
}

impl<C: CurveAffine, const K: usize> EndoscaleConfig<C, K>
where
    C::Base: PrimeFieldBits,
{
    #[allow(dead_code)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<C::Base>,
        endoscalars: Column<Instance>,
        endoscalars_copy: Column<Advice>,
        word: Column<Advice>,
        acc: (Column<Advice>, Column<Advice>),
        point: (Column<Advice>, Column<Advice>),
        base: (Column<Advice>, Column<Advice>),
        running_sum: Column<Advice>,
        pair: (Column<Advice>, Column<Advice>),
        table: TableConfig<C::Base, K>,
    ) -> Self {
        let dbl_and_add_config = double_and_add::Config::configure(
            meta,
            point.0,
            point.1,
            endoscalars_copy,
            acc.0,
            acc.1,
        );
        let acc_point_config = witness_point::Config::configure(meta, acc.0, acc.1);
        let endo_point_config = witness_point::Config::configure(meta, point.0, point.1);
        let running_sum_pairs = be::Config::<C::Base, 2>::configure(meta, running_sum);
        let running_sum_chunks = be::Config::<C::Base, K>::configure(meta, running_sum);

        let config = Self {
            q_lookup: meta.complex_selector(),
            q_endoscale_base: meta.selector(),
            q_endoscale_scalar: meta.selector(),
            endoscalars,
            endoscalars_copy,
            word,
            acc,
            point,
            base,
            running_sum_pairs,
            running_sum_chunks,
            pair,
            table,
            dbl_and_add_config,
            acc_point_config,
            endo_point_config,
        };

        meta.enable_equality(config.endoscalars);
        meta.enable_equality(config.endoscalars_copy);
        meta.enable_equality(acc.0);
        meta.enable_equality(base.0);
        meta.enable_equality(base.1);

        /*
            The accumulator is initialised to [2](φ(P) + P) = (init_x, init_y).

            | b_0 | b_1 |   endo_x  |   endo_y   | acc_x  | acc_y  | P_x | P_y | <- column names
            --------------------------------------------------------------------
            | b_0 | b_1 | endo(P)_x |  endo(P)_y | init_x | init_y | P_x | P_y |

            (0, 0) -> (P_x, -P_y)
            (0, 1) -> (ζ * P_x, -P_y)
            (1, 0) -> (P_x, P_y)
            (1, 1) -> (ζ * P_x, P_y)
        */
        meta.create_gate("Endoscale base", |meta| {
            let q_endoscale_base = meta.query_selector(config.q_endoscale_base);

            // Pair of bits from the decomposition.
            let b_0 = meta.query_advice(config.pair.0, Rotation::cur());
            let b_1 = meta.query_advice(config.pair.1, Rotation::cur());

            // Boolean-constrain b_0, b_1
            let b_0_check = bool_check(b_0.clone());
            let b_1_check = bool_check(b_1.clone());

            // Check that `b_0, b_1` are consistent with the running sum decomposition.
            let decomposition_check = {
                let word = b_0.clone() + Expression::Constant(C::Base::from(2)) * b_1.clone();
                let expected_word = config.running_sum_pairs.window_expr()(meta);

                word - expected_word
            };

            // If the first bit is set, check that endo_y = -P_y
            let y_check = {
                let endo_y = meta.query_advice(config.point.1, Rotation::cur());
                let p_y = meta.query_advice(config.base.1, Rotation::cur());
                b_0 * (endo_y + p_y)
            };
            // If the second bit is set, check that endo_x = ζ * P_x
            let x_check = {
                let endo_x = meta.query_advice(config.point.0, Rotation::cur());
                let p_x = meta.query_advice(config.base.0, Rotation::cur());
                let zeta = Expression::Constant(C::Base::ZETA);
                b_1 * (endo_x - zeta * p_x)
            };

            std::array::IntoIter::new([
                ("b_0_check", b_0_check),
                ("b_1_check", b_1_check),
                ("decomposition_check", decomposition_check),
                ("x_check", x_check),
                ("y_check", y_check),
            ])
            .map(move |(name, poly)| (name, q_endoscale_base.clone() * poly))
        });

        meta.create_gate("Endoscale scalar with lookup", |meta| {
            let q_endoscale_scalar = meta.query_selector(config.q_endoscale_scalar);
            let endo = meta.query_advice(config.endoscalars_copy, Rotation::cur());
            let acc = meta.query_advice(config.acc.0, Rotation::cur());
            let next_acc = meta.query_advice(config.acc.0, Rotation::next());

            // Check that next_acc = acc + endo * 2^{K/2}
            let expected_next_acc = acc + (endo * C::Base::from(1 << (K / 2)));

            vec![q_endoscale_scalar * (next_acc - expected_next_acc)]
        });

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(config.q_lookup);
            let neg_q_lookup = Expression::Constant(C::Base::one()) - q_lookup.clone();
            let word = config.running_sum_chunks.window_expr()(meta);
            let endo = meta.query_advice(config.endoscalars_copy, Rotation::cur());
            let default_endo = {
                let val = endoscale_scalar(C::Base::zero(), &[false; K]);
                Expression::Constant(val)
            };

            vec![
                (q_lookup.clone() * word, table.bits),
                (
                    q_lookup * endo + neg_q_lookup * default_endo,
                    table.endoscalar,
                ),
            ]
        });

        config
    }
}

impl<C: CurveAffine, const K: usize> EndoscaleInstructions<C> for EndoscaleConfig<C, K>
where
    C::Base: PrimeFieldBits,
{
    #[allow(clippy::type_complexity)]
    fn endoscale_base<L: Layouter<C::Base>, const NUM_BITS: usize, const NUM_WINDOWS: usize>(
        &self,
        mut layouter: L,
        base: C,
        bitstring: &be::RunningSum<C::Base, 2, NUM_WINDOWS>,
    ) -> Result<
        (
            AssignedCell<C::Base, C::Base>,
            AssignedCell<C::Base, C::Base>,
        ),
        Error,
    > {
        layouter.assign_region(
            || "Commit to bitstring",
            |mut region| {
                let mut offset = 0;
                // The accumulator is initialised to [2](φ(P) + P) = (init_x, init_y).
                let mut acc = {
                    let acc = base.to_curve() + base * C::Scalar::ZETA;
                    self.acc_point_config.point_non_id_from_constant(
                        acc.to_affine(),
                        offset,
                        &mut region,
                    )?
                };

                // Copy the running sum into the correct offset.
                for (idx, z) in bitstring.zs().enumerate() {
                    z.copy_advice(
                        || format!("Copy running sum {}", NUM_WINDOWS - idx),
                        &mut region,
                        self.running_sum_pairs.z(),
                        offset + idx,
                    )?;
                }

                for (pair_idx, pair) in bitstring
                    .windows()
                    .iter()
                    .map(|w| w.map(|w| w.bits()))
                    .enumerate()
                {
                    self.q_endoscale_base.enable(&mut region, offset)?;

                    // Assign base_x
                    region.assign_advice_from_constant(
                        || "base_x",
                        self.base.0,
                        offset,
                        *base.coordinates().unwrap().x(),
                    )?;

                    // Assign base_y
                    region.assign_advice_from_constant(
                        || "base_y",
                        self.base.1,
                        offset,
                        *base.coordinates().unwrap().y(),
                    )?;

                    // Assign b_0
                    let b_0: Option<Bit> = pair.map(|pair| pair[0].into());
                    region.assign_advice(
                        || format!("pair_idx: {}, b_0", pair_idx),
                        self.pair.0,
                        offset,
                        || b_0.ok_or(Error::Synthesis),
                    )?;

                    // Assign b_1
                    let b_1: Option<Bit> = pair.map(|pair| pair[1].into());
                    region.assign_advice(
                        || format!("pair_idx: {}, b_1", pair_idx),
                        self.pair.1,
                        offset,
                        || b_1.ok_or(Error::Synthesis),
                    )?;

                    // Assign endoscaled point
                    let endo = pair.map(|pair| endoscale_pair::<C>(pair, base).unwrap());
                    let endo = self
                        .endo_point_config
                        .point_non_id(endo, offset, &mut region)?;

                    // Add endo to acc.
                    acc =
                        self.dbl_and_add_config
                            .assign_region(&endo, &acc, offset, &mut region)?;

                    offset += 1;
                }

                Ok((acc.x(), acc.y()))
            },
        )
    }

    fn endoscale_scalar<
        L: Layouter<C::Base>,
        const BITSTRING_NUM_BITS: usize,
        const WINDOW_NUM_BITS: usize,
        const NUM_WINDOWS: usize,
    >(
        &self,
        mut layouter: L,
        bitstring: &be::RunningSum<C::Base, WINDOW_NUM_BITS, NUM_WINDOWS>,
    ) -> Result<AssignedCell<C::Base, C::Base>, Error> {
        layouter.assign_region(
            || "Endoscale scalar using bitstring (lookup optimisation)",
            |mut region| {
                let mut offset = 0;
                // The endoscalar is initialised to 2 * (ζ + 1).
                let mut acc = {
                    let init = (C::Base::ZETA + C::Base::one()).double();
                    region.assign_advice_from_constant(
                        || "initialise acc",
                        self.acc.0,
                        offset,
                        init,
                    )?
                };

                // Copy the running sum into the correct offset.
                for (idx, z) in bitstring.zs().enumerate() {
                    z.copy_advice(
                        || format!("Copy running sum {}", NUM_WINDOWS - idx),
                        &mut region,
                        self.running_sum_chunks.z(),
                        offset + idx,
                    )?;
                }

                // For each chunk, lookup the (chunk, endoscalar) pair and add
                // it to the accumulator.
                for (idx, chunk) in bitstring.windows().iter().enumerate() {
                    self.q_endoscale_scalar.enable(&mut region, offset)?;
                    self.q_lookup.enable(&mut region, offset)?;

                    let endoscalar = chunk.map(|c| endoscale_scalar(C::Base::zero(), &c.bits()));
                    // Witness endoscalar.
                    region.assign_advice(
                        || format!("Endoscalar for chunk {}", NUM_WINDOWS - 1 - idx),
                        self.endoscalars_copy,
                        offset,
                        || endoscalar.ok_or(Error::Synthesis),
                    )?;

                    // Bitshift the endoscalar by {K / 2} and add to accumulator.
                    let acc_val = acc
                        .value()
                        .zip(endoscalar)
                        .map(|(&acc, endo)| acc + endo * C::Base::from(1 << (K / 2)));
                    acc = region.assign_advice(
                        || format!("Endoscalar for chunk {}", NUM_WINDOWS - 1 - idx),
                        self.acc.0,
                        offset + 1,
                        || acc_val.ok_or(Error::Synthesis),
                    )?;

                    offset += 1;
                }

                Ok(acc)
            },
        )
    }

    fn recover_bitstring<
        L: Layouter<C::Base>,
        const BITSTRING_NUM_BITS: usize,
        const WINDOW_NUM_BITS: usize,
        const NUM_WINDOWS: usize,
    >(
        &self,
        mut layouter: L,
        bitstring: &be::RunningSum<C::Base, WINDOW_NUM_BITS, NUM_WINDOWS>,
        pub_input_rows: [usize; NUM_WINDOWS],
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "Recover bitstring from endoscalars",
            |mut region| {
                let mut offset = 0;

                // Copy the running sum into the correct offset.
                for (idx, z) in bitstring.zs().enumerate() {
                    z.copy_advice(
                        || format!("Copy running sum {}", NUM_WINDOWS - idx),
                        &mut region,
                        self.running_sum_chunks.z(),
                        offset + idx,
                    )?;
                }

                // For each chunk, lookup the (chunk, endoscalar) pair.
                for (chunk, pub_input_row) in bitstring.windows().iter().zip(pub_input_rows.iter())
                {
                    self.q_lookup.enable(&mut region, offset)?;

                    let _computed_endoscalar =
                        chunk.map(|c| endoscale_scalar(C::Base::zero(), &c.bits()));
                    // Copy endoscalar from given row on instance column
                    let _copied_endoscalar = region.assign_advice_from_instance(
                        || format!("Endoscalar at row {:?}", pub_input_row),
                        self.endoscalars,
                        *pub_input_row,
                        self.endoscalars_copy,
                        offset,
                    )?;

                    #[cfg(test)]
                    {
                        if let Some(&copied) = _copied_endoscalar.value() {
                            if let Some(computed) = _computed_endoscalar {
                                assert_eq!(copied, computed);
                            }
                        }
                    }

                    offset += 1;
                }

                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::{endoscale_scalar, EndoscaleConfig, EndoscaleInstructions, TableConfig};
    use ff::PrimeFieldBits;
    use halo2_gadgets::utilities::lebs2ip;
    use halo2_proofs::{
        arithmetic::CurveAffine,
        circuit::{Layouter, SimpleFloorPlanner},
        plonk::{Circuit, ConstraintSystem, Error},
        poly::commitment::Params,
    };
    use pasta_curves::{pallas, vesta};

    use std::{convert::TryInto, marker::PhantomData, vec};

    #[derive(Default)]
    struct BaseCircuit<
        C: CurveAffine,
        const NUM_BITS: usize,
        const NUM_BITS_DIV2: usize,
        const NUM_BITS_DIV10: usize,
    >
    where
        C::Base: PrimeFieldBits,
    {
        bitstring: Option<[bool; NUM_BITS]>,
        _marker: PhantomData<C>,
    }

    impl<
            C: CurveAffine,
            const NUM_BITS: usize,
            const NUM_BITS_DIV2: usize,
            const NUM_BITS_DIV10: usize,
        > Circuit<C::Base> for BaseCircuit<C, NUM_BITS, NUM_BITS_DIV2, NUM_BITS_DIV10>
    where
        C::Base: PrimeFieldBits,
    {
        type Config = EndoscaleConfig<C, 10>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<C::Base>) -> Self::Config {
            let table_config = TableConfig::configure(meta);

            let constants = meta.fixed_column();
            meta.enable_constant(constants);
            let endoscalars = meta.instance_column();
            let endoscalars_copy = meta.advice_column();
            let word = meta.advice_column();
            let acc = (meta.advice_column(), meta.advice_column());
            let point = (meta.advice_column(), meta.advice_column());
            let base = (meta.advice_column(), meta.advice_column());
            let running_sum = meta.advice_column();
            let pair = (meta.advice_column(), meta.advice_column());

            meta.enable_equality(word);

            EndoscaleConfig::<C, 10>::configure(
                meta,
                endoscalars,
                endoscalars_copy,
                word,
                acc,
                point,
                base,
                running_sum,
                pair,
                table_config,
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<C::Base>,
        ) -> Result<(), Error> {
            config.table.load(&mut layouter)?;

            let challenge = {
                let challenge = self.bitstring.map(|b| lebs2ip::<NUM_BITS>(&b));
                challenge.map(C::Base::from)
            };
            // Decompose challenge into 2-bit windows.
            let bitstring_pairs = {
                layouter.assign_region(
                    || "Decompose challenge",
                    |mut region| {
                        config
                            .running_sum_pairs
                            .witness_decompose::<NUM_BITS, NUM_BITS_DIV2>(
                                &mut region,
                                0,
                                challenge,
                                true,
                            )
                    },
                )?
            };

            // Alg 1
            let g_lagrange = Params::<C>::new(11).g_lagrange();
            config.endoscale_base::<_, NUM_BITS, NUM_BITS_DIV2>(
                layouter.namespace(|| "commit to challenge"),
                g_lagrange[0],
                &bitstring_pairs,
            )?;

            Ok(())
        }
    }

    #[derive(Default)]
    struct ScalarCircuit<
        C: CurveAffine,
        const NUM_BITS: usize,
        const NUM_BITS_DIV2: usize,
        const NUM_BITS_DIV10: usize,
    >
    where
        C::Base: PrimeFieldBits,
    {
        bitstring: Option<[bool; NUM_BITS]>,
        pub_input_rows: Option<[usize; NUM_BITS_DIV10]>,
        _marker: PhantomData<C>,
    }

    impl<
            C: CurveAffine,
            const NUM_BITS: usize,
            const NUM_BITS_DIV2: usize,
            const NUM_BITS_DIV10: usize,
        > Circuit<C::Base> for ScalarCircuit<C, NUM_BITS, NUM_BITS_DIV2, NUM_BITS_DIV10>
    where
        C::Base: PrimeFieldBits,
    {
        type Config = EndoscaleConfig<C, 10>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<C::Base>) -> Self::Config {
            let table_config = TableConfig::configure(meta);

            let constants = meta.fixed_column();
            meta.enable_constant(constants);
            let endoscalars = meta.instance_column();
            let endoscalars_copy = meta.advice_column();
            let word = meta.advice_column();
            let acc = (meta.advice_column(), meta.advice_column());
            let point = (meta.advice_column(), meta.advice_column());
            let base = (meta.advice_column(), meta.advice_column());
            let running_sum = meta.advice_column();
            let pair = (meta.advice_column(), meta.advice_column());

            meta.enable_equality(word);

            EndoscaleConfig::<C, 10>::configure(
                meta,
                endoscalars,
                endoscalars_copy,
                word,
                acc,
                point,
                base,
                running_sum,
                pair,
                table_config,
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<C::Base>,
        ) -> Result<(), Error> {
            config.table.load(&mut layouter)?;

            let challenge = {
                let challenge = self.bitstring.map(|b| lebs2ip::<NUM_BITS>(&b));
                challenge.map(C::Base::from)
            };

            // Decompose challenge into 10-bit chunks.
            let bitstring_chunks = {
                layouter.assign_region(
                    || "Decompose challenge",
                    |mut region| {
                        config
                            .running_sum_chunks
                            .witness_decompose::<NUM_BITS, NUM_BITS_DIV10>(
                                &mut region,
                                0,
                                challenge,
                                true,
                            )
                    },
                )?
            };

            // Alg 2 with lookup
            config.endoscale_scalar::<_, NUM_BITS, 10, NUM_BITS_DIV10>(
                layouter.namespace(|| "endoscale bitstring with lookup"),
                &bitstring_chunks,
            )?;

            // Recover bitstring from public input endoscalars.
            config.recover_bitstring::<_, NUM_BITS, 10, NUM_BITS_DIV10>(
                layouter.namespace(|| "recover bitstring with lookup"),
                &bitstring_chunks,
                self.pub_input_rows.unwrap(),
            )?;

            Ok(())
        }
    }

    fn test_endoscale_cycle<BaseCurve: CurveAffine, ScalarCurve: CurveAffine>()
    where
        BaseCurve::Base: PrimeFieldBits,
        ScalarCurve::Base: PrimeFieldBits,
    {
        use ff::Field;
        use halo2_proofs::dev::MockProver;

        // Random 60-bit challenge.
        let bitstring: Vec<_> = (0..60).map(|_| rand::random::<bool>()).collect();
        let endos = (0..6)
            .rev()
            .map(|i| {
                let start_idx = i * 10;
                let chunk = &bitstring[start_idx..(start_idx + 10)];
                endoscale_scalar(ScalarCurve::Base::zero(), chunk.try_into().unwrap())
            })
            .collect();

        let base_circuit = BaseCircuit::<BaseCurve, 60, 30, 6> {
            bitstring: Some(bitstring.clone().try_into().unwrap()),
            _marker: PhantomData,
        };
        let scalar_circuit = ScalarCircuit::<ScalarCurve, 60, 30, 6> {
            bitstring: Some(bitstring.try_into().unwrap()),
            pub_input_rows: Some((0..6).collect::<Vec<_>>().try_into().unwrap()),
            _marker: PhantomData,
        };

        // Calls endoscale_base
        let base_prover = MockProver::run(11, &base_circuit, vec![vec![]]).unwrap();
        assert_eq!(base_prover.verify(), Ok(()));

        // Calls endoscale_scalar
        let scalar_prover = MockProver::run(11, &scalar_circuit, vec![endos]).unwrap();
        assert_eq!(scalar_prover.verify(), Ok(()));

        // TODO: Check consistency of resulting commitment / endoscalar
    }

    #[test]
    fn test_endoscale() {
        test_endoscale_cycle::<pallas::Affine, vesta::Affine>();
        test_endoscale_cycle::<vesta::Affine, pallas::Affine>();
    }
}
