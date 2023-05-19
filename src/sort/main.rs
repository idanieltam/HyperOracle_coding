use crate::less_than::{LtChip, LtConfig, LtInstruction};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector,
    },
    poly::Rotation,
};
use std::marker::PhantomData;

const NUM_ELEMENTS: usize = 8;
const NUM_BYTES: usize = 8;

#[derive(Debug, Clone)]
struct SortNConfig<F: FieldExt> {
    // N inputs, N outputs
    pub advice: [Column<Advice>; 2 * NUM_ELEMENTS],
    pub master_selector: Selector,
    pub instance: Column<Instance>,

    lt_selectors: [Selector; NUM_ELEMENTS - 1],
    lt_configs: [LtConfig<F, NUM_BYTES>; NUM_ELEMENTS - 1],
}

#[derive(Debug, Clone)]
struct SortNChip<F: FieldExt> {
    config: SortNConfig<F>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> SortNChip<F> {
    pub fn construct(config: SortNConfig<F>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta_cs: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 2 * NUM_ELEMENTS],
        instance: Column<Instance>,
        fixed: Column<Fixed>,
    ) -> SortNConfig<F> {
        meta_cs.enable_equality(instance);
        meta_cs.enable_constant(fixed);
        for column in &advice {
            meta_cs.enable_equality(*column);
        }
        let master_selector = meta_cs.selector();
        let mut lt_selectors = Vec::with_capacity(NUM_ELEMENTS - 1);
        for _i in 0..NUM_ELEMENTS - 1 {
            lt_selectors.push(meta_cs.selector());
        }

        let mut lt_configs = Vec::with_capacity(NUM_ELEMENTS - 1);
        let mut advice_vec = advice.to_vec();
        for _i in 0..NUM_BYTES + 1 - 2 * NUM_ELEMENTS {
            advice_vec.push(meta_cs.advice_column());
        }
        let mut diff = Vec::with_capacity(NUM_BYTES);
        for i in 1..NUM_BYTES + 1 {
            diff.push(advice_vec[i]);
        }
        for i in 0..NUM_ELEMENTS - 1 {
            let lt_config: LtConfig<F, NUM_BYTES> = LtChip::configure(
                meta_cs,
                |meta| meta.query_selector(lt_selectors[i]),
                |meta| meta.query_advice(advice_vec[i], Rotation(-1 - i as i32)),
                |meta| meta.query_advice(advice_vec[i + 1], Rotation(-1 - i as i32)),
                advice_vec[0],
                diff.clone().try_into().unwrap(),
            );
            lt_configs.push(lt_config);
        }

        let mut lt_constraints = Vec::with_capacity(NUM_ELEMENTS - 1);
        meta_cs.create_gate("sortN", |meta_vc| {
            //  0 |  1 |  2 |  3 |  4 |  5 |  6 |  7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | selectors
            // i0   i1   i2   i3   i4   i5   i6   i7  o0   o1  o2  o3   o4   o5   o6   o7
            // o0'  o1'  o2'  o3'   o4' o5'  o6'  o7' 
            // lt0 diff0_0-15
            // lt1 diff1_0-15
            // lt2 diff2_0-15
            // lt3 diff3_0-15
            // lt4 diff4_0-15
            // lt5 diff5_0-15
            // lt6 diff6_0-15
            let s = meta_vc.query_selector(master_selector);

            for i in 0..NUM_ELEMENTS - 1 {
                lt_constraints.push(
                    s.clone()
                        * (lt_configs[i].is_lt(meta_vc, Some(Rotation(i as i32 + 2)))
                            - Expression::Constant(F::one())),
                );
            }
            lt_constraints
        });

        SortNConfig {
            advice,
            master_selector,
            instance,
            lt_configs: lt_configs.try_into().unwrap(),
            lt_selectors: lt_selectors.try_into().unwrap(),
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        in_indices: [usize; NUM_ELEMENTS],
        values: [F; NUM_ELEMENTS],
    ) -> Result<[AssignedCell<F, F>; NUM_ELEMENTS], Error> {
        layouter.assign_region(
            || "sort",
            |mut region| {
                self.config.master_selector.enable(&mut region, 0)?;

                // unsorted inputs
                let mut in_cells = Vec::with_capacity(2 * NUM_ELEMENTS);
                for (i, column) in self.config.advice.iter().enumerate() {
                    in_cells.push(region.assign_advice_from_instance(
                        || format!("instance({})", i),
                        self.config.instance,
                        i,
                        *column,
                        0,
                    )?);
                }

                // sorted outputs
                let mut output_cells = Vec::with_capacity(NUM_ELEMENTS);
                for i in 0..NUM_ELEMENTS {
                    output_cells.push(in_cells[in_indices[i]].copy_advice(
                        || format!("sort out[{}]", i),
                        &mut region,
                        self.config.advice[i],
                        1,
                    )?);
                }

                // lt chips
                for i in 0..NUM_ELEMENTS - 1 {
                    self.config.lt_selectors[i].enable(&mut region, i + 2)?;
                }
                let mut results = Vec::with_capacity(NUM_ELEMENTS - 1);
                for i in 0..NUM_ELEMENTS - 1 {
                    let lt_chip = LtChip::construct(self.config.lt_configs[i]);
                    results.push(lt_chip.assign(&mut region, i + 2, values[i], values[i + 1]));
                }
                Ok(output_cells.try_into().unwrap())
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct SortNCircuit<F> {
    values: [F; NUM_ELEMENTS],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for SortNCircuit<F> {
    type Config = SortNConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let mut advice = Vec::with_capacity(2 * NUM_ELEMENTS);
        for _i in 0..2 * NUM_ELEMENTS {
            advice.push(meta.advice_column());
        }
        let instance = meta.instance_column();
        let fixed = meta.fixed_column();
        SortNChip::configure(meta, advice.try_into().unwrap(), instance, fixed)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = SortNChip::construct(config);

        // Perform Bubble sort, keeping track of indices
        let mut in_indices = [0; NUM_ELEMENTS];
        for i in 0..NUM_ELEMENTS {
            in_indices[i] = i;
        }
        let mut values = self.values;
        for i in 1..NUM_ELEMENTS {
            for j in 1..(NUM_ELEMENTS - i + 1) {
                if values[j] < values[j - 1] {
                    values.swap(j - 1, j);
                    in_indices.swap(j - 1, j);
                }
            }
        }

        let output_cells = chip.assign(layouter.namespace(|| "all"), in_indices, values)?;

        for i in 0..NUM_ELEMENTS {
            chip.expose_public(
                layouter.namespace(|| "out"),
                &output_cells[i],
                i + NUM_ELEMENTS,
            )?;
        }

        Ok(())
    }
}
