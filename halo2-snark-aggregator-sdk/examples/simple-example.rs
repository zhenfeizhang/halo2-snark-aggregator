use halo2_proofs::{
    arithmetic::{BaseExt, CurveAffine, Field, FieldExt, MultiMillerLoop},
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance},
    poly::Rotation,
};
use halo2_snark_aggregator_circuit::sample_circuit::TargetCircuit;
use halo2_snark_aggregator_sdk::zkaggregate;
use rand_core::OsRng;
use std::marker::PhantomData;

// ANCHOR: instructions
trait NumericInstructions<F: FieldExt>: Chip<F> {
    /// Variable representing a number.
    type Num;

    /// Loads a number into the circuit as a private input.
    fn load_private(&self, layouter: impl Layouter<F>, a: Option<F>) -> Result<Self::Num, Error>;

    /// Loads a number into the circuit as a fixed constant.
    fn load_constant(&self, layouter: impl Layouter<F>, constant: F) -> Result<Self::Num, Error>;

    /// Returns `c = a * b`.
    fn mul(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;

    /// Exposes a number as a public input to the circuit.
    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;
}
// ANCHOR_END: instructions

// ANCHOR: chip
/// The chip that will implement our instructions! Chips store their own
/// config, as well as type markers if necessary.
struct FieldChip<F: FieldExt> {
    config: FieldConfig,
    _marker: PhantomData<F>,
}
// ANCHOR_END: chip

// ANCHOR: chip-config
/// Chip state is stored in a config struct. This is generated by the chip
/// during configuration, and then stored inside the chip.
#[derive(Clone, Debug)]
pub struct FieldConfig {
    /// For this chip, we will use two advice columns to implement our instructions.
    /// These are also the columns through which we communicate with other parts of
    /// the circuit.
    advice: [Column<Advice>; 2],

    /// This is the public input (instance) column.
    instance: Column<Instance>,

    // We need a selector to enable the multiplication gate, so that we aren't placing
    // any constraints on cells where `NumericInstructions::mul` is not being used.
    // This is important when building larger circuits, where columns are used by
    // multiple sets of instructions.
    s_mul: Column<Fixed>,
}

impl<F: FieldExt> FieldChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self { config, _marker: PhantomData }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 2],
        instance: Column<Instance>,
        constant: Column<Fixed>,
        s_mul: Column<Fixed>,
    ) -> <Self as Chip<F>>::Config {
        meta.enable_equality(instance);
        meta.enable_constant(constant);
        for column in &advice {
            meta.enable_equality(*column);
        }

        // Define our multiplication gate!
        meta.create_gate("mul", |meta| {
            // To implement multiplication, we need three advice cells and a selector
            // cell. We arrange them like so:
            //
            // | a0  | a1  | s_mul |
            // |-----|-----|-------|
            // | lhs | rhs | s_mul |
            // | out |     |       |
            //
            // Gates may refer to any relative offsets we want, but each distinct
            // offset adds a cost to the proof. The most common offsets are 0 (the
            // current row), 1 (the next row), and -1 (the previous row), for which
            // `Rotation` has specific constructors.
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_mul = meta.query_fixed(s_mul, Rotation::cur());

            // Finally, we return the polynomial expressions that constrain this gate.
            // For our multiplication gate, we only need a single polynomial constraint.
            //
            // The polynomial expressions returned from `create_gate` will be
            // constrained by the proving system to equal zero. Our expression
            // has the following properties:
            // - When s_mul = 0, any value is allowed in lhs, rhs, and out.
            // - When s_mul != 0, this constrains lhs * rhs = out.
            vec![s_mul * (lhs * rhs - out)]
        });

        FieldConfig { advice, instance, s_mul }
    }
}
// ANCHOR_END: chip-config

// ANCHOR: chip-impl
impl<F: FieldExt> Chip<F> for FieldChip<F> {
    type Config = FieldConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
// ANCHOR_END: chip-impl

// ANCHOR: instructions-impl
/// A variable representing a number.
#[derive(Clone)]
struct Number<F: FieldExt>(AssignedCell<F, F>);

impl<F: FieldExt> NumericInstructions<F> for FieldChip<F> {
    type Num = Number<F>;

    fn load_private(
        &self,
        mut layouter: impl Layouter<F>,
        value: Option<F>,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load private",
            |mut region| {
                region
                    .assign_advice(
                        || "private input",
                        config.advice[0],
                        0,
                        || value.ok_or(Error::Synthesis),
                    )
                    .map(Number)
            },
        )
    }

    fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        constant: F,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load constant",
            |mut region| {
                region
                    .assign_advice_from_constant(|| "constant value", config.advice[0], 0, constant)
                    .map(Number)
            },
        )
    }

    fn mul(
        &self,
        mut layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "mul",
            |mut region: Region<'_, F>| {
                // We only want to use a single multiplication gate in this region,
                // so we enable it at region offset 0; this means it will constrain
                // cells at offsets 0 and 1.
                region.assign_fixed(|| "s_mul", config.s_mul, 0, || Ok(F::one()))?;

                // The inputs we've been given could be located anywhere in the circuit,
                // but we can only rely on relative offsets inside this region. So we
                // assign new cells inside the region and constrain them to have the
                // same values as the inputs.
                a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                // Now we can assign the multiplication result, which is to be assigned
                // into the output position.
                let value = a.0.value().and_then(|a| b.0.value().map(|b| *a * *b));

                // Finally, we do the assignment to the output, returning a
                // variable to be used in another part of the circuit.
                region
                    .assign_advice(
                        || "lhs * rhs",
                        config.advice[0],
                        1,
                        || value.ok_or(Error::Synthesis),
                    )
                    .map(Number)
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();

        layouter.constrain_instance(num.0.cell(), config.instance, row)
    }
}
// ANCHOR_END: instructions-impl

// ANCHOR: circuit
/// The full circuit implementation.
///
/// In this struct we store the private input variables. We use `Option<F>` because
/// they won't have any value during key generation. During proving, if any of these
/// were `None` we would get an error.
pub struct MyCircuit<F: FieldExt> {
    pub(crate) constant: F,
    pub(crate) a: Option<F>,
    pub(crate) b: Option<F>,
}

impl<F: FieldExt> Default for MyCircuit<F> {
    fn default() -> Self {
        MyCircuit { constant: F::from(7u64), a: None, b: None }
    }
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = FieldConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // We create the two advice columns that FieldChip uses for I/O.
        let advice = [meta.advice_column(), meta.advice_column()];

        // We also need an instance column to store public inputs.
        let instance = meta.instance_column();

        // Create a fixed column to load constants.
        let constant = meta.fixed_column();

        // Create a fixed column for selector.
        let s_mul = meta.fixed_column();

        FieldChip::configure(meta, advice, instance, constant, s_mul)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let field_chip = FieldChip::<F>::construct(config);

        // Load our private values into the circuit.
        let a = field_chip.load_private(layouter.namespace(|| "load a"), self.a)?;
        let b = field_chip.load_private(layouter.namespace(|| "load b"), self.b)?;

        // Load the constant factor into the circuit.
        let constant =
            field_chip.load_constant(layouter.namespace(|| "load constant"), self.constant)?;

        // We only have access to plain multiplication.
        // We could implement our circuit as:
        //     asq  = a*a
        //     bsq  = b*b
        //     absq = asq*bsq
        //     c    = constant*asq*bsq
        //
        // but it's more efficient to implement it as:
        //     ab   = a*b
        //     absq = ab^2
        //     c    = constant*absq
        let ab = field_chip.mul(layouter.namespace(|| "a * b"), a, b)?;
        let absq = field_chip.mul(layouter.namespace(|| "ab * ab"), ab.clone(), ab)?;
        let c = field_chip.mul(layouter.namespace(|| "constant * absq"), constant, absq)?;

        // Expose the result as a public input to the circuit.
        field_chip.expose_public(layouter.namespace(|| "expose c"), c, 0)
    }
}

pub struct TestCircuit;

impl<C: CurveAffine, E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>> TargetCircuit<C, E>
    for TestCircuit
{
    const TARGET_CIRCUIT_K: u32 = 8;
    const PUBLIC_INPUT_SIZE: usize = 1;
    const N_PROOFS: usize = 1;
    const NAME: &'static str = "simple_example";
    const PARAMS_NAME: &'static str = "simple_example";
    const READABLE_VKEY: bool = true;

    type Circuit = MyCircuit<C::ScalarExt>;

    fn instance_builder() -> (Self::Circuit, Vec<Vec<C::ScalarExt>>) {
        let constant = C::Scalar::from(7);
        let a = C::Scalar::random(OsRng);
        let b = C::Scalar::random(OsRng);
        let circuit = MyCircuit { constant, a: Some(a), b: Some(b) };
        let instances = vec![vec![constant * a.square() * b.square()]];
        (circuit, instances)
    }

    fn load_instances(buf: &Vec<u8>) -> Vec<Vec<Vec<<C as CurveAffine>::ScalarExt>>> {
        let mut ret = vec![];
        let cursor = &mut std::io::Cursor::new(buf);

        while let Ok(a) = <E::Scalar as BaseExt>::read(cursor) {
            ret.push(a);
        }

        vec![vec![ret]]
    }
}

zkaggregate! {1, vec![], TestCircuit}

pub fn main() {
    // read in degree of test circuit from file
    let k = halo2_snark_aggregator_circuit::fs::load_verify_circuit_degree();
    let builder = zkcli::builder(k);
    builder.run()
}
