use super::{
    ecc_chip::{EccChip, EccChipOps},
    integer_chip::IntegerChipOps,
};
use crate::{
    gates::base_gate::{AssignedCondition, AssignedValue, Context},
    pair,
    utils::{bn_to_field, field_to_bn},
};
use group::ff::{Field, PrimeField};
use halo2_proofs::{arithmetic::CurveAffine, plonk::Error};
use halo2curves::FieldExt;
use num_bigint::BigUint;

pub struct NativeEccChip<'a, C: CurveAffine>(pub EccChip<'a, C, C::ScalarExt>);

impl<'a, C: CurveAffine> NativeEccChip<'a, C> {
    pub fn new(integer_chip: &'a dyn IntegerChipOps<C::Base, C::ScalarExt>) -> Self {
        NativeEccChip(EccChip::new(integer_chip))
    }

    fn decompose_bits<const WINDOW_SIZE: usize>(
        &self,
        _: &mut Context<C::ScalarExt>,
        s: BigUint,
    ) -> (Vec<C::ScalarExt>, BigUint) {
        let zero = C::ScalarExt::zero();
        let one = C::ScalarExt::one();
        (
            (0..WINDOW_SIZE)
                .map(|i| if s.bit(i as u64) { one } else { zero })
                .collect(),
            s >> WINDOW_SIZE,
        )
    }
}

impl<'a, C: CurveAffine> EccChipOps<C, C::ScalarExt> for NativeEccChip<'a, C> {
    type AssignedScalar = AssignedValue<C::ScalarExt>;

    fn integer_chip(&self) -> &dyn IntegerChipOps<C::Base, C::ScalarExt> {
        self.0.integer_chip
    }

    fn decompose_scalar<const WINDOW_SIZE: usize>(
        &self,
        ctx: &mut Context<C::ScalarExt>,
        s: &AssignedValue<C::ScalarExt>,
    ) -> Result<Vec<[AssignedCondition<C::ScalarExt>; WINDOW_SIZE]>, Error> {
        let zero = C::ScalarExt::zero();
        let one = C::ScalarExt::one();
        let base_gate = self.base_gate();
        let windows = (<C::ScalarExt as PrimeField>::NUM_BITS - 1 + WINDOW_SIZE as u32)
            / (WINDOW_SIZE as u32);
        let mut ret = vec![];

        let s_bn = field_to_bn(&s.value);

        let (bits, s_bn) = self.decompose_bits::<WINDOW_SIZE>(ctx, s_bn);
        let bits = bits
            .into_iter()
            .enumerate()
            .map(|(i, v)| pair!(v, C::ScalarExt::from(1u64 << i)))
            .collect();
        let cells = base_gate.one_line_with_last_base(
            ctx,
            bits,
            pair!(s, -one),
            zero,
            (vec![], C::ScalarExt::from(1u64 << WINDOW_SIZE)),
        )?;
        ret.push(
            cells[0..WINDOW_SIZE]
                .iter()
                .map(|v| -> AssignedCondition<C::ScalarExt> { v.into() })
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        );

        let mut s_bn = s_bn;
        for _ in 1..windows - 1 {
            let s_n: C::ScalarExt = bn_to_field(&s_bn);
            let (bits, _s_bn) = self.decompose_bits::<WINDOW_SIZE>(ctx, s_bn);
            let bits = bits
                .into_iter()
                .enumerate()
                .map(|(i, v)| pair!(v, C::ScalarExt::from(1u64 << i)))
                .collect();
            let cells = base_gate.one_line_with_last_base(
                ctx,
                bits,
                pair!(s_n, -one),
                zero,
                (vec![], C::ScalarExt::from(1u64 << WINDOW_SIZE)),
            )?;
            ret.push(
                cells[0..WINDOW_SIZE]
                    .iter()
                    .map(|v| -> AssignedCondition<C::ScalarExt> { v.into() })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap(),
            );
            s_bn = _s_bn;
        }

        let s_n: C::ScalarExt = bn_to_field(&s_bn);
        let (bits, _) = self.decompose_bits::<WINDOW_SIZE>(ctx, s_bn);
        let bits = bits
            .into_iter()
            .enumerate()
            .map(|(i, v)| pair!(v, C::ScalarExt::from(1u64 << i)))
            .collect();
        let cells =
            base_gate.one_line_with_last_base(ctx, bits, pair!(s_n, -one), zero, (vec![], zero))?;
        ret.push(
            cells[0..WINDOW_SIZE]
                .iter()
                .map(|v| -> AssignedCondition<C::ScalarExt> { v.into() })
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        );

        ret.reverse();

        for window in &ret {
            for bit in window {
                base_gate.assert_bit(ctx, &AssignedValue::from(bit))?;
            }
        }

        Ok(ret)
    }

    #[inline]
    /// Decompose a `scalar_bit_length`-bit scalar `s` into many c-bit scalar
    /// variables `{s0, ..., s_m}` such that `s = \sum_{j=0..m} 2^{cj} * s_j`
    fn decompose_scalar_pippenger(
        ctx: &mut Context<C::ScalarExt>,
        scalar: &Self::AssignedScalar,
        c: usize,
        scalar_bit_length: usize,
    ) -> Result<Vec<Self::AssignedScalar>, Error> {
        // create witness
        let m = (scalar_bit_length - 1) / c + 1;

        let mut scalar_val = scalar.value;

        // let decomposed_scalar_vars = (0..m)
        //     .map(|_| {
        //         // We mod the remaining bits by 2^{window size}, thus taking `c` bits.
        //         let scalar_u64 = scalar_val.as_ref()[0] % (1 << c);
        //         // We right-shift by c bits, thus getting rid of the
        //         // lower bits.
        //         scalar_val.divn(c as u32);
        //         circuit.create_variable(F::from(scalar_u64))
        //     })
        //     .collect::<Result<Vec<_>, _>>()?;

        // create circuit
        let range_size = C::ScalarExt::from_u128((1 << c) as u128);
        // circuit.decomposition_gate(decomposed_scalar_vars.clone(), scalar_var, range_size)?;

        // Ok(decomposed_scalar_vars)
        todo!()
    }
}
