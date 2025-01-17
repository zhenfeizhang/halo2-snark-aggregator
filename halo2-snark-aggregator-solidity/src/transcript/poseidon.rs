use group::ff::PrimeField;
use halo2_proofs::{arithmetic::CurveAffine, plonk::Error};
use halo2_snark_aggregator_api::arith::common::ArithCommonChip;
use halo2_snark_aggregator_api::{
    arith::ecc::ArithEccChip,
    hash::poseidon::PoseidonChip,
    transcript::{encode::Encode, read::TranscriptRead},
};
use pairing_bn256::group;
use std::{io, marker::PhantomData};

use crate::chips::ecc_chip::SolidityEccExpr;
use crate::chips::scalar_chip::SolidityFieldExpr;
use crate::code_generator::ctx::SolidityCodeGeneratorContext;

pub struct PoseidonTranscriptRead<
    R: io::Read,
    C: CurveAffine,
    A: ArithEccChip<
        Point = C,
        Scalar = C::Scalar,
        Context = SolidityCodeGeneratorContext,
        AssignedNative = SolidityFieldExpr<C::Scalar>,
        AssignedScalar = SolidityFieldExpr<C::Scalar>,
        AssignedPoint = SolidityEccExpr<C::CurveExt>,
    >,
    E: Encode<A>,
    const T: usize,
    const RATE: usize,
> {
    hash: PoseidonChip<A::NativeChip, T, RATE>,
    reader: R,
    _phantom: PhantomData<E>,
}

impl<
        R: io::Read,
        C: CurveAffine,
        A: ArithEccChip<
            Point = C,
            Scalar = C::Scalar,
            Context = SolidityCodeGeneratorContext,
            AssignedNative = SolidityFieldExpr<C::Scalar>,
            AssignedScalar = SolidityFieldExpr<C::Scalar>,
            AssignedPoint = SolidityEccExpr<C::CurveExt>,
        >,
        E: Encode<A>,
        const T: usize,
        const RATE: usize,
    > PoseidonTranscriptRead<R, C, A, E, T, RATE>
{
    pub fn new(
        reader: R,
        ctx: &mut A::Context,
        schip: &A::NativeChip,
        r_f: usize,
        r_p: usize,
    ) -> Result<PoseidonTranscriptRead<R, C, A, E, T, RATE>, A::Error> {
        Ok(PoseidonTranscriptRead {
            hash: PoseidonChip::new(ctx, schip, r_f, r_p)?,
            reader,
            _phantom: PhantomData,
        })
    }
}

impl<
        R: io::Read,
        C: CurveAffine,
        A: ArithEccChip<
            Point = C,
            Scalar = C::Scalar,
            Error = Error,
            Context = SolidityCodeGeneratorContext,
            AssignedNative = SolidityFieldExpr<C::Scalar>,
            AssignedScalar = SolidityFieldExpr<C::Scalar>,
            AssignedPoint = SolidityEccExpr<C::CurveExt>,
        >,
        E: Encode<A>,
        const T: usize,
        const RATE: usize,
    > TranscriptRead<A> for PoseidonTranscriptRead<R, C, A, E, T, RATE>
{
    fn read_point(
        &mut self,
        ctx: &mut A::Context,
        nchip: &A::NativeChip,
        schip: &A::ScalarChip,
        pchip: &A,
    ) -> Result<A::AssignedPoint, A::Error> {
        let mut compressed = C::Repr::default();
        self.reader.read_exact(compressed.as_mut())?;
        let point: C = Option::from(C::from_bytes(&compressed)).ok_or_else(|| {
            A::Error::Transcript(io::Error::new(
                io::ErrorKind::Other,
                "invalid point encoding in proof",
            ))
        })?;
        ctx.enter_transcript();
        let assigned_point = pchip.assign_var(ctx, point)?;
        ctx.exit_transcript();
        self.common_point(ctx, nchip, schip, pchip, &assigned_point)?;

        Ok(assigned_point)
    }

    fn read_constant_point(
        &mut self,
        ctx: &mut A::Context,
        nchip: &A::NativeChip,
        schip: &A::ScalarChip,
        pchip: &A,
    ) -> Result<A::AssignedPoint, A::Error> {
        let mut compressed = C::Repr::default();
        self.reader.read_exact(compressed.as_mut())?;
        let point: C = Option::from(C::from_bytes(&compressed)).ok_or_else(|| {
            Error::Transcript(io::Error::new(
                io::ErrorKind::Other,
                "invalid point encoding in proof",
            ))
        })?;
        let assigned_point = pchip.assign_const(ctx, point)?;

        self.common_point(ctx, nchip, schip, pchip, &assigned_point)?;

        Ok(assigned_point)
    }

    fn read_scalar(
        &mut self,
        ctx: &mut A::Context,
        nchip: &A::NativeChip,
        schip: &A::ScalarChip,
    ) -> Result<A::AssignedScalar, A::Error> {
        let mut data = <C::Scalar as PrimeField>::Repr::default();
        self.reader.read_exact(data.as_mut())?;
        let scalar: C::Scalar = Option::from(C::Scalar::from_repr(data)).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "invalid field element encoding in proof",
            )
        })?;
        ctx.enter_transcript();
        let assigned_scalar = schip.assign_var(ctx, scalar)?;
        ctx.exit_transcript();

        self.common_scalar(ctx, nchip, schip, &assigned_scalar)?;

        Ok(assigned_scalar)
    }

    fn read_constant_scalar(
        &mut self,
        ctx: &mut A::Context,
        nchip: &A::NativeChip,
        schip: &A::ScalarChip,
    ) -> Result<A::AssignedScalar, A::Error> {
        let mut data = <C::Scalar as PrimeField>::Repr::default();
        self.reader.read_exact(data.as_mut())?;
        let scalar: C::Scalar = Option::from(C::Scalar::from_repr(data)).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "invalid field element encoding in proof",
            )
        })?;
        let assigned_scalar = schip.assign_const(ctx, scalar)?;

        self.common_scalar(ctx, nchip, schip, &assigned_scalar)?;

        Ok(assigned_scalar)
    }

    fn squeeze_challenge_scalar(
        &mut self,
        ctx: &mut A::Context,
        nchip: &A::NativeChip,
        schip: &A::ScalarChip,
    ) -> Result<A::AssignedScalar, A::Error> {
        ctx.enter_hash();
        let mut v = self.hash.squeeze(ctx, nchip)?;
        let e = ctx.squeeze_challenge_scalar();
        v.expr = e;
        let s = E::decode_scalar(ctx, nchip, schip, &[v])?;
        Ok(s)
    }

    fn common_point(
        &mut self,
        ctx: &mut A::Context,
        nchip: &A::NativeChip,
        schip: &A::ScalarChip,
        pchip: &A,
        p: &A::AssignedPoint,
    ) -> Result<(), A::Error> {
        let encoded = E::encode_point(ctx, nchip, schip, pchip, p)?;
        ctx.update(&p.expr);
        // ctx.update(&encoded[1].expr);
        self.hash.update(&encoded);
        Ok(())
    }

    fn common_scalar(
        &mut self,
        ctx: &mut A::Context,
        nchip: &A::NativeChip,
        schip: &A::ScalarChip,
        s: &A::AssignedScalar,
    ) -> Result<(), A::Error> {
        let encoded = E::encode_scalar(ctx, nchip, schip, s)?;
        ctx.update(&s.expr);
        self.hash.update(&encoded);
        Ok(())
    }
}
