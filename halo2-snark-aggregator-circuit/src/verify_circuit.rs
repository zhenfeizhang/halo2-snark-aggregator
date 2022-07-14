use super::chips::{ecc_chip::EccChip, encode_chip::PoseidonEncodeChip, scalar_chip::ScalarChip};
use crate::sample_circuit::TargetCircuit;
use halo2_ecc_circuit_lib::chips::integer_chip::IntegerChipOps;
use halo2_ecc_circuit_lib::five::integer_chip::FiveColumnIntegerChipHelper;
use halo2_ecc_circuit_lib::gates::base_gate::{BaseGateOps, AssignedValue};
use halo2_ecc_circuit_lib::chips::ecc_chip::{AssignedPoint};
use halo2_ecc_circuit_lib::utils::field_to_bn;
use halo2_ecc_circuit_lib::{
    chips::native_ecc_chip::NativeEccChip,
    five::{
        base_gate::{FiveColumnBaseGate, FiveColumnBaseGateConfig},
        integer_chip::FiveColumnIntegerChip,
        range_gate::FiveColumnRangeGate,
    },
    gates::{base_gate::Context, range_gate::RangeGateConfig},
};
use halo2_proofs::circuit::floor_planner::V1;
use halo2_proofs::plonk::{create_proof, keygen_vk, ProvingKey};
use halo2_proofs::plonk::{Column, Instance};
use halo2_proofs::{
    arithmetic::BaseExt,
    plonk::{keygen_pk, verify_proof, SingleVerifier},
    transcript::Challenge255,
};
use halo2_proofs::{
    arithmetic::{CurveAffine, MultiMillerLoop},
    circuit::Layouter,
    plonk::{Circuit, ConstraintSystem, Error, VerifyingKey},
    poly::commitment::{Params, ParamsVerifier},
};
use halo2_snark_aggregator_api::mock::arith::{ecc::{MockEccChip}, field::MockFieldChip};
use halo2_snark_aggregator_api::mock::transcript_encode::PoseidonEncode;
use halo2_snark_aggregator_api::systems::halo2::verify::{verify_aggregation_proofs_in_chip, CircuitProof};
use halo2_snark_aggregator_api::systems::halo2::{
    transcript::PoseidonTranscriptRead, verify::ProofData,
};
use halo2_snark_aggregator_api::transcript::sha::{ShaRead, ShaWrite};
use log::info;
use pairing_bn256::group::Curve;
use rand_core::OsRng;
use std::env::var;
use std::path::Path;
use std::{io::Read, marker::PhantomData};

const COMMON_RANGE_BITS: usize = 17usize;

#[derive(Clone)]
pub struct Halo2VerifierCircuitConfig {
    base_gate_config: FiveColumnBaseGateConfig,
    range_gate_config: RangeGateConfig,
    instance: Column<Instance>,
}

#[derive(Clone)]
pub struct SingleProofWitness<'a, E: MultiMillerLoop> {
    pub(crate) instances: &'a Vec<Vec<Vec<E::Scalar>>>,
    pub(crate) transcript: &'a Vec<u8>,
}

#[derive(Clone)]
pub struct Halo2VerifierCircuit<'a, E: MultiMillerLoop> {
    pub(crate) params: &'a ParamsVerifier<E>,
    pub(crate) vk: &'a VerifyingKey<E::G1Affine>,
    pub(crate) proofs: Vec<SingleProofWitness<'a, E>>,
    pub(crate) nproofs: usize,
}

#[derive(Clone)]
pub struct Halo2CircuitInstance<'a, E: MultiMillerLoop> {
    pub(crate) params: &'a ParamsVerifier<E>,
    pub(crate) vk: &'a VerifyingKey<E::G1Affine>,
    pub(crate) n_instances: Vec<Vec<Vec<Vec<E::Scalar>>>>,
    pub(crate) n_transcript: Vec<Vec<u8>>,
}

pub struct Halo2CircuitInstances<'a, E: MultiMillerLoop, const N: usize> ([Halo2CircuitInstance<'a, E>; N]);


impl<'a, C: CurveAffine, E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>, const N: usize>
    Halo2CircuitInstances<'a, E, N> {
    pub fn calc_verify_circuit_final_pair(
        &self
    ) -> (C, C, Vec<<C as CurveAffine>::ScalarExt>) {
        let nchip = MockFieldChip::<C::ScalarExt, Error>::default();
        let schip = MockFieldChip::<C::ScalarExt, Error>::default();
        let pchip = MockEccChip::<C, Error>::default();
        let ctx = &mut ();

        let circuit_proofs = self.0.iter().map(|instance| {
            let mut proof_data_list = vec![];
            for (i, instances) in instance.n_instances.iter().enumerate() {
                let transcript = PoseidonTranscriptRead::<_, C, _, PoseidonEncode, 9usize, 8usize>::new(
                    &instance.n_transcript[i][..],
                    ctx,
                    &schip,
                    8usize,
                    33usize,
                )
                .unwrap();

                proof_data_list.push(ProofData {
                    instances,
                    transcript,
                    key: format!("p{}", i),
                    _phantom: PhantomData,
                })
            }


            CircuitProof {vk:instance.vk, params:instance.params, proofs:proof_data_list}

        }).collect();

        let empty_vec = vec![];
        let mut transcript = PoseidonTranscriptRead::<_, C, _, PoseidonEncode, 9usize, 8usize>::new(
            &empty_vec[..],
            ctx,
            &nchip,
            8usize,
            33usize,
        )
        .unwrap();


        let (w_x, w_g, instances) = verify_aggregation_proofs_in_chip(
            ctx,
            &nchip,
            &schip,
            &pchip,
            circuit_proofs,
            &mut transcript,
        )
        .unwrap();

        (w_x.to_affine(), w_g.to_affine(), instances)
    }
}

pub struct Halo2VerifierCircuits<'a, E: MultiMillerLoop, const N:usize> ([Halo2VerifierCircuit<'a, E>; N]);

impl<'a, C: CurveAffine, E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>, const N:usize>
    Circuit<C::ScalarExt> for Halo2VerifierCircuits<'a, E, N> {

    type Config = Halo2VerifierCircuitConfig;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Halo2VerifierCircuits(self.0.clone().map(|c| c.without_witnesses()))
    }
    fn configure(meta: &mut ConstraintSystem<C::ScalarExt>) -> Self::Config {
        let base_gate_config = FiveColumnBaseGate::configure(meta);
        let range_gate_config =
            FiveColumnRangeGate::<'_, C::Base, C::ScalarExt, COMMON_RANGE_BITS>::configure(
                meta,
                &base_gate_config,
            );

        let instance = meta.instance_column();
        meta.enable_equality(instance);

        Self::Config {
            base_gate_config,
            range_gate_config,
            instance,
        }
    }
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<C::ScalarExt>,
    ) -> Result<(), Error> {
        let base_gate = FiveColumnBaseGate::new(config.base_gate_config.clone());
        let range_gate = FiveColumnRangeGate::<'_, C::Base, C::ScalarExt, COMMON_RANGE_BITS>::new(
            config.range_gate_config.clone(),
            &base_gate,
        );

        let mut layouter = layouter.namespace(|| "mult-circuit");
        let mut res = self.synthesize_proof(&base_gate, &range_gate, &mut layouter)?;

        let integer_chip = FiveColumnIntegerChip::new(&range_gate);

        let mut x0_low = None;
        let mut x0_high = None;
        let mut x1_low = None;
        let mut x1_high = None;
        let mut instances = None;

        layouter.assign_region(
            || "base",
            |region| {
                let base_offset = 0usize;
                let mut aux = Context::new(region, base_offset);
                let ctx = &mut aux;

                integer_chip.reduce(ctx, &mut res.0.x)?;
                integer_chip.reduce(ctx, &mut res.0.y)?;
                integer_chip.reduce(ctx, &mut res.1.x)?;
                integer_chip.reduce(ctx, &mut res.1.y)?;

                // It uses last bit to identify y and -y, so the w_modulus must be odd.
                assert!(integer_chip.helper.w_modulus.bit(0));

                let y0_bit = integer_chip.get_last_bit(ctx, &res.0.y)?;
                let y1_bit = integer_chip.get_last_bit(ctx, &res.1.y)?;

                let zero = C::ScalarExt::from(0);

                let x0_low_ = base_gate.sum_with_constant(
                    ctx,
                    vec![
                        (
                            &res.0.x.limbs_le[0],
                            integer_chip.helper.limb_modulus_exps[0],
                        ),
                        (
                            &res.0.x.limbs_le[1],
                            integer_chip.helper.limb_modulus_exps[1],
                        ),
                    ],
                    zero,
                )?;

                let x0_high_ = base_gate.sum_with_constant(
                    ctx,
                    vec![
                        (
                            &res.0.x.limbs_le[2],
                            integer_chip.helper.limb_modulus_exps[0],
                        ),
                        (
                            &res.0.x.limbs_le[3],
                            integer_chip.helper.limb_modulus_exps[1],
                        ),
                        (&y0_bit, integer_chip.helper.limb_modulus_exps[2]),
                    ],
                    zero,
                )?;

                let x1_low_ = base_gate.sum_with_constant(
                    ctx,
                    vec![
                        (
                            &res.1.x.limbs_le[0],
                            integer_chip.helper.limb_modulus_exps[0],
                        ),
                        (
                            &res.1.x.limbs_le[1],
                            integer_chip.helper.limb_modulus_exps[1],
                        ),
                    ],
                    zero,
                )?;

                let x1_high_ = base_gate.sum_with_constant(
                    ctx,
                    vec![
                        (
                            &res.1.x.limbs_le[2],
                            integer_chip.helper.limb_modulus_exps[0],
                        ),
                        (
                            &res.1.x.limbs_le[3],
                            integer_chip.helper.limb_modulus_exps[1],
                        ),
                        (&y1_bit, integer_chip.helper.limb_modulus_exps[2]),
                    ],
                    zero,
                )?;

                x0_low = Some(x0_low_);
                x0_high = Some(x0_high_);
                x1_low = Some(x1_low_);
                x1_high = Some(x1_high_);
                instances = Some(res.2.clone());
                Ok(())
            },
        )?;


        Ok ({
            let mut layouter = layouter.namespace(|| "expose");
            layouter.constrain_instance(x0_low.unwrap().cell, config.instance, 0)?;
            layouter.constrain_instance(x0_high.unwrap().cell, config.instance, 1)?;
            layouter.constrain_instance(x1_low.unwrap().cell, config.instance, 2)?;
            layouter.constrain_instance(x1_high.unwrap().cell, config.instance, 3)?;
            let mut row = 4;
            for instance in instances.unwrap() {
                layouter
                    .constrain_instance(instance.cell, config.instance, row)
                    .unwrap();
                row = row + 1;
            }
        })

    }
}


impl<'a, C: CurveAffine, E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>, const N: usize>
    Halo2VerifierCircuits<'a, E, N> {
    fn synthesize_proof(
        &self,
        base_gate: &FiveColumnBaseGate<C::ScalarExt>,
        range_gate: &FiveColumnRangeGate<'_, C::Base, C::ScalarExt, COMMON_RANGE_BITS>,
        layouter: &mut impl Layouter<C::ScalarExt>,
    ) ->Result<(AssignedPoint<C, <C as CurveAffine>::ScalarExt>,
                AssignedPoint<C, <C as CurveAffine>::ScalarExt>,
                Vec<AssignedValue<<C as CurveAffine>::ScalarExt>>,
        ), Error> {
        let integer_chip = FiveColumnIntegerChip::new(range_gate);
        let ecc_chip = NativeEccChip::new(&integer_chip);
        range_gate
            .init_table(layouter, &integer_chip.helper.integer_modulus)
            .unwrap();

        let nchip = &ScalarChip::new(base_gate);
        let schip = nchip;
        let pchip = &EccChip::new(&ecc_chip);

        let mut r = None;

        layouter.assign_region(
            || "base",
            |region| {
                let base_offset = 0usize;
                let mut aux = Context::new(region, base_offset);
                let ctx = &mut aux;

                let circuit_proofs = self.0.iter().map(|instance| {
                    let mut proof_data_list: Vec<
                        ProofData<
                            E,
                            _,
                            PoseidonTranscriptRead<_, C, _, PoseidonEncodeChip<_>, 9usize, 8usize>,
                        >,
                    > = vec![];

                    for i in 0..instance.nproofs {
                        let transcript = PoseidonTranscriptRead::<
                            _,
                            C,
                            _,
                            PoseidonEncodeChip<_>,
                            9usize,
                            8usize,
                        >::new(
                            &instance.proofs[i].transcript[..], ctx, schip, 8usize, 33usize
                        )?;

                        proof_data_list.push(ProofData {
                            instances: &instance.proofs[i].instances,
                            transcript,
                            key: format!("p{}", i),
                            _phantom: PhantomData,
                        })
                    }

                    Ok(CircuitProof {vk: instance.vk, params: instance.params, proofs: proof_data_list})

                }).into_iter().collect::<Result<Vec<CircuitProof<_,_,_>>, Error>>()?;

                let empty_vec = vec![];
                let mut transcript =
                    PoseidonTranscriptRead::<_, C, _, PoseidonEncodeChip<_>, 9usize, 8usize>::new(
                        &empty_vec[..],
                        ctx,
                        schip,
                        8usize,
                        33usize,
                    )?;
                let res = verify_aggregation_proofs_in_chip(
                    ctx,
                    nchip,
                    schip,
                    pchip,
                    circuit_proofs,
                    &mut transcript,
                )?;

                base_gate.assert_false(ctx, &res.0.z)?;
                base_gate.assert_false(ctx, &res.1.z)?;
                r = Some (res);
                Ok(())

            },
        )?;

        Ok(r.unwrap())

    }
}

impl<'a, C: CurveAffine, E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>>
    Circuit<C::ScalarExt> for Halo2VerifierCircuit<'a, E>
{
    type Config = Halo2VerifierCircuitConfig;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self {
            params: self.params,
            vk: self.vk,
            proofs: (0..self.nproofs).map(|_| self.proofs[0].clone()).collect(),
            nproofs: self.nproofs,
        }
    }

    fn configure(meta: &mut ConstraintSystem<C::ScalarExt>) -> Self::Config {
        let base_gate_config = FiveColumnBaseGate::configure(meta);
        let range_gate_config =
            FiveColumnRangeGate::<'_, C::Base, C::ScalarExt, COMMON_RANGE_BITS>::configure(
                meta,
                &base_gate_config,
            );

        let instance = meta.instance_column();
        meta.enable_equality(instance);

        Self::Config {
            base_gate_config,
            range_gate_config,
            instance,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        layouter: impl Layouter<C::ScalarExt>,
    ) -> Result<(), Error> {
        Halo2VerifierCircuits ([self.clone()]).synthesize(config, layouter)
    }
}

fn verify_circuit_builder<'a, C: CurveAffine, E: MultiMillerLoop<G1Affine = C>>(
    params: &'a ParamsVerifier<E>,
    vk: &'a VerifyingKey<E::G1Affine>,
    instances: &'a Vec<Vec<Vec<Vec<E::Scalar>>>>,
    transcript: &'a Vec<Vec<u8>>,
    nproofs: usize,
) -> Halo2VerifierCircuit<'a, E> {
    Halo2VerifierCircuit {
        params,
        vk,
        nproofs,
        proofs: instances
            .iter()
            .zip(transcript.iter())
            .map(|(i, t)| SingleProofWitness {
                instances: i,
                transcript: t,
            })
            .collect(),
    }
}

pub fn load_params<C: CurveAffine>(folder: &mut std::path::PathBuf, file_name: &str) -> Params<C> {
    folder.push(file_name);
    let mut fd = std::fs::File::open(folder.as_path()).unwrap();
    folder.pop();
    Params::<C>::read(&mut fd).unwrap()
}

pub fn load_transcript<C: CurveAffine>(
    folder: &mut std::path::PathBuf,
    file_name: &str,
) -> Vec<u8> {
    folder.push(file_name);
    let mut fd = std::fs::File::open(folder.as_path()).unwrap();
    folder.pop();

    let mut buf = vec![];
    fd.read_to_end(&mut buf).unwrap();
    buf
}

pub fn load_instances<E: MultiMillerLoop>(buf: &[u8]) -> Vec<Vec<Vec<E::Scalar>>> {
    let mut ret = vec![];
    let cursor = &mut std::io::Cursor::new(buf);

    while let Ok(a) = <E::Scalar as BaseExt>::read(cursor) {
        ret.push(a);
    }

    vec![vec![ret]]
}

pub struct Setup<'a, C: CurveAffine> {
    pub target_circuit_params: &'a Params<C>,
    pub target_circuit_vk: &'a VerifyingKey<C>,
    pub target_circuit_instances: Vec<Vec<Vec<Vec<C::ScalarExt>>>>,
    pub proofs: Vec<Vec<u8>>,
    pub nproofs: usize,
}
impl<C: CurveAffine> Setup<'_, C> {
    fn new_verify_circuit_info<
        E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>,
        CIRCUIT: TargetCircuit<C, E>,
    >(
        &self,
        setup: bool,
    ) -> (
        ParamsVerifier<E>,
        Vec<Vec<Vec<Vec<E::Scalar>>>>,
        Vec<Vec<u8>>,
    ) {
        let target_circuit_verifier_params = self
            .target_circuit_params
            .verifier::<E>(self.target_circuit_vk.cs.num_instance_columns)
            .unwrap();

        let mut target_circuit_transcripts = vec![];
        let mut target_circuit_instances = vec![];

        for i in 0..self.nproofs {
            let index = if setup { 0 } else { i };
            target_circuit_transcripts.push(self.proofs[index].clone());
            target_circuit_instances.push(self.target_circuit_instances[index].clone());
        }

        (
            target_circuit_verifier_params,
            target_circuit_instances,
            target_circuit_transcripts,
        )
    }

    fn get_params_cached<E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>>(
        k: u32,
    ) -> Params<C> {
        let params_path = format!("HALO2_PARAMS_{}", k);

        let path = var(params_path);
        let path = match &path {
            Ok(path) => {
                let path = Path::new(path);
                Some(path)
            }
            _ => None,
        };

        println!("params path: {:?}", path);
        if path.is_some() && Path::exists(&path.unwrap()) {
            println!("read params from {:?}", path.unwrap());
            let mut fd = std::fs::File::open(&path.unwrap()).unwrap();
            Params::<C>::read(&mut fd).unwrap()
        } else {
            let params = Params::<C>::unsafe_setup::<E>(k);

            if let Some(path) = path {
                println!("write params to {:?}", path);

                let mut fd = std::fs::File::create(path).unwrap();

                params.write(&mut fd).unwrap();
            };

            params
        }
    }

    pub fn call<
        E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>,
        CIRCUIT: TargetCircuit<C, E>,
        const VERIFY_CIRCUIT_K: u32,
    >(
        &self,
    ) -> (Params<C>, VerifyingKey<C>) {
        let sample_circuit_info = self.new_verify_circuit_info::<E, CIRCUIT>(true);
        let verify_circuit = verify_circuit_builder(
            &sample_circuit_info.0,
            &self.target_circuit_vk,
            &sample_circuit_info.1,
            &sample_circuit_info.2,
            self.nproofs,
        );
        info!("circuit build done");

        // TODO: Do not use this setup in production
        let verify_circuit_params = Self::get_params_cached::<E>(VERIFY_CIRCUIT_K);
        info!("setup params done");

        let verify_circuit_vk =
            keygen_vk(&verify_circuit_params, &verify_circuit).expect("keygen_vk should not fail");
        info!("setup vkey done");

        (verify_circuit_params, verify_circuit_vk)
    }
}

pub fn final_pair_to_instances<
    C: CurveAffine,
    E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>,
>(
    pair: &(C, C, Vec<E::Scalar>),
) -> Vec<C::ScalarExt> {
    let helper = FiveColumnIntegerChipHelper::<C::Base, C::ScalarExt>::new();
    let w_x_x = helper.w_to_limb_n_le(&pair.0.coordinates().unwrap().x());
    let w_x_y = helper.w_to_limb_n_le(&pair.0.coordinates().unwrap().y());
    let w_g_x = helper.w_to_limb_n_le(&pair.1.coordinates().unwrap().x());
    let w_g_y = helper.w_to_limb_n_le(&pair.1.coordinates().unwrap().y());

    let get_last_bit = |n| {
        if field_to_bn(n).bit(0) {
            helper.limb_modulus_exps[2]
        } else {
            C::ScalarExt::from(0)
        }
    };

    let mut verify_circuit_instances = vec![
        (w_x_x[0] * helper.limb_modulus_exps[0] + w_x_x[1] * helper.limb_modulus_exps[1]),
        (w_x_x[2] * helper.limb_modulus_exps[0]
            + w_x_x[3] * helper.limb_modulus_exps[1]
            + get_last_bit(&w_x_y[0])),
        (w_g_x[0] * helper.limb_modulus_exps[0] + w_g_x[1] * helper.limb_modulus_exps[1]),
        (w_g_x[2] * helper.limb_modulus_exps[0]
            + w_g_x[3] * helper.limb_modulus_exps[1]
            + get_last_bit(&w_g_y[0])),
    ];

    pair.2.iter().for_each(|instance| {
        verify_circuit_instances.push(*instance);
    });

    verify_circuit_instances
}

pub fn calc_verify_circuit_instances<
    C: CurveAffine,
    E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>,
>(
    params: &ParamsVerifier<E>,
    vk: &VerifyingKey<C>,
    n_instances: Vec<Vec<Vec<Vec<E::Scalar>>>>,
    n_transcript: Vec<Vec<u8>>,
) -> Vec<C::ScalarExt> {
    let pair = Halo2CircuitInstances([Halo2CircuitInstance{params, vk, n_instances, n_transcript}])
        .calc_verify_circuit_final_pair();
    final_pair_to_instances::<C, E>(&pair)
}

pub struct CreateProof<'a, C: CurveAffine> {
    pub target_circuit_params: &'a Params<C>,
    pub target_circuit_vk: &'a VerifyingKey<C>,
    pub verify_circuit_params: &'a Params<C>,
    pub verify_circuit_vk: VerifyingKey<C>,
    pub template_instances: Vec<Vec<Vec<Vec<C::ScalarExt>>>>,
    pub template_proofs: Vec<Vec<u8>>,
    pub instances: Vec<Vec<Vec<Vec<C::ScalarExt>>>>,
    pub proofs: Vec<Vec<u8>>,
    pub nproofs: usize,
}

impl<C: CurveAffine> CreateProof<'_, C> {
    pub fn call<
        E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>,
        CIRCUIT: TargetCircuit<C, E>,
    >(
        self,
    ) -> (
        ProvingKey<C>,
        (C, C, Vec<C::ScalarExt>),
        Vec<C::ScalarExt>,
        Vec<u8>,
    ) {
        let setup = Setup {
            target_circuit_params: self.target_circuit_params,
            target_circuit_vk: &self.target_circuit_vk,
            target_circuit_instances: self.template_instances.clone(),
            proofs: self.template_proofs.clone(),
            nproofs: self.nproofs,
        };

        let now = std::time::Instant::now();
        let target_circuit_params_verifier = {
            let sample_circuit_info = setup.new_verify_circuit_info::<E, CIRCUIT>(false);
            sample_circuit_info.0
        };

        let sample_circuit_info = setup.new_verify_circuit_info::<E, CIRCUIT>(false);
        let verify_circuit = verify_circuit_builder(
            &sample_circuit_info.0,
            &self.target_circuit_vk,
            &sample_circuit_info.1,
            &sample_circuit_info.2,
            self.nproofs,
        );

        let (instances, transcripts) = {
            let mut verify_circuit_transcripts = vec![];
            let mut verify_circuit_instances = vec![];

            for i in 0..self.nproofs {
                verify_circuit_transcripts.push(self.proofs[i].clone());
                verify_circuit_instances.push(self.instances[i].clone());
            }

            (verify_circuit_instances, verify_circuit_transcripts)
        };

        let verify_circuit_final_pair = Halo2CircuitInstances([Halo2CircuitInstance {
                params: &target_circuit_params_verifier,
                vk: &self.target_circuit_vk,
                n_instances: instances,
                n_transcript: transcripts,
            }]).calc_verify_circuit_final_pair();

        let verify_circuit_instances = final_pair_to_instances::<C, E>(&verify_circuit_final_pair);

        let verify_circuit_pk = keygen_pk(
            &self.verify_circuit_params,
            self.verify_circuit_vk,
            &verify_circuit,
        )
        .expect("keygen_pk should not fail");

        let elapsed_time = now.elapsed();
        info!("Running keygen_pk took {} seconds.", elapsed_time.as_secs());

        let instances: &[&[&[C::ScalarExt]]] = &[&[&verify_circuit_instances[..]]];
        let mut transcript = ShaWrite::<_, _, Challenge255<_>, sha2::Sha256>::init(vec![]);
        create_proof(
            &self.verify_circuit_params,
            &verify_circuit_pk,
            &[verify_circuit],
            instances,
            OsRng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();

        let elapsed_time = now.elapsed();
        println!(
            "Running create proof took {} seconds.",
            elapsed_time.as_secs()
        );

        (
            verify_circuit_pk,
            verify_circuit_final_pair,
            verify_circuit_instances,
            proof,
        )
    }
}

pub struct VerifyCheck<'a, C: CurveAffine> {
    pub verify_params: &'a Params<C>,
    pub verify_vk: &'a VerifyingKey<C>,
    pub verify_instance: Vec<Vec<Vec<C::ScalarExt>>>,
    pub proof: Vec<u8>,
    pub nproofs: usize,
}

impl<C: CurveAffine> VerifyCheck<'_, C> {
    pub fn call<
        E: MultiMillerLoop<G1Affine = C, Scalar = C::ScalarExt>,
        CIRCUIT: TargetCircuit<C, E>,
    >(
        &self,
    ) -> Result<(), Error> {
        let params = self
            .verify_params
            .verifier::<E>(4 + CIRCUIT::PUBLIC_INPUT_SIZE * self.nproofs)
            .unwrap();
        let strategy = SingleVerifier::new(&params);

        let verify_circuit_instance1: Vec<Vec<&[E::Scalar]>> = self
            .verify_instance
            .iter()
            .map(|x| x.iter().map(|y| &y[..]).collect())
            .collect();
        let verify_circuit_instance2: Vec<&[&[E::Scalar]]> =
            verify_circuit_instance1.iter().map(|x| &x[..]).collect();

        let mut transcript = ShaRead::<_, _, Challenge255<_>, sha2::Sha256>::init(&self.proof[..]);

        verify_proof(
            &params,
            &self.verify_vk,
            strategy,
            &verify_circuit_instance2[..],
            &mut transcript,
        )
    }
}
