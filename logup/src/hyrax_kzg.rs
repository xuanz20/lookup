use arithmetic::multilinear_poly::{bind_vars, new_eq};
use ark_ec::{
    pairing::Pairing, CurveGroup, VariableBaseMSM,
};
use ark_std::{
    marker::PhantomData, rand::Rng,
};
use pcs::{
    multilinear_kzg::{data_structures::{
        MultilinearProverParam, MultilinearUniversalParams, MultilinearVerifierParam
    }, open_internal, verify_internal},
    utils::vector_to_matrix, PolynomialCommitmentScheme, StructuredReferenceString,
};

pub struct HyraxKzgPCS<E: Pairing> {
    phantom: PhantomData<E>,
}

impl<E: Pairing> PolynomialCommitmentScheme<E> for HyraxKzgPCS<E> {
    type SRS = MultilinearUniversalParams<E>;
    type ProverParam = MultilinearProverParam<E>;
    type VerifierParam = MultilinearVerifierParam<E>;
    type Commitment = Vec<E::G1Affine>;
    type Proof = Vec<E::G1Affine>;

    fn gen_srs<R: Rng>(rng: &mut R, l: usize) -> Self::SRS {
        Self::SRS::gen_srs(rng, l)
    }

    fn trim(srs: &Self::SRS) -> (Self::ProverParam, Self::VerifierParam) {
        srs.trim()
    }

    fn commit(
        prover_param: &Self::ProverParam,
        eval: &Vec<E::ScalarField>,
    ) -> Self::Commitment {
        let l = eval.len().ilog2() as usize;
        let l_prime = l.ilog2() as usize;
        let num_vars = l - l_prime;
        let ignored = prover_param.num_vars - num_vars;
        let u = vector_to_matrix(eval, l_prime);
        (0..(1 << l_prime)).map(|i| {
            E::G1::msm_unchecked(&prover_param.powers_of_g[ignored].evals, &u[i]).into_affine()
        }).collect()
    }

    fn open(
        prover_param: &Self::ProverParam,
        eval: &Vec<E::ScalarField>,
        point: &[E::ScalarField],
    ) -> (Self::Proof, E::ScalarField) {
        let l = point.len();
        let l_prime = l.ilog2() as usize;
        let eval = bind_vars(eval, &point[..l_prime]);
        let point = &point[l_prime..];
        open_internal(prover_param, &eval, point)
    }

    fn verify(
        verifier_param: &Self::VerifierParam,
        commitment: &Self::Commitment,
        point: &[E::ScalarField],
        proof: &Self::Proof,
        value: E::ScalarField,
    ) -> bool {
        let l = point.len();
        let l_prime = l.ilog2() as usize;
        let new_eq = new_eq(&point[..l_prime]);
        let commitment = E::G1::msm_unchecked(&commitment, &new_eq).into_affine();
        let point = &point[l_prime..];
        verify_internal(verifier_param, &commitment, point, proof, value)
    }
}