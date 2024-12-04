use arithmetic::multilinear_poly::{bind_vars, new_eq};
use ark_ec::{
    pairing::Pairing, CurveGroup, VariableBaseMSM,
};
use ark_std::{
    marker::PhantomData, rand::Rng,
};
use crate::{
    multilinear_kzg::{data_structures::{
        MultilinearProverParam, MultilinearUniversalParams, MultilinearVerifierParam
    }, open_internal, verify_internal},
    utils::vector_to_matrix, PolynomialCommitmentScheme, StructuredReferenceString,
};

pub struct HyraxKzgPCS2<E: Pairing> {
    phantom: PhantomData<E>,
}

impl<E: Pairing> PolynomialCommitmentScheme<E> for HyraxKzgPCS2<E> {
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
        let l_prime = 2 * l.ilog2() as usize;
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
        let l_prime = 2 * l.ilog2() as usize;
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
        let l_prime = 2 * l.ilog2() as usize;
        let new_eq = new_eq(&point[..l_prime]);
        let commitment = E::G1::msm_unchecked(&commitment, &new_eq).into_affine();
        let point = &point[l_prime..];
        verify_internal(verifier_param, &commitment, point, proof, value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_std::{test_rng, UniformRand};
    use utils::rand_eval;

    type E = Bls12_381;
    type F = <E as Pairing>::ScalarField;

    fn test_single_helper<R: Rng>(
        srs: &MultilinearUniversalParams<E>,
        eval: &Vec<F>,
        rng: &mut R,
    ) {
        let num_vars = eval.len().ilog2();
        let (ck, vk) = HyraxKzgPCS2::trim(srs);
        let commit = HyraxKzgPCS2::commit(&ck, eval);
        let point: Vec<_> = (0..num_vars).map(|_| F::rand(rng)).collect();
        let (proof, value) = HyraxKzgPCS2::open(&ck, eval, &point);
        assert!(HyraxKzgPCS2::verify(&vk, &commit, &point, &proof, value));
        let value = F::rand(rng);
        assert!(!HyraxKzgPCS2::verify(&vk, &commit, &point, &proof, value));
    }

    #[test]
    fn test_single_commit() {
        let mut rng = test_rng();
        let srs  = HyraxKzgPCS2::<E>::gen_srs(&mut rng, 10);
        let eval_1 = rand_eval(10, &mut rng);
        test_single_helper(&srs, &eval_1, &mut rng);
    }
}