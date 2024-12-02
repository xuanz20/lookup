use std::ops::Mul;
use arithmetic::multilinear_poly::evaluate_on_point;
use ark_ec::{
    pairing::{Pairing, PairingOutput}, scalar_mul::{fixed_base::FixedBase, variable_base::VariableBaseMSM}, AffineRepr, CurveGroup
};
use ark_ff::PrimeField;
use ark_std::{
    marker::PhantomData, rand::Rng, Zero, One,
};
use crate::{PolynomialCommitmentScheme, StructuredReferenceString};
use data_structures::*;

pub mod data_structures;

pub struct MultilinearKzgPCS<E: Pairing> {
    phantom: PhantomData<E>,
}

impl<E: Pairing> PolynomialCommitmentScheme<E> for MultilinearKzgPCS<E> {
    type SRS = MultilinearUniversalParams<E>;
    type ProverParam = MultilinearProverParam<E>;
    type VerifierParam = MultilinearVerifierParam<E>;
    type Commitment = E::G1Affine;
    type Proof = Vec<E::G1Affine>;

    fn gen_srs<R: Rng>(rng: &mut R, log_size: usize) -> Self::SRS {
        Self::SRS::gen_srs(rng, log_size)
    }

    fn trim(srs: &Self::SRS) -> (Self::ProverParam, Self::VerifierParam) {
        srs.trim()
    }

    fn commit(
        prover_param: &Self::ProverParam,
        eval: &Vec<E::ScalarField>,
    ) -> Self::Commitment {
        let num_vars = eval.len().ilog2() as usize;
        let ignored = prover_param.num_vars - num_vars;
        let commitment = E::G1::msm_unchecked(&prover_param.powers_of_g[ignored].evals, eval).into_affine();
        commitment
    }

    fn open(
        prover_param: &Self::ProverParam,
        eval: &Vec<E::ScalarField>,
        point: &[E::ScalarField],
    ) -> (Self::Proof, E::ScalarField) {
        open_internal(prover_param, eval, point)
    }

    fn verify(
        verifier_param: &Self::VerifierParam,
        commitment: &Self::Commitment,
        point: &[E::ScalarField],
        proof: &Self::Proof,
        value: E::ScalarField,
    ) -> bool {
        verify_internal(verifier_param, commitment, point, proof, value)
    }
}

// On input a polynomial 'p' and a point 'point', outputs a proof
pub fn open_internal<E: Pairing>(
    prover_param: &MultilinearProverParam<E>,
    eval: &[E::ScalarField],
    point: &[E::ScalarField],
 ) -> (Vec<E::G1Affine>, E::ScalarField) {
    let num_vars = eval.len().ilog2() as usize;
    let ignored = prover_param.num_vars - num_vars + 1;
    let mut f = eval.to_vec();
    
    let mut proof = Vec::new();

    // High level idea of open:
    // q(X_{1, {2, ..., nv}}) = (X1 - z1) * w1(X_{2, ..., l}) + r1(X_{2, ..., l})
    // when X1 changes from 0 to 1, r1 remains the same
    // q(1, X_{2, ..., nv}) - q(0, X_{2, ..., nv}) = w1(X_{2, ..., nv})
    for (i, (&zi, gi)) in point.iter()
        .zip(prover_param.powers_of_g[ignored..ignored+num_vars].iter())
        .enumerate()
    {   
        let cur_num_vars = num_vars - i - 1;
        let mut w = vec![E::ScalarField::zero(); 1 << cur_num_vars];
        let mut r = vec![E::ScalarField::zero(); 1 << cur_num_vars];

        // w[b] = f[1, b] - f[0, b]
        // r[b] = f[0, b] + zi * w[b]
        for b in 0..(1 << cur_num_vars) {
            w[b] = f[(b << 1) + 1] - f[b << 1];
            r[b] = f[b << 1] + (zi * w[b])
        }
        
        f = r;
        proof.push(E::G1::msm_unchecked(&gi.evals, &w).into_affine());
    }
    let eval = evaluate_on_point(eval, point);
    (proof, eval)
}

pub fn verify_internal<E: Pairing>(
    verifier_param: &MultilinearVerifierParam<E>,
    commitment: &E::G1Affine,
    point: &[E::ScalarField],
    proof: &[E::G1Affine],
    value: E::ScalarField,
) -> bool {
    let num_vars = point.len();
    let scalar_size = E::ScalarField::MODULUS_BIT_SIZE as usize;
    let h_mul: Vec<E::G2> = {
        let window = FixedBase::get_mul_window_size(num_vars);
        let h_table = FixedBase::get_window_table(scalar_size, window, verifier_param.h.into_group());
        FixedBase::msm(scalar_size, window, &h_table, point)
    };

    let ignored = verifier_param.num_vars - num_vars;
    let h_vec: Vec<_> = (0..num_vars).map(|i| verifier_param.h_mask[ignored + i].into_group() - h_mul[i]).collect();
    let h_vec = E::G2::normalize_batch(&h_vec);

    let mut pairings: Vec<_> = proof.iter().map(|&x| E::G1Prepared::from(x))
        .zip(h_vec.into_iter().map(E::G2Prepared::from)).collect();
    
    // add pairing e(g * v - c, g)
    pairings.push((
        E::G1Prepared::from(
            (verifier_param.g.mul(value) - commitment.into_group()).into_affine(),
        ),
        E::G2Prepared::from(verifier_param.h),
    ));

    let ps = pairings.iter().map(|(p, _)| p.clone());
    let hs = pairings.iter().map(|(_, h)| h.clone());

    let res = E::multi_pairing(ps, hs) == PairingOutput(E::TargetField::one());

    res
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
        let (ck, vk) = MultilinearKzgPCS::trim(srs);
        let commit = MultilinearKzgPCS::commit(&ck, eval);
        let point: Vec<_> = (0..num_vars).map(|_| F::rand(rng)).collect();
        let (proof, value) = MultilinearKzgPCS::open(&ck, eval, &point);
        assert!(MultilinearKzgPCS::verify(&vk, &commit, &point, &proof, value));
        let value = F::rand(rng);
        assert!(!MultilinearKzgPCS::verify(&vk, &commit, &point, &proof, value));
    }

    #[test]
    fn test_single_commit() {
        let mut rng = test_rng();
        let srs  = MultilinearKzgPCS::<E>::gen_srs(&mut rng, 10);
        let (ck, vk) = MultilinearKzgPCS::trim(&srs);

        // let eval_1 = rand_eval(8, &mut rng);
        // test_single_helper(&srs, &eval_1, &mut rng);

        let eval_1 = rand_eval(8, &mut rng);
        let eval_2 = rand_eval(8, &mut rng);
        let eval_3: Vec<_> = (0..(1<<8)).map(|i| eval_1[i] + eval_2[i]).collect();
        let ignored = ck.num_vars - 8;
        let commit_1 = <E as Pairing>::G1::msm_unchecked(&ck.powers_of_g[ignored].evals, &eval_1);
        let commit_2 = <E as Pairing>::G1::msm_unchecked(&ck.powers_of_g[ignored].evals, &eval_2);
        let commit_3 = <E as Pairing>::G1::msm_unchecked(&ck.powers_of_g[ignored].evals, &eval_3);
        assert_eq!(commit_3, commit_1 + commit_2);
        let commit_1 = commit_1.into_affine();
        let commit_2 = commit_2.into_affine();
        let commit_3 = commit_3.into_affine();
        let commit = <E as Pairing>::G1::msm_unchecked(&vec![commit_1, commit_2], &[F::from(1), F::from(1)]).into_affine();
        assert_eq!(commit, commit_3);


        // let eval_2 = rand_eval(1, &mut rng);
        // test_single_helper(&srs, &eval_2, &mut rng);
    }
}