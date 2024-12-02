use std::collections::VecDeque;

use ark_ff::PrimeField;
use merlin::Transcript;
use utils::get_and_append_challenge;

use crate::grand_prod_check::GrandProdCheck;

pub struct PermCheck;

impl PermCheck {
    pub fn prove<F: PrimeField>(
        mut evals_0: Vec<F>,
        mut evals_1: Vec<F>,
        transcript: &mut Transcript
    ) -> (VecDeque<Vec<F>>, [Vec<F>; 2], [F; 2]) {
        let mut proof: VecDeque<Vec<F>> = VecDeque::new();
        let r: F = get_and_append_challenge(transcript, b"Internal round");
        evals_0.iter_mut().for_each(|x| *x += r);
        evals_1.iter_mut().for_each(|x| *x += r);
        let (proof_0, challenges_0, value_0) = GrandProdCheck::prove(
            evals_0,
            transcript,
        );
        proof.extend(proof_0);
        let (proof_1, challenges_1, value_1) = GrandProdCheck::prove(
            evals_1,
            transcript,
        );
        proof.extend(proof_1);
        (proof, [challenges_0, challenges_1], [value_0 - r, value_1 - r])
    }

    pub fn verify<F: PrimeField>(
        layer_num: usize,
        transcript: &mut Transcript,
        proof: &mut VecDeque<Vec<F>>,
    ) -> ([Vec<F>; 2], [F; 2]) {
        let r: F = get_and_append_challenge(transcript, b"Internal round");
        let (prod_0, challenge_0, value_0) = GrandProdCheck::verify(
            layer_num,
            transcript,
            proof,
        );
        let (prod_1, challenge_1, value_1) = GrandProdCheck::verify(
            layer_num,
            transcript,
            proof,
        );
        assert_eq!(prod_0, prod_1);
        ([challenge_0, challenge_1], [value_0 - r, value_1 - r])
    }
}

#[cfg(test)]
mod tests {
    use arithmetic::multilinear_poly::evaluate_on_point;
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_std::{test_rng, UniformRand, One};
    use merlin::Transcript;
    use rand::seq::SliceRandom;

    use super::PermCheck;

    type F = <Bls12_381 as Pairing>::ScalarField;

    #[test]
    fn test_perm_check() {
        let mut rng = test_rng();
        let evals_0: Vec<_> = (0..4096).map(|_| F::rand(&mut rng)).collect();
        let mut evals_1 = evals_0.clone();
        evals_1.shuffle(&mut rng);

        let mut transcript = Transcript::new(b"PermCheck");
        let (mut proof, _, _) = PermCheck::prove(
            evals_0.clone(),
            evals_1.clone(),
            &mut transcript,
        );

        let prod_0 = evals_0.iter().fold(F::one(), |mut prod, x| {
            prod *= x;
            prod
        });
        let prod_1 = evals_1.iter().fold(F::one(), |mut prod, x| {
            prod *= x;
            prod
        });
        assert_eq!(prod_0, prod_1);

        let mut transcript = Transcript::new(b"PermCheck");
        let (challenges, values) = PermCheck::verify(
            12,
            &mut transcript,
            &mut proof,
        );
        assert_eq!(
            values[0],
            evaluate_on_point(&evals_0, &challenges[0])
        );
        assert_eq!(
            values[1],
            evaluate_on_point(&evals_1, &challenges[1])
        );
    }
}