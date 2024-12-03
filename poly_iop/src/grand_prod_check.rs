use std::collections::VecDeque;

use arithmetic::multilinear_poly::{eq_eval, new_eq};
use ark_ff::PrimeField;
use merlin::Transcript;
use utils::{append_serializable_element, get_and_append_challenge};

use crate::sum_check::SumCheck;

pub struct GrandProdCheck;

impl GrandProdCheck {
    /// prove the product of evals
    /// return value:
    /// - proofs sent from the prover
    /// - random challenge r (in the last round)
    /// - claimed value of evals' extension on point r
    pub fn prove<F: PrimeField>(
        evals: Vec<F>,
        transcript: &mut Transcript
    ) -> (VecDeque<Vec<F>>, Vec<F>, F) {
        let mut proof: VecDeque<Vec<F>> = VecDeque::new();

        // compute the product in each layer
        let layer_num = evals.len().ilog2() as usize;
        let mut products = vec![evals];
        for i in 1..layer_num {
            let last_prod = &products[i - 1];
            let mut new_prod = vec![];
            let m = 1 << (layer_num - i);
            for j in 0..m {
                new_prod.push(last_prod[j * 2] * last_prod[j * 2 + 1]);
            }
            products.push(new_prod);
        }

        // append the value of the last layer
        let prover_msg = vec![products[layer_num - 1][0], products[layer_num - 1][1]];
        append_serializable_element(transcript, b"prover msg", &prover_msg);
        proof.push_back(prover_msg);

        // sum-check V_{i+1}(r) = \sum_{p} V_i(p, 0) * V_i(p, 1) * eq(r, p)
        let mut point: Vec<F> = vec![get_and_append_challenge(transcript, b"Internal round")];
        let mut value = F::zero();
        for i in (0..layer_num - 1).rev() {
            let eq = new_eq(&point);
            let mut evals_0 = vec![];
            let mut evals_1 = vec![];
            for j in products[i].iter().enumerate() {
                if j.0 % 2 == 0 {
                    evals_0.push(*j.1);
                } else {
                    evals_1.push(*j.1);
                }
            }

            let (layer_proof, mut layer_challenges, layer_values) = SumCheck::prove(
                vec![evals_0, evals_1, eq],
                |v: Vec<F>| v[0] * v[1] * v[2],
                transcript
            );

            proof.extend(layer_proof);

            // append V_i(r', 0), V_i(r', 1), eq(r, r')
            append_serializable_element(transcript, b"prover msg", &layer_values);
            proof.push_back(layer_values.clone());

            // sum-check is reduced to check V_i(r', 0), V_i(r', 1), eq(r, r')
            // i.e. p is bound to random challenge r'
            // eq(r, r') can be verified by the verifier
            // checking V_i(r', 0), V_i(r', 1) is reduced to check V_i(r', r'')
            let challenge: F = get_and_append_challenge(transcript, b"Internal round");
            value = layer_values[0] + (layer_values[1] - layer_values[0]) * challenge;

            // now point: (r', r'')
            point = vec![challenge];
            point.append(&mut layer_challenges);
        }
        return (proof, point, value);
    }

    /// return value:
    /// - claimed product
    /// - random challenge r
    /// - claimed value of evals' extension on point r
    pub fn verify<F: PrimeField>(
        layer_num: usize,
        transcript: &mut Transcript,
        proof: &mut VecDeque<Vec<F>>
    ) -> (F, Vec<F>, F) {
        let mut evals = proof.pop_front().unwrap();
        append_serializable_element(transcript, b"prover msg", &evals);
        let y = evals[0] * evals[1];

        let mut challenge: F = get_and_append_challenge(transcript, b"Internal round");
        let mut point: Vec<F> = vec![challenge];
        let mut value = evals[0] + (evals[1] - evals[0]) * challenge;
        for i in (0..layer_num - 1).rev() {
            // first sum-check
            let (mut layer_challenges, layer_value) = SumCheck::verify(
                value,
                3,
                layer_num - i - 1,
                transcript,
                proof
            );

            // get the value of the last layer
            evals = proof.pop_front().unwrap();
            append_serializable_element(transcript, b"prover msg", &evals);

            // check the validity of layer_value
            assert_eq!(layer_value, evals[0] * evals[1] * evals[2]);
            
            // check eq(r, r') (evals[2])
            assert_eq!(evals[2], eq_eval(&point, &layer_challenges));

            challenge = get_and_append_challenge(transcript, b"Internal round");
            value = evals[0] + (evals[1] - evals[0]) * challenge;

            point = vec![challenge];
            point.append(&mut layer_challenges);
        }

        return (y, point, value);
    }
}

#[cfg(test)]
mod tests {
    use arithmetic::multilinear_poly::evaluate_on_point;
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_std::{test_rng, UniformRand, One};
    use merlin::Transcript;
    use super::GrandProdCheck;

    type F = <Bls12_381 as Pairing>::ScalarField;

    #[test]
    fn test_grand_prod_check() {
        let mut rng = test_rng();

        let evals: Vec<_> = (0..4096).map(|_| F::rand(&mut rng)).collect();

        let mut transcript = Transcript::new(b"GrandProdCheck");
        let (mut proof, _, _) = GrandProdCheck::prove(
            evals.clone(),
            &mut transcript
        );

        let y = (0..4096).fold(
            F::one(),
            |acc, x| {
                acc * evals[x]
            }
        );

        let mut transcript_ = Transcript::new(b"GrandProdCheck");
        let (prod, r, v) = GrandProdCheck::verify(
            12,
            &mut transcript_,
            &mut proof,
        );

        assert_eq!(y, prod);

        assert_eq!(
            v,
            evaluate_on_point(&evals, &r)
        );
    }
}