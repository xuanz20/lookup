use std::collections::VecDeque;

use arithmetic::multilinear_poly::{eq_eval, new_eq};
use ark_ff::PrimeField;
use merlin::Transcript;
use utils::{append_serializable_element, get_and_append_challenge};

use crate::sum_check::SumCheck;

pub struct ZeroCheck;

impl ZeroCheck {
    pub fn prove<F: PrimeField>(
        evals: Vec<Vec<F>>,
        transcript: &mut Transcript,
    ) -> (VecDeque<Vec<F>>, Vec<F>, Vec<F>) {
        let nv = evals[0].len().ilog2() as usize;
        let mut challenges = vec![];
        for _ in 0..nv {
            challenges.push(get_and_append_challenge(transcript, b"Internal round"));
        }
        let eq = new_eq(&challenges);
        let mut new_evals = evals;
        new_evals.push(eq);
        let (mut proof, new_challenges, values) = SumCheck::prove(
            new_evals,
            |v: Vec<F>| {v.iter().fold(F::one(), |mut acc, x| {
                acc *= x;
                acc
            })},
            transcript,
        );
        append_serializable_element(transcript, b"prover msg", &values);
        proof.push_back(values.clone());
        (proof, new_challenges, values)
    }

    pub fn verify<F: PrimeField>(
        num_var: usize,
        transcript: &mut Transcript,
        proof: &mut VecDeque<Vec<F>>
    ) -> (Vec<F>, Vec<F>) {
        let mut challenges = vec![];
        for _ in 0..num_var {
            challenges.push(get_and_append_challenge::<F>(transcript, b"Internal round"));
        }
        let (new_challenges, value) = SumCheck::verify(
            F::zero(),
            3,
            num_var,
            transcript,
            proof
        );
        let mut evals = proof.pop_front().unwrap();
        append_serializable_element(transcript, b"prover msg", &evals);
        let prod = evals.iter().fold(F::one(), |mut acc, x| {
            acc *= x;
            acc
        });

        // check the validity of value
        assert_eq!(value, prod);

        // check eq(r, r')
        let eq = evals.pop().unwrap();
        assert_eq!(eq, eq_eval(&challenges, &new_challenges));

        (new_challenges, evals)
    }
}

#[cfg(test)]
mod tests {
    use arithmetic::multilinear_poly::evaluate_on_point;
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_std::{test_rng, One, Zero, rand::Rng};
    use merlin::Transcript;

    use super::ZeroCheck;

    type F = <Bls12_381 as Pairing>::ScalarField;

    #[test]
    fn test_zero_check() {
        let mut rng = test_rng();
        let a: Vec<_> = (0..4096).map(|_| {F::from(rng.gen_range(0..2))}).collect();
        let b: Vec<_> = a.iter().map(|x| F::one() - *x).collect();
        for i in 0..4096 {
            assert_eq!(F::zero(), a[i] * b[i]);
        }
        let mut transcript = Transcript::new(b"ZeroCheck");
        let (mut proof, _, _) = ZeroCheck::prove(
            vec![a.clone(), b.clone()],
            &mut transcript,
        );

        let mut transcript = Transcript::new(b"ZeroCheck");
        let (r, v) = ZeroCheck::verify(
            12,
            &mut transcript,
            &mut proof,
        );

        assert_eq!(F::one(), v[0] + v[1]);

        assert_eq!(
            v[0],
            evaluate_on_point(&a, &r)
        );
    }

    #[test]
    fn test_bad_zero_check() {
        let mut rng = test_rng();
        let a: Vec<_> = (0..4096).map(|_| {F::from(rng.gen_range(1..3))}).collect();
        let b: Vec<_> = a.iter().map(|x| F::one() - *x).collect();
        let mut transcript = Transcript::new(b"ZeroCheck");
        let (mut proof, _, _) = ZeroCheck::prove(
            vec![a.clone(), b.clone()],
            &mut transcript,
        );

        let mut transcript = Transcript::new(b"ZeroCheck");
        let (r, v) = ZeroCheck::verify(12, &mut transcript, &mut proof);
        assert_eq!(F::one(), v[0] + v[1]);
        assert_eq!(v[0], evaluate_on_point(&a, &r));
    }
}