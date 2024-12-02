use std::collections::VecDeque;

use arithmetic::univariate_poly::uni_extroplate;
use ark_ff::PrimeField;
use merlin::Transcript;
use utils::{append_serializable_element, get_and_append_challenge};


pub struct SumCheck;

impl SumCheck {
    fn fold_next_domain<F: PrimeField>(poly_evals: &mut Vec<F>, challenge: F) {
        let l = poly_evals.len() / 2;
        for i in 0..l {
            poly_evals[i] = 
                poly_evals[i * 2] + (poly_evals[i * 2 + 1] - poly_evals[i * 2]) * challenge;
        }
        poly_evals.truncate(l);
    }

    /// sum-check on product of multilinear polys: f(x) = p1(x) * ... * p_D(x)
    /// evals: bookkeeping tables of p1, ..., p_D
    /// D: number of multilinear polys and the degree of f(x) on each variate
    /// return value:
    /// - proofs sent from the prover
    /// - random challenge r
    /// - p1(r), ..., p_D(r): x get bound to r (need by the verifier)
    #[allow(non_snake_case)]
    pub fn prove<F: PrimeField, FUNC: Fn(Vec<F>) -> F>(
        mut evals: Vec<Vec<F>>,
        f: FUNC,
        transcript: &mut Transcript,
    ) -> (VecDeque<Vec<F>>, Vec<F>, Vec<F>) {
        let D = evals.len();
        let nv = evals[0].len().ilog2() as usize;
        let mut proof: VecDeque<Vec<F>> = VecDeque::new();
        let mut challenges = vec![];

        for i in 0..nv {
            // in the j-th round, prover send f_j(0), ..., f_j(D)
            let m = 1usize << (nv - i);
            // sums: f_j(0), ..., f_j(D)
            let sums = (0..m).step_by(2).fold(
                vec![F::zero(); D + 1],
                |mut acc, x| {
                    // (x_{j+1}, ..., x_nv) gets bound to x
                    // f_j(k) += p1_j(x, k) * ... * pD_j(x, k)
                    // compute all p1_j(x, k), ..., pD_j(x, k)
                    // values: [[p1(x, 0), p1(x, 1), ..., p1(x, D)],
                    //          [p2(x, 0), p2(x, 1), ..., p2(x, D)],
                    //          ...,
                    //          [pD(x, 0), pD(x, 1), ..., pD(x, D)]]
                    let values = {
                        let mut res = vec![];
                        for j in 0..D {
                            let v_0 = evals[j][x];
                            let v_1 = evals[j][x + 1];
                            let diff = v_1 - v_0;
                            let mut e = vec![];
                            e.push(v_0);
                            for d in 1..=D {
                                e.push(e[d - 1] + diff);
                            }
                            res.push(e);
                        }
                        res
                    };
                    for k in 0..=D {
                        // sums[k] += p1_j(x, k) * ... * pD_j(x, k)
                        let mut input = vec![];
                        for row in 0..D {
                            input.push(values[row][k]);
                        }
                        let prod = f(input);
                        acc[k] += prod;
                    }
                    acc
                }
            );
            
            // Prover sends {f_j(0), ..., f_j(D)}
            append_serializable_element(transcript, b"prover msg", &sums);
            proof.push_back(sums);

            // bind the j-th variate to random field element
            let challenge = get_and_append_challenge(transcript, b"Internal round");
            challenges.push(challenge);

            for j in evals.iter_mut() {
                Self::fold_next_domain(j, challenge);
            }
        }
        (proof, challenges, evals.iter().map(|x| x[0]).collect())
    }

    pub fn verify<F: PrimeField>(
        y: F,
        degree: usize,
        num_var: usize,
        transcript: &mut Transcript,
        proof: &mut VecDeque<Vec<F>>
    ) -> (Vec<F>, F) {
        let mut r = vec![];
        let mut value = y;
        for _ in 0..num_var {
            let evals = proof.pop_front().unwrap();
            assert!(evals.len() <= degree + 1);
            append_serializable_element(transcript, b"prover msg", &evals);
            assert_eq!(evals[0] + evals[1], value);

            let challenge: F = get_and_append_challenge(transcript, b"Internal round");
            r.push(challenge);
            value = uni_extroplate(&evals, challenge);
        }
        (r, value)
    }
}

#[cfg(test)]
mod tests {
    use arithmetic::multilinear_poly::evaluate_on_point;
    use ark_bls12_381::Bls12_381;
    use ark_ec::pairing::Pairing;
    use ark_std::{test_rng, UniformRand, Zero};
    use merlin::Transcript;

    use super::SumCheck;

    type F = <Bls12_381 as Pairing>::ScalarField;

    #[test]
    fn test_sum_check() {
        let mut rng = test_rng();

        let a: Vec<_> = (0..4096).map(|_| F::rand(&mut rng)).collect();
        let b: Vec<_> = (0..4096).map(|_| F::rand(&mut rng)).collect();
        let c: Vec<_> = (0..4096).map(|_| F::rand(&mut rng)).collect();

        let mut transcript = Transcript::new(b"SumCheck");
        let (mut proof, _, _) = SumCheck::prove(
            vec![a.clone(), b.clone(), c.clone()],
            |v: Vec<F>| (v[0] * v[1] * v[2]),
            &mut transcript,
        );
        
        let y = (0..4096).fold(
            F::zero(),
            |acc, x| {
                acc + a[x] * b[x] * c[x]
            }
        );

        let mut transcript = Transcript::new(b"SumCheck");
        let (r, v) = SumCheck::verify(
            y,
            3,
            12,
            &mut transcript,
            &mut proof,
        );

        assert_eq!(
            evaluate_on_point(&a, &r)
                * evaluate_on_point(&b, &r)
                * evaluate_on_point(&c, &r),
            v
        );
    }
}