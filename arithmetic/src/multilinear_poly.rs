use ark_ff::PrimeField;

pub fn new_eq<F: PrimeField>(point: &[F]) -> Vec<F> {
    let mut evals = vec![F::one()];
    for b in point.iter().rev() {
        evals = evals.iter().flat_map(|prod| [*prod * (F::one() - b), *prod * b]).collect();
    }
    evals
}

pub fn bind_vars<F: PrimeField>(eval: &[F], point: &[F]) -> Vec<F> {
    let num_vars = eval.len().ilog2() as usize;
    let num_bind = point.len();
    let mut res = eval.to_vec();
    for i in 0..num_bind {
        for j in 0..(1 << (num_vars - i - 1)) {
            res[j] = res[j << 1] + (res[(j << 1) + 1] - res[j << 1]) * point[i];
        }
        res.truncate(1 << (num_vars - i - 1));
    }
    res
}

pub fn evaluate_on_point<F: PrimeField>(eval: &[F], point: &[F]) -> F {
    let res = bind_vars(eval, point);
    res[0]
}

/// Evaluate eq(t, X) at a point
pub fn eq_eval<F: PrimeField>(x: &[F], y: &[F]) -> F {
    if x.len() != y.len() {
        panic!("x and y have different length");
    }
    let mut res = F::one();
    for (&xi, &yi) in x.iter().zip(y.iter()) {
        let xi_yi = xi * yi;
        res *= xi_yi + xi_yi - xi - yi + F::one();
    }
    res
}