use ark_ff::PrimeField;
pub mod multilinear_poly;
pub mod univariate_poly;

pub fn power<F: PrimeField>(mut a: F, mut b: usize) -> F {
    let mut result = F::one();
    while b > 0 {
        if b % 2 != 0 {
            result = result * a;
        }
        a = a * a;
        b = b / 2;
    }
    result
}

pub fn batch_inverse<F: PrimeField>(v: &Vec<F>) -> Vec<F> {
    let len = v.len();
    let mut res = v.clone();
    for i in 1..len {
        let x = res[i - 1];
        res[i] *= x;
    }
    let mut inv = F::one() / res[len - 1];
    for i in (1..len).rev() {
        res[i] = inv * res[i - 1];
        inv *= v[i]
    }
    res[0] = inv;
    res
}