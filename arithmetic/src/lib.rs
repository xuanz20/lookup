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