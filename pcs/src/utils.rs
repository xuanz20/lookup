use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;

/// input (t1, ..., t_nv) return vec[eq(t1, x1), eq(t2, x2), ..., eq(t_nv, x_nv)]
/// each eq(ti, xi) iterates (x1, ..., x_nv) in 2^nv
pub fn eq_extension<F: PrimeField>(t: &[F]) -> Vec<DenseMultilinearExtension<F>> {
    let dim = t.len();
    let mut result = Vec::new();
    for (i, &ti) in t.iter().enumerate() {
        let mut poly = Vec::with_capacity(1 << dim);
        for x in 0..(1 << dim) {
            let xi = if x >> i & 1 == 1 { F::one() } else { F::zero() };
            let ti_xi = ti * xi;
            poly.push(ti_xi + ti_xi - xi - ti + F::one()); // ti * xi + (1 - ti) * (1 - xi)
        }
        result.push(DenseMultilinearExtension::from_evaluations_vec(dim, poly));
    }
    result
}

pub fn remove_dummy_variable<F: PrimeField>(poly: &[F], pad: usize) -> Vec<F> {
    if pad == 0 {
        return poly.to_vec();
    }
    if !poly.len().is_power_of_two() {
        panic!("Size of polynomial should be power of two.");
    }
    let nv = ark_std::log2(poly.len()) as usize - pad;
    (0..(1 << nv)).map(|x| poly[x << pad]).collect()
}

pub fn vector_to_matrix<F: PrimeField>(vec: &Vec<F>, l_prime: usize) -> Vec<Vec<F>> {
    let l = vec.len().ilog2() as usize;
    let rows = 1 << l_prime;
    let cols = 1 << (l - l_prime);
    let mut res = vec![vec![F::zero(); cols]; rows];
    for i in 0..rows {
        for j in 0..cols {
            res[i][j] = vec[j * rows + i];
        }
    }
    res
}