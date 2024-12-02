use ark_ff::PrimeField;

/// TODO: How to batch inverse?
pub fn uni_extroplate<F: PrimeField>(v: &[F], x: F) -> F {
    let n = v.len() - 1;
    let base = {
        let mut res = vec![];
        for i in 0..=n {
            let mut prod = F::one();
            for j in 0..=n {
                if j != i {
                    prod /= F::from(i as u32) - F::from(j as u32);
                }
            }
            res.push(prod);
        }
        res
    };

    let factorial = {
        let mut res = F::one();
        for i in 0..=n {
            res *= x - F::from(i as u32);
        }
        res
    };

    let mut res = F::zero();
    for i in 0..=n {
        res += v[i] * base[i] / (x - F::from(i as u32));
    }

    res * factorial
}