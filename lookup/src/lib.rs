use std::collections::VecDeque;

use ark_ec::pairing::Pairing;
mod prover;
mod verifier;

pub struct Lookup;

pub struct LookupProof<E: Pairing> {
    affine_deque: VecDeque<Vec<<E as Pairing>::G1Affine>>,
    field_deque: VecDeque<Vec<<E as Pairing>::ScalarField>>,
}

impl<E: Pairing> LookupProof<E> {
    pub fn get_proof_size(&self) -> f64 {
        let mut total_size: usize = 0;
        total_size += size_of::<Self>();
        for vec in &self.affine_deque {
            total_size += size_of::<Vec<<E as Pairing>::G1Affine>>();
            total_size += vec.capacity() * size_of::<<E as Pairing>::G1Affine>();
        }
        for vec in &self.field_deque {
            total_size += size_of::<Vec<<E as Pairing>::ScalarField>>();
            total_size += vec.capacity() * size_of::<<E as Pairing>::ScalarField>();
        }
        total_size as f64 / 1024.0
    }
}

#[cfg(test)]
mod tests {
    use ark_ec::pairing::Pairing;
    use ark_std::{rand::seq::SliceRandom, test_rng};
    use merlin::Transcript;
    use pcs::{hyrax_kzg::hyrax_kzg_2::HyraxKzgPCS2, PolynomialCommitmentScheme};
    use crate::Lookup;

    type E = ark_bn254::Bn254;
    type F = <E as Pairing>::ScalarField;
    type PCS<E> = HyraxKzgPCS2<E>;

    const M: usize = 1 << 8;
    const N: usize = 1 << 4;
    const SUPPORTED_SIZE: usize = 8;

    #[test]
    fn test_lookup() {
        let mut rng = test_rng();
        let t: Vec<_> = (1..=N).into_iter().map(|x| F::from(x as u32)).collect();
        let a: Vec<_> = (1..=M).into_iter().map(|_| t.choose(&mut rng).unwrap().clone()).collect();
        let mut transcript = Transcript::new(b"Lookup");
        let srs = PCS::<E>::gen_srs(&mut rng, SUPPORTED_SIZE);
        let (pk, vk) = PCS::<E>::trim(&srs);
        let commit = PCS::<E>::commit(&pk, &a);
        let proof = Lookup::prove::<E>(&a, &t, &pk, &mut transcript);
        let mut transcript = Transcript::new(b"Lookup");
        Lookup::verify(&a, &t, &commit, &vk, &proof, &mut transcript);
    }
}