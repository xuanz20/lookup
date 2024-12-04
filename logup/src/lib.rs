use std::collections::VecDeque;

use ark_ec::pairing::Pairing;
use ark_std::test_rng;
use pcs::hyrax_kzg::hyrax_kzg_1::HyraxKzgPCS1;
use pcs::{
    multilinear_kzg::data_structures::{MultilinearProverParam, MultilinearVerifierParam}, PolynomialCommitmentScheme
};

mod prover;
mod verifier;

pub struct Logup;

pub struct LogupProof<E: Pairing> {
    affine_deque: VecDeque<Vec<<E as Pairing>::G1Affine>>,
    field_deque: VecDeque<Vec<<E as Pairing>::ScalarField>>,
}

impl<E: Pairing> LogupProof<E> {
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

type PCS<E> = HyraxKzgPCS1<E>;
type ProverParam<E> = MultilinearProverParam<E>;
type VerifierParam<E> = MultilinearVerifierParam<E>;

impl Logup {
    pub fn process<E: Pairing> (
        srs_num_vars: usize,
        a: &Vec<E::ScalarField>,
    ) -> (
        (ProverParam<E>, VerifierParam<E>),
        Vec<<E as Pairing>::G1Affine>,
    ) {
        let mut rng = test_rng();
        let srs = PCS::<E>::gen_srs(&mut rng, srs_num_vars);
        let (ck, vk) = PCS::<E>::trim(&srs);
        let commit = PCS::<E>::commit(&ck, a);
        ((ck, vk), commit)
    }
}

#[cfg(test)]
mod tests {
    use ark_ec::pairing::Pairing;
    use ark_std::{rand::seq::SliceRandom, test_rng};
    use merlin::Transcript;
    use crate::Logup;

    type E = ark_bn254::Bn254;
    type F = <E as Pairing>::ScalarField;

    const M: usize = 1 << 20;
    const N: usize = 1 << 8;

    #[test]
    fn test_logup() {
        let mut rng = test_rng();
        let t: Vec<_> = (1..=N).into_iter().map(|x| F::from(x as u32)).collect();
        let a: Vec<_> = (1..=M).into_iter().map(|_| t.choose(&mut rng).unwrap().clone()).collect();
        let mut transcript = Transcript::new(b"Logup");
        let ((pk, ck), commit) = Logup::process::<E>(20, &a); // srs for 20 variates is enough
        let proof = Logup::prove::<E>(&a, &t, &pk, &mut transcript);
        let mut transcript = Transcript::new(b"Logup");
        Logup::verify(&a, &t, &commit, &ck, &proof, &mut transcript);
    }
}