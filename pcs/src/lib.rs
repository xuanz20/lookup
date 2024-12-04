use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::Rng;
use std::fmt::Debug;

pub mod multilinear_kzg;
pub mod hyrax_kzg;
pub mod utils;

pub trait PolynomialCommitmentScheme<E: Pairing> {
    type SRS: Clone + Debug;
    type ProverParam: Clone + Sync;
    type VerifierParam: Clone + CanonicalSerialize + CanonicalDeserialize;
    type Commitment: Clone + CanonicalDeserialize + CanonicalSerialize + Debug;
    type Proof: Clone + CanonicalSerialize + CanonicalDeserialize + Debug;

    fn gen_srs<R: Rng>(
        rng: &mut R,
        supported_num_vars: usize,
    ) -> Self::SRS;

    fn trim(srs: &Self::SRS) -> (Self::ProverParam, Self::VerifierParam);

    fn commit(
        prover_param: &Self::ProverParam,
        eval: &Vec<E::ScalarField>,
    ) -> Self::Commitment;

    fn open(
        prover_param: &Self::ProverParam,
        eval: &Vec<E::ScalarField>,
        point: &[E::ScalarField],
    ) -> (Self::Proof, E::ScalarField);

    fn verify(
        verifier_param: &Self::VerifierParam,
        commitment: &Self::Commitment,
        point: &[E::ScalarField],
        proof: &Self::Proof,
        open_value: E::ScalarField,
    ) -> bool;
}


pub trait StructuredReferenceString<E: Pairing>: Sized {
    type ProverParam;
    type VerifierParam;

    fn extract_prover_param(&self, supported_num_vars: usize) -> Self::ProverParam;
    fn extract_verifier_param(&self, supported_num_vars: usize) -> Self::VerifierParam;
    fn trim(&self) -> (Self::ProverParam, Self::VerifierParam);
    fn gen_srs<R: Rng>(rng: &mut R, supported_num_vars: usize) -> Self;
}