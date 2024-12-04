use std::collections::VecDeque;

use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::Rng;
use merlin::Transcript;

#[macro_export]
macro_rules! to_bytes {
    ($x:expr) => {{
        let mut buf = ark_std::vec![];
        ark_serialize::CanonicalSerialize::serialize_compressed($x, &mut buf).map(|_| buf)
    }};
}

pub fn append_serializable_element<S: CanonicalSerialize>(
    transcript: &mut Transcript,
    label: &'static [u8],
    group_element: &S,
) -> () {
    transcript.append_message(label, &to_bytes!(group_element).unwrap());
}

pub fn get_and_append_challenge<F: PrimeField>(transcript: &mut Transcript, label: &'static [u8]) -> F {
    let mut buf = [0u8; 64];
    transcript.challenge_bytes(label, &mut buf);
    let challenge = F::from_le_bytes_mod_order(&buf);
    transcript.append_message(label, &to_bytes!(&challenge).unwrap());
    challenge
}

pub fn rand_eval<F: PrimeField, R: Rng>(num_vars: usize, rng: &mut R) -> Vec<F> {
    (0..(1 << num_vars)).map(|_| F::rand(rng)).collect()
}

pub fn get_size<E>(deque: &VecDeque<Vec<E>>) -> f64 {
    let mut total_size: usize = 0;
    for vec in deque {
        total_size += size_of::<Vec<E>>();
        total_size += vec.capacity() * size_of::<E>();
    }
    total_size as f64 / 1024.0
}