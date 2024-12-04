use std::collections::{HashMap, VecDeque};

use arithmetic::{batch_inverse, multilinear_poly::new_eq};
use ark_ec::pairing::Pairing;
use ark_std::{end_timer, start_timer, Zero};
use merlin::Transcript;
use pcs::PolynomialCommitmentScheme;
use poly_iop::sum_check::SumCheck;
use utils::{append_serializable_element, get_and_append_challenge};

use crate::{Logup, LogupProof, ProverParam, PCS};

impl Logup {
    pub fn prove<E: Pairing> (
        a: &Vec<E::ScalarField>,
        t: &Vec<E::ScalarField>,
        pk: &ProverParam<E>,
        transcript: &mut Transcript,
    ) -> LogupProof<E> {
        let m = a.len();
        let n = t.len();

        let mut affine_deque: VecDeque<Vec<<E as Pairing>::G1Affine>> = VecDeque::new();
        let mut field_deque: VecDeque<Vec<<E as Pairing>::ScalarField>> = VecDeque::new();

        // compute e
        let mut count_map = HashMap::new();
        for ai in a {
            *count_map.entry(ai).or_insert(0) += 1;
        }
        let e: Vec<_> = t.iter().map(|ti| *count_map.get(ti).unwrap_or(&0)).collect();
        let e: Vec<_> = e.iter().map(|x| E::ScalarField::from(*x as u32)).collect();

        let r = get_and_append_challenge::<E::ScalarField>(transcript, b"Internal round");

        // let f: Vec<_> = a.iter().map(|x| E::ScalarField::one() / (r + x)).collect();
        let f = batch_inverse(&a.iter().map(|x| r + x).collect());
        // let g: Vec<_> = t.iter().map(|x| E::ScalarField::one() / (r + x)).collect();
        let g = batch_inverse(&t.iter().map(|x| r + x).collect());

        // commit f
        let commit_f = PCS::<E>::commit(pk, &f);
        append_serializable_element(transcript, b"commitment", &commit_f);
        affine_deque.push_back(commit_f);
        // commit g
        let commit_g = PCS::<E>::commit(pk, &g);
        append_serializable_element(transcript, b"commitment", &commit_g);
        affine_deque.push_back(commit_g);
        // commit e
        let commit_e = PCS::<E>::commit(pk, &e);
        append_serializable_element(transcript, b"commitment", &commit_e);
        affine_deque.push_back(commit_e);

        // prove \sum_i f_i = \sum_i g_i * e_i
        let sum_1 = f.iter().sum();
        let sum_2 = (0..n).fold(E::ScalarField::zero(), |mut acc, i| {
            acc += g[i] * e[i];
            acc
        });
        assert_eq!(sum_1, sum_2);
        append_serializable_element(transcript, b"value", &vec![sum_1, sum_2]);
        field_deque.push_back(vec![sum_1, sum_2]);
        // sum-check on \sum_i f_i
        let (proof, challenges, _) = SumCheck::prove(vec![f.clone()], |v| v[0], transcript);
        field_deque.extend(proof);
        let (proof, _) = PCS::<E>::open(pk, &f, &challenges);
        append_serializable_element(transcript, b"open", &proof);
        affine_deque.push_back(proof);
        // sum-check on \sum_i g_i * e_i
        let (proof, challenges, _) = SumCheck::prove(vec![g.clone(), e.clone()], |v| v[0] * v[1], transcript);
        field_deque.extend(proof);
        let (proof, open_g) = PCS::<E>::open(pk, &g, &challenges);
        append_serializable_element(transcript, b"open", &proof);
        affine_deque.push_back(proof);
        let (proof, open_e) = PCS::<E>::open(pk, &e, &challenges);
        append_serializable_element(transcript, b"open", &proof);
        affine_deque.push_back(proof);
        append_serializable_element(transcript, b"value", &vec![open_g, open_e]);
        field_deque.push_back(vec![open_g, open_e]);

        // prove \sum_i eq(r', i) * f_i * (r + a_i) = 1
        let point: Vec<_> = (0..m.ilog2() as usize).map(|_| get_and_append_challenge::<E::ScalarField>(transcript, b"")).collect();
        let eq = new_eq(&point);
        let (proof, challenge, _) = SumCheck::prove(vec![eq, f.clone(), a.iter().map(|x| r+x).collect()], |v| v[0] * v[1] * v[2], transcript);
        field_deque.extend(proof);
        let (proof, open_f) = PCS::<E>::open(pk, &f, &challenge);
        append_serializable_element(transcript, b"open", &proof);
        affine_deque.push_back(proof);
        let (proof, open_a) = PCS::<E>::open(pk, &a, &challenge);
        append_serializable_element(transcript, b"open", &proof);
        affine_deque.push_back(proof);
        append_serializable_element(transcript, b"value", &vec![open_f, open_a]);
        field_deque.push_back(vec![open_f, open_a]);

        // prove \sum_i eq(r', i) * g_i * (r + t_i) = 1
        let point: Vec<_> = (0..n.ilog2() as usize).map(|_| get_and_append_challenge::<E::ScalarField>(transcript, b"")).collect();
        let eq = new_eq(&point);
        let (proof, challenges, _) = SumCheck::prove(vec![eq.clone(), g.clone(), t.iter().map(|x| r+x).collect()], |v| v[0] * v[1] * v[2], transcript);
        field_deque.extend(proof);
        let (proof, open_value) = PCS::<E>::open(pk, &g, &challenges);
        append_serializable_element(transcript, b"open", &proof);
        affine_deque.push_back(proof);
        append_serializable_element(transcript, b"value", &open_value);
        field_deque.push_back(vec![open_value]);

        LogupProof {
            affine_deque: affine_deque,
            field_deque: field_deque,
        }
    }
}