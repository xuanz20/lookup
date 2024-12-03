use std::collections::VecDeque;
use arithmetic::{multilinear_poly::{eq_eval, evaluate_on_point, new_eq}, power};
use ark_ec::pairing::Pairing;
use ark_std::{end_timer, start_timer, One, Zero};
use merlin::Transcript;
use pcs::{
    hyrax_kzg::HyraxKzgPCS, multilinear_kzg::data_structures::MultilinearVerifierParam, PolynomialCommitmentScheme
};
use poly_iop::{grand_prod_check::GrandProdCheck, perm_check::PermCheck, sum_check::SumCheck, zero_check::ZeroCheck};
use utils::{append_serializable_element, get_and_append_challenge};

use crate::{Lookup, LookupProof};

type PCS<E> = HyraxKzgPCS<E>;
type VerifierParam<E> = MultilinearVerifierParam<E>;

impl Lookup {
    pub fn verify<E: Pairing> (
        a: &Vec<E::ScalarField>,
        t: &Vec<E::ScalarField>,
        commit_a: &Vec<<E as Pairing>::G1Affine>,
        vk: &VerifierParam<E>,
        proof: &LookupProof<E>,
        transcript: &mut Transcript,
    ) {
        let m = a.len();
        let n = t.len();
        let s = ((m + 1) as f64).sqrt().ceil() as usize;
        let len = (n + s).next_power_of_two();
        let pad = len - n - s;
        let num_vars = len.ilog2() as usize;

        let mut affine_deque = proof.affine_deque.clone();
        let mut field_deque = proof.field_deque.clone();

        let commit_u1 = affine_deque.pop_front().unwrap();
        let commit_u2 = affine_deque.pop_front().unwrap();
        let commit_q1 = affine_deque.pop_front().unwrap();
        let commit_q2 = affine_deque.pop_front().unwrap();
        append_serializable_element(transcript, b"commitnent", &commit_u1);
        append_serializable_element(transcript, b"commitnent", &commit_u2);
        append_serializable_element(transcript, b"commitnent", &commit_q1);
        append_serializable_element(transcript, b"commitnent", &commit_q2);

        let step = start_timer!(|| "verify u and q");
        // verify the validity of u and q:
        // 1. u is a permutation of t and 0
        // 2. q_i is 0 or 1
        // 3. u_i * q_i is 0
        // 4. u's and q's pad 0
        let mut perm = vec![E::ScalarField::zero(); len - n];
        perm.extend(t.clone());
        let mut f_mask = vec![E::ScalarField::one(); pad];
        f_mask.resize(len, E::ScalarField::zero());
        verify_u_and_q(&commit_u1, &commit_q1, &perm, &f_mask, vk, &mut field_deque, &mut affine_deque, transcript);
        verify_u_and_q(&commit_u2, &commit_q2, &perm, &f_mask, vk, &mut field_deque, &mut affine_deque, transcript);
        end_timer!(step);
        
        let r = get_and_append_challenge::<E::ScalarField>(transcript, b"Internal round");
        
        // verify \pi (r - a_i) = \pi (r - t_i)^{e_i}
        // verify \pi (r - a_i)
        let step = start_timer!(|| "grand prod check");
        let (y, challenges, value) = GrandProdCheck::verify(m.ilog2() as usize, transcript, &mut field_deque);
        end_timer!(step);
        let step = start_timer!(|| "open a");
        let open_value = r - value;
        let proof = affine_deque.pop_front().unwrap();
        append_serializable_element(transcript, b"open", &proof);
        assert!(PCS::<E>::verify(vk, commit_a, &challenges, &proof, open_value));
        end_timer!(step);

        // verify \pi (r - t_i)^{e_i} = r1 * r2^s
        let eval = field_deque.pop_front().unwrap();
        append_serializable_element(transcript, b"value", &eval);
        let r1 = eval[0];
        let r2 = eval[1];
        assert_eq!(y, r1 * power(r2, s));

        // verify r{j} * r^{s(s+1)/2} = \pi (d{j}_i * q{j}_i + 1 - q{j}_i)
        let commit_d1 = affine_deque.pop_front().unwrap();
        let commit_d2 = affine_deque.pop_front().unwrap();
        append_serializable_element(transcript, b"commitment", &commit_d1);
        append_serializable_element(transcript, b"commitment", &commit_d2);

        // verify the validity of d:
        let step = start_timer!(|| "verify d");
        verify_d(&commit_d1, &commit_u1, len, r, vk, &mut field_deque, &mut affine_deque, transcript);
        verify_d(&commit_d2, &commit_u2, len, r, vk, &mut field_deque, &mut affine_deque, transcript);
        end_timer!(step);

        
        // verify r{j} * r^{s(s+1)/2} = \pi (d{j}_i * q{j}_i + 1 - q{j}_i)
        let step = start_timer!(|| "verify d and q");
        verify_d_and_q(&commit_d1, &commit_q1, num_vars, s, r1, r, vk, &mut field_deque, &mut affine_deque, transcript);
        verify_d_and_q(&commit_d2, &commit_q2, num_vars, s, r2, r, vk, &mut field_deque, &mut affine_deque, transcript);
        end_timer!(step);
        // Finish verify!!!
    } 
}

fn verify_u_and_q<E: Pairing>(
    commit_u: &Vec<<E as Pairing>::G1Affine>,
    commit_q: &Vec<<E as Pairing>::G1Affine>,
    perm: &Vec<E::ScalarField>,
    f_mask: &Vec<E::ScalarField>,
    vk: &VerifierParam<E>,
    field_deque: &mut VecDeque<Vec<<E as Pairing>::ScalarField>>,
    affine_deque: &mut VecDeque<Vec<<E as Pairing>::G1Affine>>,
    transcript: &mut Transcript,
) {
    let num_vars = perm.len().ilog2() as usize;
    // 1. perm check u:
    let (challenges, values) = PermCheck::verify(num_vars, transcript, field_deque);
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, &commit_u, &challenges[0], &proof, values[0]));
    assert_eq!(values[1], evaluate_on_point(&perm, &challenges[1]));

    // 2. verify u_i * q_i = 0
    let (challenges, values) = ZeroCheck::verify(num_vars, transcript, field_deque);
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, &commit_u, &challenges, &proof, values[0]));
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, &commit_q, &challenges, &proof, values[1]));

    // 3. verify q_i = 0 / 1
    // prove q1_i * (1 - q1_i) = 0
    let (challenges, values) = ZeroCheck::verify(num_vars, transcript, field_deque);
    assert_eq!(E::ScalarField::one(), values[0] + values[1]);
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, &commit_q, &challenges, &proof, values[0]));

    // 4. verify u's and q's pad 0
    let (challenges, values) = ZeroCheck::verify(num_vars, transcript, field_deque);
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, &commit_u, &challenges, &proof, values[0]));
    assert_eq!(values[1], evaluate_on_point(&f_mask, &challenges));
    let (challenges, values) = ZeroCheck::verify(num_vars, transcript, field_deque);
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, &commit_q, &challenges, &proof, values[0]));
    assert_eq!(values[1], evaluate_on_point(&f_mask, &challenges));
}

fn verify_d<E: Pairing>(
    commit_d: &Vec<<E as Pairing>::G1Affine>,
    commit_u: &Vec<<E as Pairing>::G1Affine>,
    len: usize,
    r: <E as Pairing>::ScalarField,
    vk: &VerifierParam<E>,
    field_deque: &mut VecDeque<Vec<<E as Pairing>::ScalarField>>,
    affine_deque: &mut VecDeque<Vec<<E as Pairing>::G1Affine>>,
    mut transcript: &mut Transcript,
) {
    let num_vars = len.ilog2() as usize;
    let alpha = get_and_append_challenge::<E::ScalarField>(&mut transcript, b"");
    let mut alpha_1 = vec![E::ScalarField::zero(); len];
    let mut alpha_2 = vec![E::ScalarField::zero(); len];
    let mut tmp = alpha;
    for i in 0..len - 1 {
        alpha_1[i] = tmp;
        alpha_2[i + 1] = tmp;
        tmp *= alpha;
    }
    let eval = field_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"value", &eval);
    let sum_1 = eval[0];
    let sum_2 = eval[1];
    assert_eq!(sum_1, sum_2);
    let (challenge, value) = SumCheck::verify(sum_1, 2, num_vars, transcript, field_deque);
    let open_value = field_deque.pop_front().unwrap().pop().unwrap();
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"value", &open_value);
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, commit_d, &challenge, &proof, open_value));
    let mut alpha_power = vec![alpha; num_vars];
    for i in 1..num_vars {
        alpha_power[i] = alpha_power[i - 1] * alpha_power[i - 1];
    }
    // assert_eq!(value, open_value * evaluate_on_point(&alpha_1, &challenge));
    assert_eq!(
        value,
        open_value * (
            alpha * (0..num_vars).fold(E::ScalarField::one(), |mut acc, i| {
                acc *= alpha_power[i] * challenge[i] + E::ScalarField::one() - challenge[i];
                acc
            }) - alpha_power[num_vars - 1] * alpha_power[num_vars - 1] * (0..num_vars).fold(E::ScalarField::one(), |mut acc, i| {
                acc *= challenge[i];
                acc
            })
        )
    );

    let (challenge, value) = SumCheck::verify(sum_2, 3, num_vars, transcript, field_deque);
    let open_d = field_deque.pop_front().unwrap().pop().unwrap();
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"value", &open_d);
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, commit_d, &challenge, &proof, open_d));
    let open_u = field_deque.pop_front().unwrap().pop().unwrap();
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"value", &open_u);
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, commit_u, &challenge, &proof, open_u));
    // assert_eq!(value, open_d * (r - open_u) * evaluate_on_point(&alpha_2, &challenge));
    assert_eq!(value, open_d * (r - open_u) * (
        (0..num_vars).fold(E::ScalarField::one(), |mut acc, i| {
            acc *= alpha_power[i] * challenge[i] + E::ScalarField::one() - challenge[i];
            acc
        }) - (0..num_vars).fold(E::ScalarField::one(), |mut acc, i| {
            acc *= E::ScalarField::one() - challenge[i];
            acc
        })
    ));
}

fn verify_d_and_q<E: Pairing>(
    commit_d: &Vec<<E as Pairing>::G1Affine>,
    commit_q: &Vec<<E as Pairing>::G1Affine>,
    num_vars: usize,
    s: usize,
    rj: <E as Pairing>::ScalarField,
    r: <E as Pairing>::ScalarField,
    vk: &VerifierParam<E>,
    field_deque: &mut VecDeque<Vec<<E as Pairing>::ScalarField>>,
    affine_deque: &mut VecDeque<Vec<<E as Pairing>::G1Affine>>,
    transcript: &mut Transcript,
) {
    // verify R_j * r^{s(s+1)/2} = \pi (d_i * q_i + 1 - q_i)
    let (prod, point, value) = GrandProdCheck::verify(num_vars, transcript, field_deque);
    assert_eq!(rj * power(r, s * (s - 1) / 2), prod);
    // prove value = \sum_{i} eq(challenge, i) * (d_i * q_i + 1 - q_i)
    let (challenge, value) = SumCheck::verify(value, 3, num_vars, transcript, field_deque);
    let open_d = field_deque.pop_front().unwrap().pop().unwrap();
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"value", &open_d);
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, &commit_d, &challenge, &proof, open_d));
    let open_q = field_deque.pop_front().unwrap().pop().unwrap();
    let proof = affine_deque.pop_front().unwrap();
    append_serializable_element(transcript, b"value", &open_q);
    append_serializable_element(transcript, b"open", &proof);
    assert!(PCS::<E>::verify(vk, &commit_q, &challenge, &proof, open_q));
    assert_eq!(value, eq_eval(&point, &challenge) * (open_d * open_q + E::ScalarField::one() - open_q));
}