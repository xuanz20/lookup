use std::collections::{HashMap, VecDeque};
use arithmetic::{multilinear_poly::{evaluate_on_point, new_eq}, power};
use ark_ec::pairing::Pairing;
use ark_std::{One, Zero, start_timer, end_timer};
use merlin::Transcript;
use pcs::{
    hyrax_kzg::{hyrax_kzg_1::HyraxKzgPCS1, hyrax_kzg_2::HyraxKzgPCS2}, multilinear_kzg::data_structures::MultilinearProverParam, PolynomialCommitmentScheme
};
use poly_iop::{grand_prod_check::GrandProdCheck, perm_check::PermCheck, sum_check::SumCheck, zero_check::ZeroCheck};
use utils::{append_serializable_element, get_and_append_challenge};

use crate::{Lookup, LookupProof};

type PCS1<E> = HyraxKzgPCS1<E>;
type PCS2<E> = HyraxKzgPCS2<E>;
type ProverParam<E> = MultilinearProverParam<E>;

impl Lookup {
    pub fn prove<E: Pairing> (
        a: &Vec<E::ScalarField>,
        t: &Vec<E::ScalarField>,
        pk: &ProverParam<E>,
        transcript: &mut Transcript,
    ) -> LookupProof<E> {
        let m = a.len();
        let n = t.len();
        let s = ((m + 1) as f64).sqrt().ceil() as usize;

        let mut affine_deque: VecDeque<Vec<E::G1Affine>> = VecDeque::new();
        let mut field_deque: VecDeque<Vec<E::ScalarField>> = VecDeque::new();

        // compute e, e1, e2
        let mut count_map = HashMap::new();
        for ai in a {
            *count_map.entry(ai).or_insert(0) += 1;
        }
        let e: Vec<_> = t.iter().map(|ti| *count_map.get(ti).unwrap_or(&0)).collect();
        let e1: Vec<_> = e.iter().map(|ei| ei % (s as i32)).collect();
        let e2: Vec<_> = e.iter().map(|ei| ei / (s as i32)).collect();

        // compute u1, u2, q1, q2
        let mut u1_ = vec![vec![E::ScalarField::zero()]; s];
        let mut q1_ = vec![vec![E::ScalarField::one()]; s];
        for (i, ei) in e1.iter().enumerate() {
            u1_[*ei as usize].push(t[i]);
            q1_[*ei as usize].push(E::ScalarField::zero());
        }
        let u1_: Vec<_> = u1_.into_iter().flat_map(|mut v| {v.reverse(); v}).collect();
        let q1_: Vec<_> = q1_.into_iter().flat_map(|mut v| {v.reverse(); v}).collect();
        let mut u2_ = vec![vec![E::ScalarField::zero()]; s];
        let mut q2_ = vec![vec![E::ScalarField::one()]; s];
        for (i, ei) in e2.iter().enumerate() {
            u2_[*ei as usize].push(t[i]);
            q2_[*ei as usize].push(E::ScalarField::zero());
        }
        let u2_: Vec<_> = u2_.into_iter().flat_map(|mut v| {v.reverse(); v}).collect();
        let q2_: Vec<_> = q2_.into_iter().flat_map(|mut v| {v.reverse(); v}).collect();

        // pad 0 if necessary
        let len = (n + s).next_power_of_two();
        let pad = len - n - s;
        let mut u1 = vec![E::ScalarField::zero(); pad];
        let mut u2 = vec![E::ScalarField::zero(); pad];
        let mut q1 = vec![E::ScalarField::zero(); pad];
        let mut q2 = vec![E::ScalarField::zero(); pad];
        u1.extend(u1_);
        u2.extend(u2_);
        q1.extend(q1_);
        q2.extend(q2_);

        // commit u1, u2, q1, q2
        let commit_u1 = PCS1::<E>::commit(pk, &u1);
        let commit_u2 = PCS1::<E>::commit(pk, &u2);
        let commit_q1 = PCS1::<E>::commit(pk, &q1);
        let commit_q2 = PCS1::<E>::commit(pk, &q2);
        append_serializable_element(transcript, b"commitnent", &commit_u1);
        append_serializable_element(transcript, b"commitnent", &commit_u2);
        append_serializable_element(transcript, b"commitnent", &commit_q1);
        append_serializable_element(transcript, b"commitnent", &commit_q2);
        affine_deque.push_back(commit_u1);
        affine_deque.push_back(commit_u2);
        affine_deque.push_back(commit_q1);
        affine_deque.push_back(commit_q2);

        let mut u1_open: Vec<(Vec<E::ScalarField>, E::ScalarField)> = Vec::new();
        let mut u2_open: Vec<(Vec<E::ScalarField>, E::ScalarField)> = Vec::new();
        let mut q1_open: Vec<(Vec<E::ScalarField>, E::ScalarField)> = Vec::new();
        let mut q2_open: Vec<(Vec<E::ScalarField>, E::ScalarField)> = Vec::new();

        // prove the validity of u and q:
        // 1. u is a permutation of t and 0
        // 2. q_i is 0 or 1
        // 3. u_i * q_i is 0
        // 4. u's and q's pad 0
        let mut perm = vec![E::ScalarField::zero(); len - n];
        perm.extend(t.clone());
        let mut f_mask = vec![E::ScalarField::one(); pad];
        f_mask.resize(len, E::ScalarField::zero());
        check_u_and_q::<E>(&u1, &q1, &mut u1_open, &mut q1_open, &perm, &f_mask, &mut field_deque, transcript);
        check_u_and_q::<E>(&u2, &q2, &mut u2_open, &mut q2_open, &perm, &f_mask, &mut field_deque, transcript);

        let r = get_and_append_challenge::<E::ScalarField>(transcript, b"Internal round");

        // prove \pi (r - a_i) = \pi (r - t_i)^{e_i}
        // prove \pi (r - a_i)
        let eval: Vec<_> = a.iter().map(|x| r - x).collect();
        let (proof, challenge, _) = GrandProdCheck::prove(eval, transcript);
        field_deque.extend(proof);
        let (proof, _) = PCS2::<E>::open(pk, &a, &challenge);
        append_serializable_element(transcript, b"open", &proof);
        affine_deque.push_back(proof);

        // prove \pi (r - t_i)^{e_i} = r1 * r2^s
        let eval: Vec<_> = t.iter().map(|x| r - x).collect();
        let r1 = (0..n).fold(E::ScalarField::one(), |acc, i| acc * power(eval[i], e1[i] as usize));
        let r2 = (0..n).fold(E::ScalarField::one(), |acc, i| acc * power(eval[i], e2[i] as usize));
        append_serializable_element(transcript, b"value", &vec![r1, r2]);
        field_deque.push_back(vec![r1, r2]);
        
        // next prove r{j} * r^{s(s+1)/2} = \pi (d{j}_i * q{j}_i + 1 - q{j}_i):
        // compute and commit d{j}
        let mut d1 = vec![E::ScalarField::zero(); len];
        let mut _prod = E::ScalarField::one();
        for i in (0..len).rev() {
            d1[i] = _prod;
            _prod *= r - u1[i];
        }
        let mut d2 = vec![E::ScalarField::zero(); len];
        let mut _prod = E::ScalarField::one();
        for i in (0..len).rev() {
            d2[i] = _prod;
            _prod *= r - u2[i];
        }
        let commit_d1 = PCS1::<E>::commit(pk, &d1);
        let commit_d2 = PCS1::<E>::commit(pk, &d2);
        append_serializable_element(transcript, b"commitment", &commit_d1);
        append_serializable_element(transcript, b"commitment", &commit_d2);
        affine_deque.push_back(commit_d1);
        affine_deque.push_back(commit_d2);

        let mut d1_open: Vec<(Vec<E::ScalarField>, E::ScalarField)> = Vec::new();
        let mut d2_open: Vec<(Vec<E::ScalarField>, E::ScalarField)> = Vec::new();

        // prove the validity of d:
        prove_d::<E>(&d1, &u1, r, &mut d1_open, &mut u1_open, &mut field_deque, transcript);
        prove_d::<E>(&d2, &u2, r, &mut d2_open, &mut u2_open, &mut field_deque, transcript);
        
        prove_d_and_q::<E>(&d1, &q1, &mut d1_open, &mut q1_open, &mut field_deque, transcript);
        prove_d_and_q::<E>(&d2, &q2, &mut d2_open, &mut q2_open, &mut field_deque, transcript);

        batch_open(&u1, &u1_open, pk, &mut field_deque, &mut affine_deque, transcript);
        batch_open(&u2, &u2_open, pk, &mut field_deque, &mut affine_deque, transcript);
        batch_open(&q1, &q1_open, pk, &mut field_deque, &mut affine_deque, transcript);
        batch_open(&q2, &q2_open, pk, &mut field_deque, &mut affine_deque, transcript);
        batch_open(&d1, &d1_open, pk, &mut field_deque, &mut affine_deque, transcript);
        batch_open(&d2, &d2_open, pk, &mut field_deque, &mut affine_deque, transcript);

        // Finish prove!!!
        LookupProof {
            affine_deque: affine_deque,
            field_deque: field_deque,
        }
    }
}

fn check_u_and_q<E: Pairing>(
    u: &Vec<E::ScalarField>,
    q: &Vec<E::ScalarField>,
    u_open: &mut Vec<(Vec<E::ScalarField>, E::ScalarField)>,
    q_open: &mut Vec<(Vec<E::ScalarField>, E::ScalarField)>,
    perm: &Vec<E::ScalarField>,
    f_mask: &Vec<E::ScalarField>,
    field_deque: &mut VecDeque<Vec<E::ScalarField>>,
    transcript: &mut Transcript,
) {
    // 1. perm check u:
    let (proof, challenges, values) = PermCheck::prove(u.clone(), perm.clone(), transcript);
    field_deque.extend(proof);
    u_open.push((challenges[0].clone(), values[0]));

    // 2. prove u_i * q_i = 0
    let (proof, challenge, values) = ZeroCheck::prove(vec![u.clone(), q.clone()], transcript);
    field_deque.extend(proof);
    u_open.push((challenge.clone(), values[0]));
    q_open.push((challenge.clone(), values[1]));

    // 3. prove q_i = 0 / 1
    let q_: Vec<_> = q.iter().map(|x| E::ScalarField::one() - x).collect();
    let (proof, challenge, values) = ZeroCheck::prove(vec![q.clone(), q_], transcript);
    field_deque.extend(proof);
    q_open.push((challenge.clone(), values[0]));

    // 4. prove u's and q's pad 0
    let (proof, challenge, values) = ZeroCheck::prove(vec![u.clone(), f_mask.clone()], transcript);
    field_deque.extend(proof);
    u_open.push((challenge.clone(), values[0]));
    let (proof, challenge, values) = ZeroCheck::prove(vec![q.clone(), f_mask.clone()], transcript);
    field_deque.extend(proof);
    q_open.push((challenge.clone(), values[0]));
}

// d_i = d_{i+1} * u_{i+1}
// \sum d_i * alpha^{i+1} = d_{i+1} * u_{i+1} * alpha^{i+1} i = 0, ..., len - 2
fn prove_d<E: Pairing>(
    d: &Vec<E::ScalarField>,
    u: &Vec<E::ScalarField>,
    r: E::ScalarField,
    d_open: &mut Vec<(Vec<E::ScalarField>, E::ScalarField)>,
    u_open: &mut Vec<(Vec<E::ScalarField>, E::ScalarField)>,
    field_deque: &mut VecDeque<Vec<<E as Pairing>::ScalarField>>,
    mut transcript: &mut Transcript,
) {
    let len = d.len();
    let alpha = get_and_append_challenge::<E::ScalarField>(&mut transcript, b"");
    let mut alpha_1 = vec![E::ScalarField::zero(); len];
    let mut alpha_2 = vec![E::ScalarField::zero(); len];
    let mut tmp = alpha;
    let mut sum_1 = E::ScalarField::zero();
    let mut sum_2 = E::ScalarField::zero();
    for i in 0..len - 1 {
        alpha_1[i] = tmp;
        alpha_2[i + 1] = tmp;
        tmp *= alpha;
        sum_1 += d[i] * alpha_1[i];
        sum_2 += d[i + 1] * (r - u[i + 1]) * alpha_2[i + 1];
    }
    assert_eq!(sum_1, sum_2);
    append_serializable_element(transcript, b"value", &vec![sum_1, sum_2]);
    field_deque.push_back(vec![sum_1, sum_2]);
    let (proof, challenge, _) = SumCheck::prove(vec![d.clone(), alpha_1], |v| v[0] * v[1], &mut transcript);
    field_deque.extend(proof);
    let open_value = evaluate_on_point(d, &challenge);
    append_serializable_element(transcript, b"value", &open_value);
    field_deque.push_back(vec![open_value]);
    d_open.push((challenge.clone(), open_value));

    let (proof, challenge, _) = SumCheck::prove(
        vec![d.clone(), u.iter().map(|x| r - *x).collect(), alpha_2],
        |v| v[0] * v[1] * v[2],
        &mut transcript
    );
    field_deque.extend(proof);
    let open_d = evaluate_on_point(d, &challenge);
    append_serializable_element(transcript, b"value", &open_d);
    field_deque.push_back(vec![open_d]);
    d_open.push((challenge.clone(), open_d));
    let open_u = evaluate_on_point(u, &challenge);
    append_serializable_element(transcript, b"value", &open_u);
    field_deque.push_back(vec![open_u]);
    u_open.push((challenge.clone(), open_u));
}

fn prove_d_and_q<E: Pairing> (
    d: &Vec<E::ScalarField>,
    q: &Vec<E::ScalarField>,
    d_open: &mut Vec<(Vec<E::ScalarField>, E::ScalarField)>,
    q_open: &mut Vec<(Vec<E::ScalarField>, E::ScalarField)>,
    field_deque: &mut VecDeque<Vec<<E as Pairing>::ScalarField>>,
    transcript: &mut Transcript,
) {
    // grand product check of \pi (d_i * q_i + 1 - q_i)
    let len = d.len();
    let eval: Vec<_> = (0..len).map(|i| d[i] * q[i] + E::ScalarField::one() - q[i]).collect();
    let (proof, challenge, _) = GrandProdCheck::prove(eval.clone(), transcript);
    field_deque.extend(proof);
    // prove eval(challenge) = \sum_i eq(challenge, i) * (d_i * q_i + 1 - q_i)
    let eq = new_eq(&challenge);
    let (proof, challenge, _) = SumCheck::prove(
        vec![eq, d.clone(), q.clone()],
        |v| v[0] * (v[1] * v[2] + E::ScalarField::one() - v[2]),
        transcript
    );
    field_deque.extend(proof);
    // open d and q at challenge
    let open_d = evaluate_on_point(d, &challenge);
    append_serializable_element(transcript, b"value", &open_d);
    field_deque.push_back(vec![open_d]);
    d_open.push((challenge.clone(), open_d));
    let open_q = evaluate_on_point(q, &challenge);
    append_serializable_element(transcript, b"value", &open_q);
    field_deque.push_back(vec![open_q]);
    q_open.push((challenge.clone(), open_q));
}

fn batch_open<E: Pairing> (
    eval: &Vec<E::ScalarField>,
    open: &Vec<(Vec<E::ScalarField>, E::ScalarField)>,
    pk: &ProverParam<E>,
    field_deque: &mut VecDeque<Vec<<E as Pairing>::ScalarField>>,
    affine_deque: &mut VecDeque<Vec<<E as Pairing>::G1Affine>>,
    transcript: &mut Transcript,
) {
    let num = open.len();
    let alpha = get_and_append_challenge::<E::ScalarField>(transcript, b"Internal round");
    let eq: Vec<Vec<E::ScalarField>> = (0..num).map(|i| new_eq(&open[i].0)).collect();
    let len = eq[0].len();
    let mut alpha_power = vec![E::ScalarField::one(); num];
    for i in 1..num {
        alpha_power[i] = alpha_power[i - 1] * alpha;
    }
    let mut batch_eq = vec![E::ScalarField::zero(); len];
    for i in 0..num {
        for j in 0..len {
            batch_eq[j] += alpha_power[i] * eq[i][j];
        }
    }
    let (proof, challenge, _) = SumCheck::prove(vec![batch_eq, eval.clone()], |v| v[0] * v[1], transcript);
    field_deque.extend(proof);
    let (proof, _) = PCS1::<E>::open(pk, &eval, &challenge);
    append_serializable_element(transcript, b"open", &proof);
    affine_deque.push_back(proof);
}