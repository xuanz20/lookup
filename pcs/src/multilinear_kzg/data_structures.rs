use std::collections::{LinkedList, VecDeque};
use ark_ec::{pairing::Pairing, scalar_mul::fixed_base::FixedBase, AffineRepr, CurveGroup};
use ark_ff::{PrimeField, Zero};
use ark_poly::DenseMultilinearExtension;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{rand::Rng, UniformRand};
use crate::StructuredReferenceString;
use crate::utils::{eq_eval, eq_extension, remove_dummy_variable};

// Evaluations over {0, 1}^n for G1 and G2
#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct Evaluations<C: AffineRepr> {
    pub evals: Vec<C>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct MultilinearProverParam<E: Pairing> {
    pub num_vars: usize,
    pub g: E::G1Affine,
    pub h: E::G2Affine,
    /// pp[i] = g^{eq((t1, t2, ..., t_{nv-i}), (X1, X2, ..., X_{nv-i}))}
    pub powers_of_g: Vec<Evaluations<E::G1Affine>>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct MultilinearVerifierParam<E: Pairing> {
    pub num_vars: usize,
    pub g: E::G1Affine,
    pub h: E::G2Affine,
    pub h_mask: Vec<E::G2Affine>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug)]
pub struct MultilinearUniversalParams<E: Pairing> {
    pub prover_param: MultilinearProverParam<E>,
    pub h_mask: Vec<E::G2Affine>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Debug, PartialEq, Eq)]
pub struct MultilinearKzgProof<E: Pairing> {
    pub proofs: Vec<E::G1Affine>,
}

impl<E: Pairing> MultilinearKzgProof<E> {
    pub fn from(pcs_proof: &mut VecDeque<Vec<<E as Pairing>::G1Affine>>) -> Self {
        Self {
            proofs: pcs_proof.pop_front().unwrap()
        }
    }
}

impl<E: Pairing> StructuredReferenceString<E> for MultilinearUniversalParams<E> {
    type ProverParam = MultilinearProverParam<E>;
    type VerifierParam = MultilinearVerifierParam<E>;

     fn gen_srs<R: Rng>(rng: &mut R, num_vars: usize) -> Self {
        if num_vars == 0 {
            panic!("constant polynomial not supported");
        }
        
        // Generator for G1
        // let g = E::G1::rand(rng);
        let g = E::G1::rand(rng);
        // Generator for G2
        let h = E::G2::rand(rng);

        let mut powers_of_g = Vec::new();
        // t1, t2, ..., t_nv: toxic waste of the SRS
        let t: Vec<_> = (0..num_vars).map(|_| E::ScalarField::rand(rng)).collect();

        let mut eq: LinkedList<DenseMultilinearExtension<E::ScalarField>> =
            LinkedList::from_iter(eq_extension(&t));
        let mut eq_arr = LinkedList::new();
        let mut base = eq.pop_back().unwrap().evaluations;

        // eq_arr: eq((t1, ..., t_nv), (X1, ..., X_nv)) -> ... -> eq(t_nv, X_nv)
        // eq_arr[i] is a 2^{nv - i}-len vector
        for i in (0..num_vars).rev() {
            eq_arr.push_front(remove_dummy_variable(&base, i));
            if i != 0 {
                let mul = eq.pop_back().unwrap().evaluations;
                base = base.into_iter().zip(mul.into_iter()).map(|(a, b)| a * b).collect();
            }
        }

        let mut pp_powers = Vec::new();
        let mut total_scalars = 0;
        for i in 0..num_vars {
            let eq = eq_arr.pop_front().unwrap();
            // let pp_k_powers = (0..(1 << (num_vars - i))).map(|x| eq[x]);
            // pp_powers.extend(pp_k_powers);
            pp_powers.extend(eq);
            total_scalars += 1 << (num_vars - i);
        }

        let scalar_size = E::ScalarField::MODULUS_BIT_SIZE as usize;
        // pp_g is g power of long vector (concat of eq_arr)
        let pp_g = {
            let window = FixedBase::get_mul_window_size(total_scalars);
            let g_table = FixedBase::get_window_table(scalar_size, window, g);
            E::G1::normalize_batch(&FixedBase::msm(scalar_size, window, &g_table, &pp_powers))
        };

        let mut start = 0;
        for i in 0..num_vars {
            let size = 1 << (num_vars - i);
            let pp_k_g = Evaluations {
                evals: pp_g[start..(start + size)].to_vec(),
            };
            // check correctness of pp_k_g by checking pp_k_g[0]
            let t_eval_0 = eq_eval(&vec![E::ScalarField::zero(); num_vars - i], &t[i..num_vars]);
            assert_eq!((g * t_eval_0).into(), pp_k_g.evals[0]);
            powers_of_g.push(pp_k_g);
            start += size;
        }
        powers_of_g.push(Evaluations { evals: [g.into_affine()].to_vec() });

        let pp = Self::ProverParam {
            num_vars,
            g: g.into_affine(),
            h: h.into_affine(),
            powers_of_g,
        };

        let h_mask = {
            let window = FixedBase::get_mul_window_size(num_vars);
            let h_table = FixedBase::get_window_table(scalar_size, window, h);
            E::G2::normalize_batch(&FixedBase::msm(scalar_size, window, &h_table, &t))
        };

        Self {
            prover_param: pp,
            h_mask,
        }
    }

    fn extract_prover_param(&self, supported_num_vars: usize) -> Self::ProverParam {
        let to_reduce = self.prover_param.num_vars - supported_num_vars;

        Self::ProverParam {
            num_vars: supported_num_vars,
            g: self.prover_param.g,
            h: self.prover_param.h,
            powers_of_g: self.prover_param.powers_of_g[to_reduce..].to_vec(),
        }
    }

    fn extract_verifier_param(&self, supported_num_vars: usize) -> Self::VerifierParam {
        let to_reduce = self.prover_param.num_vars - supported_num_vars;

        Self::VerifierParam {
            num_vars: supported_num_vars,
            g: self.prover_param.g,
            h: self.prover_param.h,
            h_mask: self.h_mask[to_reduce..].to_vec(),
        }
    }

    fn trim(&self) -> (Self::ProverParam, Self::VerifierParam) {
        let pp = self.extract_prover_param(self.prover_param.num_vars);
        let vp = self.extract_verifier_param(self.prover_param.num_vars);
        (pp, vp)
    }
}