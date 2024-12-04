use core::time;
use std::{fs::{self, File}, io, path::Path, time::Instant};

use ark_ec::pairing::Pairing;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Write};
use ark_std::{rand::seq::SliceRandom, test_rng};
use lookup::Lookup;
use merlin::Transcript;
use pcs::{
    hyrax_kzg::{hyrax_kzg_1::HyraxKzgPCS1, hyrax_kzg_2::HyraxKzgPCS2},
    multilinear_kzg::data_structures::{MultilinearUniversalParams, MultilinearProverParam, MultilinearVerifierParam},
    PolynomialCommitmentScheme
};

type E = ark_bn254::Bn254;
type F = <E as Pairing>::ScalarField;
type PCS1<E> = HyraxKzgPCS1<E>;
type PCS2<E> = HyraxKzgPCS2<E>;
type ProverParam<E> = MultilinearProverParam<E>;
type VerifierParam<E> = MultilinearVerifierParam<E>;

const SUPPORTED_SIZE: usize = 20;
const M: [usize; 3] = [20, 24, 28];
const N: [usize; 2] = [8, 16];

fn main() {
    let mut rng = test_rng();
    let srs = {
        match read_srs() {
            Ok(p) => p,
            Err(_e) => {
                let srs =
                    PCS1::<E>::gen_srs(&mut rng, SUPPORTED_SIZE);
                write_srs(&srs);
                srs
            },
        }
    };
    let (pk, vk) = PCS1::<E>::trim(&srs);
    // for m in M {
    //     for n in N {
    //         bench_lookup_helper(m, n, &pk, &vk);
    //     }
    // }
    bench_lookup_helper(20, 8, &pk, &vk);
}

fn read_srs() -> Result<MultilinearUniversalParams<E>, io::Error> {
    let mut f = File::open("srs.params")?;
    Ok(MultilinearUniversalParams::<E>::deserialize_uncompressed_unchecked(&mut f).unwrap())
}

fn write_srs(pcs_srs: &MultilinearUniversalParams<E>) {
    let mut f = File::create("srs.params").unwrap();
    pcs_srs.serialize_uncompressed(&mut f).unwrap();
}

fn bench_lookup_helper(
    m: usize,
    n: usize,
    pk: &ProverParam<E>,
    vk: &VerifierParam<E>,
) {
    let path = "bench_results";
    if !Path::new(path).exists() {
        fs::create_dir(path).unwrap();
    }
    let filename = format!("{}/{}_{}.txt", path, m, n);
    let mut file = File::create(filename).unwrap();
    file.write_all(format!("M=2^{}, N=2^{}\n", m, n).as_ref()).unwrap();
    let mut rng = test_rng();
    let t: Vec<_> = (1..=(1 << n)).into_iter().map(|x| F::from(x as u32)).collect();
    let a: Vec<_> = (1..=(1 << m)).into_iter().map(|_| t.choose(&mut rng).unwrap().clone()).collect();
    let commit = PCS2::<E>::commit(pk, &a);
    //==========================================================
    // generate a proof
    let mut transcript = Transcript::new(b"Lookup");
    let start = Instant::now();
    let proof = Lookup::prove::<E>(&a, &t, pk, &mut transcript);
    let time = start.elapsed().as_secs_f32();
    println!("prove for M=2^{}, N=2^{}: {}s", m, n, time);
    file.write_all(format!("{}\n", time).as_ref()).unwrap();
    //==========================================================
    // get proof size
    let size = proof.get_proof_size();
    println!("proof size for M=2^{}, N=2^{}: {}KB", m, n, proof.get_proof_size());
    //==========================================================
    // verify a proof
    let mut transcript = Transcript::new(b"Lookup");
    let start = Instant::now();
    Lookup::verify(&a, &t, &commit, vk, &proof, &mut transcript);
    let time = start.elapsed().as_secs_f32();
    println!("verify for M=2^{}, N=2^{}: {}s", m, n, time);
    file.write_all(format!("{}\n", time).as_ref()).unwrap();
    file.write_all(format!("{}\n", size).as_ref()).unwrap();
}