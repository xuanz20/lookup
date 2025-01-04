# Celer: a Computationally Efficient Lookup Argument for Large Scale Queries

## Usage
```Rust
let mut rng = test_rng();
// generate random lookup table
let t: Vec<_> = (1..=N).into_iter().map(|x| F::from(x as u32)).collect();
// generate random query vector
let a: Vec<_> = (1..=M).into_iter().map(|_| t.choose(&mut rng).unwrap().clone()).collect();
let mut transcript = Transcript::new(b"Lookup");
// preprocessing
let srs = PCS::<E>::gen_srs(&mut rng, SUPPORTED_SIZE);
let (pk, vk) = PCS::<E>::trim(&srs);
let commit = PCS::<E>::commit(&pk, &a);
// generate proof
let proof = Lookup::prove::<E>(&a, &t, &pk, &mut transcript);
let mut transcript = Transcript::new(b"Lookup");
// verify proof
Lookup::verify(&a, &t, &commit, &vk, &proof, &mut transcript);
```

## Test
Run `cargo bench`.

All experiment data are collected in `lookup/bench_results` as `{m}_{n}.txt`:
the query vector length is $2^m$, and the lookup table size is $2^n$.

## Acknowledgements
This repository references https://github.com/EspressoSystems/hyperplonk.git.