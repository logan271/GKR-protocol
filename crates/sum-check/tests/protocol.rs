//! Completeness, round identities, and adversarial verifier checks.

use ark_bn254::Fr;
use ark_ff::{AdditiveGroup, Field, UniformRand};
use ark_poly::{
    DenseMVPolynomial, DenseUVPolynomial, Polynomial,
    multivariate::{SparsePolynomial, SparseTerm, Term},
    univariate::DensePolynomial,
};
use ark_std::rand::{Rng, RngCore, SeedableRng, rngs::StdRng};
use sum_check::{Error, Prover, Verifier};

type G = SparsePolynomial<Fr, SparseTerm>;

fn polynomial(v: usize, terms: &[(u64, &[(usize, usize)])]) -> G {
    G::from_coefficients_vec(
        v,
        terms
            .iter()
            .map(|(c, term)| (Fr::from(*c), SparseTerm::new(term.to_vec())))
            .collect(),
    )
}

fn univariate(coefficients: &[u64]) -> DensePolynomial<Fr> {
    DensePolynomial::from_coefficients_vec(coefficients.iter().copied().map(Fr::from).collect())
}

fn book_polynomial() -> G {
    polynomial(
        3,
        &[
            (2, &[(0, 3)]),
            (1, &[(0, 1), (2, 1)]),
            (1, &[(1, 1), (2, 1)]),
        ],
    )
}

fn boolean_sum(g: &G, prefix: &[Fr]) -> Fr {
    let remaining = g.num_vars - prefix.len();
    (0..1usize << remaining)
        .map(|bits| {
            let mut point = prefix.to_vec();
            point.extend((0..remaining).map(|i| Fr::from(((bits >> i) & 1) as u64)));
            g.evaluate(&point)
        })
        .sum()
}

fn run(g: &G) {
    let prover = Prover::new(g).unwrap();
    let h = boolean_sum(g, &[]);
    assert_eq!(prover.sum(), h);
    let mut verifier = Verifier::new(h, prover.degree_bounds().to_vec()).unwrap();
    let mut rng = StdRng::seed_from_u64(42);
    let mut r = Vec::new();
    for _ in 0..g.num_vars {
        let g_j = prover.round_polynomial(&r).unwrap();
        r.push(verifier.verify_round(&g_j, &mut rng).unwrap());
    }
    let mut oracle_calls = 0;
    let accepted_r = verifier
        .finish(|point| {
            oracle_calls += 1;
            g.evaluate(&point.to_vec())
        })
        .unwrap();
    assert_eq!(accepted_r, r);
    assert_eq!(oracle_calls, 1);
}

#[test]
fn reproduces_section_4_1_example() {
    // g = 2 X_1^3 + X_1 X_3 + X_2 X_3, H = 12.
    let g = book_polynomial();
    let prover = Prover::new(&g).unwrap();
    assert_eq!(prover.degree_bounds(), &[3, 1, 1]);
    assert_eq!(prover.sum(), Fr::from(12));
    let g_1 = prover.round_polynomial(&[]).unwrap();
    assert_eq!(g_1, univariate(&[1, 2, 0, 8]));
    let g_2 = prover.round_polynomial(&[Fr::from(2)]).unwrap();
    assert_eq!(g_2, univariate(&[34, 1]));
    assert_eq!(
        g_1.evaluate(&Fr::from(2)),
        g_2.evaluate(&Fr::ZERO) + g_2.evaluate(&Fr::ONE)
    );
    let g_3 = prover
        .round_polynomial(&[Fr::from(2), Fr::from(3)])
        .unwrap();
    assert_eq!(g_3, univariate(&[16, 5]));
    assert_eq!(
        g_2.evaluate(&Fr::from(3)),
        g_3.evaluate(&Fr::ZERO) + g_3.evaluate(&Fr::ONE)
    );
    assert_eq!(
        g_3.evaluate(&Fr::from(6)),
        g.evaluate(&vec![Fr::from(2), Fr::from(3), Fr::from(6)])
    );
    run(&g);
}

#[test]
fn accepts_univariate_constant_zero_and_unused_variables() {
    for g in [
        polynomial(1, &[(7, &[]), (3, &[(0, 4)])]),
        polynomial(4, &[(7, &[])]),
        polynomial(3, &[]),
        polynomial(4, &[(2, &[(1, 2)]), (3, &[(3, 1)])]),
    ] {
        run(&g);
    }
}

#[test]
fn random_polynomials_match_direct_boolean_sums_in_every_round() {
    let mut rng = StdRng::seed_from_u64(123);
    for v in 1..=4 {
        for _ in 0..8 {
            let terms = (0..10)
                .map(|_| {
                    let term = SparseTerm::new((0..v).map(|i| (i, rng.gen_range(0..=3))).collect());
                    (Fr::rand(&mut rng), term)
                })
                .collect();
            let g = G::from_coefficients_vec(v, terms);
            let prover = Prover::new(&g).unwrap();
            let mut r = Vec::new();
            for j in 0..v {
                let g_j = prover.round_polynomial(&r).unwrap();
                assert!(g_j.degree() <= prover.degree_bounds()[j]);
                for t in [Fr::ZERO, Fr::ONE, Fr::rand(&mut rng)] {
                    let mut prefix = r.clone();
                    prefix.push(t);
                    assert_eq!(g_j.evaluate(&t), boolean_sum(&g, &prefix));
                }
                r.push(Fr::rand(&mut rng));
            }
            run(&g);
        }
    }
}

#[test]
fn rejects_wrong_initial_claim_without_sampling_and_cannot_resume() {
    let g = book_polynomial();
    let prover = Prover::new(&g).unwrap();
    let mut verifier = Verifier::new(Fr::from(13), vec![3, 1, 1]).unwrap();
    let mut rng = StdRng::seed_from_u64(1);
    let mut untouched_rng = rng.clone();
    assert_eq!(
        verifier.verify_round(&prover.round_polynomial(&[]).unwrap(), &mut rng),
        Err(Error::InconsistentSum)
    );
    assert_eq!(rng.next_u64(), untouched_rng.next_u64());
    assert_eq!(
        verifier.verify_round(&univariate(&[6, 1]), &mut rng),
        Err(Error::InvalidRound)
    );
    assert_eq!(
        verifier.finish(|_| panic!("must not query oracle")),
        Err(Error::InvalidRound)
    );
}

#[test]
fn rejects_inconsistent_later_round() {
    let g = book_polynomial();
    let prover = Prover::new(&g).unwrap();
    let mut verifier = Verifier::new(Fr::from(12), vec![3, 1, 1]).unwrap();
    let mut rng = StdRng::seed_from_u64(2);
    let r_1 = verifier
        .verify_round(&prover.round_polynomial(&[]).unwrap(), &mut rng)
        .unwrap();
    let mut g_2 = prover.round_polynomial(&[r_1]).unwrap();
    g_2.coeffs[0] += Fr::ONE;
    assert_eq!(
        verifier.verify_round(&g_2, &mut rng),
        Err(Error::InconsistentSum)
    );
}

#[test]
fn rejects_excess_degree_even_when_boolean_sum_matches() {
    // X^2 - X sums to zero, but exceeds the trusted degree bound of one.
    let g_1 = DensePolynomial::from_coefficients_vec(vec![Fr::ZERO, -Fr::ONE, Fr::ONE]);
    let mut verifier = Verifier::new(Fr::ZERO, vec![1]).unwrap();
    let mut rng = StdRng::seed_from_u64(3);
    let mut untouched_rng = rng.clone();
    assert_eq!(
        verifier.verify_round(&g_1, &mut rng),
        Err(Error::DegreeTooHigh)
    );
    assert_eq!(rng.next_u64(), untouched_rng.next_u64());
}

#[test]
fn enforces_each_variables_bound() {
    let mut verifier = Verifier::new(Fr::from(2), vec![3, 0]).unwrap();
    let mut rng = StdRng::seed_from_u64(4);
    verifier.verify_round(&univariate(&[1]), &mut rng).unwrap();
    // X has the required Boolean sum of one, but this variable is constant.
    assert_eq!(
        verifier.verify_round(&univariate(&[0, 1]), &mut rng),
        Err(Error::DegreeTooHigh)
    );
}

#[test]
fn final_oracle_rejects_a_consistent_but_false_claim() {
    // The prover sends g_1 = 1 - X instead of the statement's g = X.
    let mut verifier = Verifier::new(Fr::ONE, vec![1]).unwrap();
    let mut rng = StdRng::seed_from_u64(5);
    let forged = DensePolynomial::from_coefficients_vec(vec![Fr::ONE, -Fr::ONE]);
    let r_1 = verifier.verify_round(&forged, &mut rng).unwrap();
    assert_ne!(r_1 + r_1, Fr::ONE);
    assert_eq!(
        verifier.finish(|r| r[0]),
        Err(Error::FinalEvaluationMismatch)
    );
}

#[test]
fn rejects_incomplete_and_extra_rounds() {
    let verifier = Verifier::new(Fr::ZERO, vec![0, 0]).unwrap();
    assert_eq!(
        verifier.finish(|_| panic!("must not query oracle")),
        Err(Error::Incomplete)
    );
    let mut verifier = Verifier::new(Fr::ZERO, vec![0]).unwrap();
    let mut rng = StdRng::seed_from_u64(6);
    verifier.verify_round(&univariate(&[]), &mut rng).unwrap();
    assert_eq!(
        verifier.verify_round(&univariate(&[]), &mut rng),
        Err(Error::InvalidRound)
    );
    assert_eq!(
        verifier.finish(|_| panic!("must not query oracle")),
        Err(Error::InvalidRound)
    );
}

#[test]
fn handles_non_normalized_round_coefficients() {
    let mut rng = StdRng::seed_from_u64(7);
    let mut verifier = Verifier::new(Fr::from(2), vec![0]).unwrap();
    let g_1 = DensePolynomial {
        coeffs: vec![Fr::ONE, Fr::ZERO, Fr::ZERO],
    };
    verifier.verify_round(&g_1, &mut rng).unwrap();
    verifier.finish(|_| Fr::ONE).unwrap();
    let mut verifier = Verifier::new(Fr::ZERO, vec![0]).unwrap();
    verifier
        .verify_round(
            &DensePolynomial {
                coeffs: vec![Fr::ZERO; 3],
            },
            &mut rng,
        )
        .unwrap();
    verifier.finish(|_| Fr::ZERO).unwrap();
}

#[test]
fn rejects_invalid_inputs_and_prover_rounds() {
    assert!(matches!(
        Prover::new(&polynomial(0, &[])),
        Err(Error::InvalidPolynomial)
    ));
    assert!(matches!(
        Verifier::<Fr>::new(Fr::ZERO, vec![]),
        Err(Error::InvalidPolynomial)
    ));
    let invalid = G {
        num_vars: 1,
        terms: vec![(Fr::ONE, SparseTerm::new(vec![(1, 1)]))],
    };
    assert!(matches!(
        Prover::new(&invalid),
        Err(Error::InvalidPolynomial)
    ));
    let g = polynomial(1, &[(1, &[(0, 1)])]);
    let prover = Prover::new(&g).unwrap();
    assert_eq!(
        prover.round_polynomial(&[Fr::ONE]),
        Err(Error::InvalidRound)
    );
    assert_eq!(
        prover.round_polynomial(&[Fr::ONE; 2]),
        Err(Error::InvalidRound)
    );
}

#[test]
fn reduction_returns_only_the_remaining_evaluation_claim() {
    let g = book_polynomial();
    let prover = Prover::new(&g).unwrap();
    let mut verifier = Verifier::new(prover.sum(), prover.degree_bounds().to_vec()).unwrap();
    let mut rng = StdRng::seed_from_u64(46);
    let mut r = Vec::new();
    for _ in 0..g.num_vars {
        let g_j = prover.round_polynomial(&r).unwrap();
        r.push(verifier.verify_round(&g_j, &mut rng).unwrap());
    }
    let subclaim = verifier.reduce().unwrap();
    assert_eq!(subclaim.point, r);
    // The outer protocol is responsible for this equality, not reduce().
    assert_eq!(subclaim.value, g.evaluate(&r));

    let incomplete = Verifier::new(Fr::ZERO, vec![1]).unwrap();
    assert_eq!(incomplete.reduce(), Err(Error::Incomplete));
    let mut rejected = Verifier::new(Fr::ZERO, vec![1]).unwrap();
    assert_eq!(
        rejected.verify_round(&univariate(&[1]), &mut rng),
        Err(Error::InconsistentSum)
    );
    assert_eq!(rejected.reduce(), Err(Error::InvalidRound));
}
