//! Runs Section 4.1's example polynomial with fresh verifier challenges.
use ark_bn254::Fr;
use ark_poly::{
    DenseMVPolynomial, Polynomial,
    multivariate::{SparsePolynomial, SparseTerm, Term},
};
use ark_std::rand::rngs::OsRng;
use sum_check::{Prover, Verifier};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Book variables X_1, X_2, X_3 have arkworks indices 0, 1, 2.
    let g = SparsePolynomial::from_coefficients_vec(
        3,
        vec![
            (Fr::from(2), SparseTerm::new(vec![(0, 3)])),
            (Fr::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
            (Fr::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
        ],
    );
    // The prover first announces the claimed Boolean sum C_1.
    let prover = Prover::new(&g)?;
    let c_1 = prover.sum();
    assert_eq!(c_1, Fr::from(12));

    // The verifier knows these bounds from the statement g.
    let mut verifier = Verifier::new(c_1, vec![3, 1, 1])?;
    let mut rng = OsRng;
    let mut r = Vec::new();
    for _ in 0..g.num_vars {
        // P -> V: the next univariate polynomial g_j.
        let g_j = prover.round_polynomial(&r)?;
        // V -> P: a fresh r_j, after checking the degree and sum.
        let r_j = verifier.verify_round(&g_j, &mut rng)?;
        r.push(r_j);
    }
    // V checks g_v(r_v) against the original polynomial at the same point.
    verifier.finish(|r| g.evaluate(&r.to_vec()))?;
    println!("Accepted: H = 12 for g = 2 X_1^3 + X_1 X_3 + X_2 X_3");
    Ok(())
}
