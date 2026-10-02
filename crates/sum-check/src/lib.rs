//! Interactive sum-check from Section 4.1 of *Proofs, Arguments, and Zero-Knowledge*.
//!
//! For a `v`-variate polynomial `g`, the prover claims that `c_1` equals
//! `h = sum_{b in {0,1}^v} g(b)`. In round `j`, it sends the coefficients of
//! `g_j(X_j) = sum_b g(r_1, ..., r_{j-1}, X_j, b)`. The verifier checks the
//! individual degree bound and `g_j(0) + g_j(1)`, then samples `r_j`.
//! After `v` rounds it checks `g_v(r_v) = g(r_1, ..., r_v)` with one oracle query.
//!
//! Book subscripts are one-based; arkworks variable indices and Rust slices are
//! zero-based. This is the interactive protocol, without Fiat–Shamir or masking.
//! Degree bounds and the final evaluation oracle must come from the verifier's
//! statement, independently of the prover. Challenges must remain unpredictable
//! until the corresponding round polynomial has been received.
//!
//! Reading order: [`Prover::sum`], [`Prover::round_polynomial`],
//! [`Verifier::verify_round`], then [`Verifier::finish`].

use ark_ff::Field;
use ark_poly::{
    DenseUVPolynomial, Polynomial,
    multivariate::{SparsePolynomial, SparseTerm},
    univariate::DensePolynomial,
};
use ark_std::rand::{CryptoRng, RngCore};
use std::fmt;

/// An invalid input, protocol transition, or failed sum-check verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The polynomial has no variables or contains an out-of-range variable.
    InvalidPolynomial,
    /// No next round exists, or the verifier has already rejected.
    InvalidRound,
    /// A round polynomial exceeds the verifier's individual degree bound.
    DegreeTooHigh,
    /// `g_j(0) + g_j(1)` differs from the current claim.
    InconsistentSum,
    /// Final verification was requested before all `v` rounds completed.
    Incomplete,
    /// The final claim differs from the oracle's evaluation of `g`.
    FinalEvaluationMismatch,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidPolynomial => {
                "expected a polynomial with valid indices and at least one variable"
            }
            Self::InvalidRound => "no round is available or the verifier has rejected",
            Self::DegreeTooHigh => "round polynomial exceeds its individual degree bound",
            Self::InconsistentSum => "round polynomial is inconsistent with the current claim",
            Self::Incomplete => "not all sum-check rounds have completed",
            Self::FinalEvaluationMismatch => "final claim differs from the evaluation of g",
        })
    }
}

impl std::error::Error for Error {}

/// An honest prover for a sparse polynomial `g` over an arkworks field.
///
/// Supports arbitrary individual degrees, including constants and unused
/// variables. Boolean sums are computed term by term: an absent variable
/// contributes a factor of two, while `0^k + 1^k = 1` for positive `k`.
pub struct Prover<'a, F: Field> {
    g: &'a SparsePolynomial<F, SparseTerm>,
    degree_bounds: Vec<usize>,
}

impl<'a, F: Field> Prover<'a, F> {
    /// Creates a prover, rejecting zero variables and invalid variable indices.
    pub fn new(g: &'a SparsePolynomial<F, SparseTerm>) -> Result<Self, Error> {
        if g.num_vars == 0 {
            return Err(Error::InvalidPolynomial);
        }
        let mut degree_bounds = vec![0; g.num_vars];
        for (coefficient, term) in &g.terms {
            for &(variable, power) in term.iter() {
                if variable >= g.num_vars {
                    return Err(Error::InvalidPolynomial);
                }
                if !coefficient.is_zero() {
                    degree_bounds[variable] = degree_bounds[variable].max(power);
                }
            }
        }
        Ok(Self { g, degree_bounds })
    }

    /// Returns `deg_j(g)` for each variable, in the book's variable order.
    pub fn degree_bounds(&self) -> &[usize] {
        &self.degree_bounds
    }

    /// Computes the true sum `H` over all Boolean inputs (Equation 4.1).
    pub fn sum(&self) -> F {
        // g_1 already sums over X_2, ..., X_v. Sum over X_1 as well.
        let g_1 = self.compute_round_polynomial(&[]);
        g_1.evaluate(&F::ZERO) + g_1.evaluate(&F::ONE)
    }

    /// Computes `g_j` after challenges `r = [r_1, ..., r_{j-1}]` (Equation 4.5).
    ///
    /// Returns [`Error::InvalidRound`] if `r` already fixes all `v` variables.
    pub fn round_polynomial(&self, r: &[F]) -> Result<DensePolynomial<F>, Error> {
        if r.len() >= self.g.num_vars {
            return Err(Error::InvalidRound);
        }
        Ok(self.compute_round_polynomial(r))
    }

    fn compute_round_polynomial(&self, r: &[F]) -> DensePolynomial<F> {
        // j is the zero-based index of the variable left free this round.
        let j = r.len();
        let mut coefficients = vec![F::ZERO; self.degree_bounds[j] + 1];

        // Summation distributes over addition, so handle one monomial at a time.
        for (coefficient, term) in &self.g.terms {
            if coefficient.is_zero() {
                continue;
            }
            let mut round_coefficient = *coefficient;
            let mut power_j = 0;
            let mut absent_suffix_variables = self.g.num_vars - j - 1;

            for &(variable, power) in term.iter() {
                if variable < j {
                    // 1. Substitute the challenges for earlier variables.
                    round_coefficient *= r[variable].pow([power as u64]);
                } else if variable == j {
                    // 2. Leave X_j free: this term contributes to X_j^power_j.
                    power_j = power;
                } else if power > 0 {
                    // 3. Sum later variables over {0, 1}.
                    // A positive power contributes 0^power + 1^power = 1.
                    absent_suffix_variables -= 1;
                }
            }

            // A variable absent from the monomial contributes 1 + 1 = 2.
            let two = F::ONE + F::ONE;
            round_coefficient *= two.pow([absent_suffix_variables as u64]);
            coefficients[power_j] += round_coefficient;
        }
        DensePolynomial::from_coefficients_vec(coefficients)
    }
}

/// A verifier holding the current claim and the challenges sampled so far.
///
/// A successful round is provisional; only [`Self::finish`] accepts the claim.
/// Any rejected round permanently prevents this verifier from accepting.
pub struct Verifier<F: Field> {
    degree_bounds: Vec<usize>,
    claim: F,
    r: Vec<F>,
    rejected: bool,
}

/// The evaluation claim remaining after all sum-check rounds.
///
/// This is **not acceptance**: an enclosing protocol must establish
/// `g(point) = value`. GKR does so by reducing it to the next circuit layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Subclaim<F: Field> {
    /// The verifier's sampled point `(r_1, ..., r_v)`.
    pub point: Vec<F>,
    /// The claimed value `g_v(r_v)` that must equal `g(point)`.
    pub value: F,
}

impl<F: Field> Verifier<F> {
    /// Starts with claimed sum `C_1` and trusted bounds on `deg_j(g)`.
    ///
    /// The number of bounds defines `v` and must be positive. Bounds must be
    /// established independently of prover messages. Soundness error is at most
    /// `sum_j degree_bounds[j] / |F|` with uniform, independent challenges.
    pub fn new(c_1: F, degree_bounds: Vec<usize>) -> Result<Self, Error> {
        if degree_bounds.is_empty() {
            return Err(Error::InvalidPolynomial);
        }
        Ok(Self {
            degree_bounds,
            claim: c_1,
            r: Vec::new(),
            rejected: false,
        })
    }

    /// Checks `g_j` and then samples and returns the next challenge `r_j`.
    ///
    /// The caller supplies the verifier's privately seeded cryptographic RNG.
    /// A malformed or inconsistent message is rejected before any randomness
    /// is consumed. Calling this after the last round also rejects the session.
    pub fn verify_round<R: RngCore + CryptoRng>(
        &mut self,
        g_j: &DensePolynomial<F>,
        rng: &mut R,
    ) -> Result<F, Error> {
        if self.rejected || self.r.len() == self.degree_bounds.len() {
            self.rejected = true;
            return Err(Error::InvalidRound);
        }
        // 1. Check deg(g_j) <= deg_j(g).
        // DensePolynomial has public coefficients; do not assume that an
        // untrusted message has normalized trailing zeros (degree() does).
        let degree = g_j.coeffs.iter().rposition(|c| !c.is_zero()).unwrap_or(0);
        if degree > self.degree_bounds[self.r.len()] {
            self.rejected = true;
            return Err(Error::DegreeTooHigh);
        }

        // 2. Check C_1 in round 1, or g_{j-1}(r_{j-1}) in later rounds.
        let sum = g_j.evaluate(&F::ZERO) + g_j.evaluate(&F::ONE);
        if sum != self.claim {
            self.rejected = true;
            return Err(Error::InconsistentSum);
        }

        // 3. Choose r_j only after the prover's message passes both checks.
        let r_j = F::rand(rng);

        // The next round must justify this evaluation of g_j.
        self.claim = g_j.evaluate(&r_j);
        self.r.push(r_j);
        Ok(r_j)
    }

    /// Consumes the verifier and checks `g_v(r_v) = g(r_1, ..., r_v)`.
    ///
    /// Calls the trusted evaluation oracle exactly once after all rounds pass,
    /// and never for an incomplete or rejected session. Returns the challenge
    /// vector on acceptance. The oracle must evaluate the original statement's
    /// `g`; a prover-supplied final value is insufficient.
    pub fn finish(self, evaluate_g: impl FnOnce(&[F]) -> F) -> Result<Vec<F>, Error> {
        let subclaim = self.reduce()?;

        // All variables are now fixed, so no Boolean sum remains.
        // Compare g_v(r_v) with one direct evaluation of the original g.
        let g_at_r = evaluate_g(&subclaim.point);
        if subclaim.value != g_at_r {
            return Err(Error::FinalEvaluationMismatch);
        }
        Ok(subclaim.point)
    }

    /// Stops before the final oracle check and returns the remaining claim.
    ///
    /// Used when sum-check is a subroutine, as in GKR (Section 4.6). This only
    /// reduces the original claim; it does not establish its truth. Standalone
    /// callers should use [`Self::finish`] with a trusted evaluation oracle.
    pub fn reduce(self) -> Result<Subclaim<F>, Error> {
        if self.rejected {
            return Err(Error::InvalidRound);
        }
        if self.r.len() != self.degree_bounds.len() {
            return Err(Error::Incomplete);
        }

        Ok(Subclaim {
            point: self.r,
            value: self.claim,
        })
    }
}
