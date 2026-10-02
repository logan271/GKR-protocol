//! Multilinear extensions from Section 3.5 of *Proofs, Arguments, and Zero-Knowledge*.
//!
//! Every function `f: {0,1}^v -> F` has a unique multilinear extension `f_tilde`:
//!
//! ```text
//! f_tilde(r) = sum_{w in {0,1}^v} f(w) * chi_w(r)                (3.1)
//! chi_w(r)   = product_i (r_i * w_i + (1 - r_i) * (1 - w_i))     (3.2)
//! ```
//!
//! Multilinear means degree at most one in each variable, not total degree one.
//! The Boolean evaluations determine the polynomial, so we store `f(w)` rather
//! than expand its coefficients.
//!
//! Read [`chi`], then [`MultilinearExtension::evaluate_direct`] for the formula,
//! and [`MultilinearExtension::evaluate`] for the table-building algorithm of
//! Lemma 3.8. Both methods evaluate the same polynomial.

use ark_ff::Field;
use std::fmt;

/// Invalid table size or mismatched point dimensions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// A Boolean evaluation table must have a nonzero power-of-two length.
    InvalidTableLength,
    /// The point must contain one coordinate per variable.
    DimensionMismatch,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidTableLength => "evaluation table length must be a nonzero power of two",
            Self::DimensionMismatch => "point dimension must equal the number of variables",
        })
    }
}

impl std::error::Error for Error {}

/// Evaluates the multilinear Lagrange basis polynomial `chi_w` at `r` (3.2).
///
/// `w` is a Boolean vector. Each factor is `r_i` when `w_i = 1`, and `1 - r_i`
/// when `w_i = 0`. Consequently, at Boolean points `chi_w(w) = 1` and
/// `chi_w(y) = 0` for every `y != w`.
///
/// Returns [`Error::DimensionMismatch`] if the lengths differ. Empty vectors
/// give the empty product, one. Takes `O(v)` field operations.
pub fn chi<F: Field>(w: &[bool], r: &[F]) -> Result<F, Error> {
    if w.len() != r.len() {
        return Err(Error::DimensionMismatch);
    }

    let mut chi_w = F::ONE;
    for (&w_i, &r_i) in w.iter().zip(r) {
        let factor = if w_i { r_i } else { F::ONE - r_i };
        chi_w *= factor;
    }
    Ok(chi_w)
}

/// The unique multilinear extension `f_tilde` of a Boolean evaluation table `f`.
///
/// The table uses arkworks' little-endian indexing: bit `i` of an index is the
/// value of the book's variable `X_{i+1}`. For two variables the entries are
/// `[f(0,0), f(1,0), f(0,1), f(1,1)]`. This is an evaluation table, not a list
/// of polynomial coefficients.
///
/// A one-entry table represents a constant polynomial in zero variables.
///
/// ```
/// use ark_bn254::Fr;
/// use multilinear_ext::MultilinearExtension;
///
/// // f(0,0) = 1, f(1,0) = 1, f(0,1) = 2, f(1,1) = 4.
/// // Thus f_tilde(X_1, X_2) = 1 + X_2 + 2 X_1 X_2.
/// let f = [1, 1, 2, 4].into_iter().map(Fr::from).collect();
/// let f_tilde = MultilinearExtension::new(f)?;
/// let r = [Fr::from(2), Fr::from(3)];
/// assert_eq!(f_tilde.evaluate(&r)?, Fr::from(16));
/// assert_eq!(f_tilde.evaluate_direct(&r)?, Fr::from(16));
/// # Ok::<(), multilinear_ext::Error>(())
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultilinearExtension<F: Field> {
    f: Vec<F>,
}

impl<F: Field> MultilinearExtension<F> {
    /// Stores all `2^v` Boolean evaluations of `f`, inferring `v` from the length.
    ///
    /// Rejects empty tables and lengths that are not powers of two. No padding
    /// is performed: any padding would define additional values of `f`.
    pub fn new(f: Vec<F>) -> Result<Self, Error> {
        if !f.len().is_power_of_two() {
            return Err(Error::InvalidTableLength);
        }
        Ok(Self { f })
    }

    /// Returns `v`, the number of variables.
    pub fn num_vars(&self) -> usize {
        self.f.len().ilog2() as usize
    }

    /// Returns the Boolean evaluation table in little-endian order.
    pub fn evaluations(&self) -> &[F] {
        &self.f
    }

    /// Evaluates Equation 3.1 directly, as in Lemma 3.7.
    ///
    /// Each basis value is computed independently. For `n = 2^v`, this takes
    /// `O(n * v)` field operations and `O(v)` extra space beyond the input table.
    /// Returns [`Error::DimensionMismatch`] unless `r` has exactly `v` entries.
    pub fn evaluate_direct(&self, r: &[F]) -> Result<F, Error> {
        if r.len() != self.num_vars() {
            return Err(Error::DimensionMismatch);
        }

        let mut f_tilde_at_r = F::ZERO;
        for (index, &f_w) in self.f.iter().enumerate() {
            // Decode the Boolean point w: its first coordinate is the low bit.
            let w: Vec<bool> = (0..r.len()).map(|i| (index >> i) & 1 == 1).collect();
            f_tilde_at_r += f_w * chi(&w, r)?;
        }
        Ok(f_tilde_at_r)
    }

    /// Evaluates Equation 3.1 using the basis table of Lemma 3.8.
    ///
    /// After processing `r_1, ..., r_j`, the table stores all `2^j` products of
    /// the first `j` basis factors. Each stage doubles the table, for a total of
    /// `O(n)` field operations and `O(n)` extra space, where `n = 2^v`.
    /// Returns [`Error::DimensionMismatch`] unless `r` has exactly `v` entries.
    pub fn evaluate(&self, r: &[F]) -> Result<F, Error> {
        if r.len() != self.num_vars() {
            return Err(Error::DimensionMismatch);
        }

        // A^(0) contains the empty product. It also handles v = 0.
        let mut basis = vec![F::ONE];
        for &r_j in r {
            let previous_len = basis.len();
            basis.resize(2 * previous_len, F::ZERO);

            for index in 0..previous_len {
                let previous_product = basis[index];
                // The new coordinate is the next bit in the table index.
                // w_j = 0: multiply by (1 - r_j).
                basis[index] = previous_product * (F::ONE - r_j);
                // w_j = 1: multiply by r_j.
                basis[index + previous_len] = previous_product * r_j;
            }
        }

        // Equation 3.1 is now the inner product of f(w) and chi_w(r).
        let mut f_tilde_at_r = F::ZERO;
        for (&f_w, &chi_w) in self.f.iter().zip(&basis) {
            f_tilde_at_r += f_w * chi_w;
        }
        Ok(f_tilde_at_r)
    }
}
