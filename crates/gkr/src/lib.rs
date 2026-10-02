//! Interactive GKR from Section 4.6 of *Proofs, Arguments, and Zero-Knowledge*.
//!
//! Layers run from output layer `0` to input layer `d`. At layer `i`, the
//! verifier holds a claim `m_i = W_i_tilde(r_i)`. Sum-check reduces it to two
//! evaluations of `W_{i+1}_tilde`, and a line polynomial `q` reduces those to
//! one. Finally the verifier evaluates the public input's MLE directly.
//!
//! Read [`Layer`], [`Circuit`], [`Prover`], [`LayerProver`], then [`Verifier`]. The prover
//! uses the sparse wiring idea of Section 4.6.5, Method 2. The verifier scans
//! the public gates to evaluate wiring predicates; it does not evaluate the
//! circuit's internal gate values. Specialized wiring and the data-parallel
//! variant of Section 4.6.7 are not implemented. This is an interactive protocol.

mod circuit;
mod layer;
mod prover;
mod verifier;

pub use circuit::Circuit;
pub use layer::{Gate, Layer};
pub use prover::{LayerProver, Prover};
pub use verifier::Verifier;

use ark_ff::Field;
use multilinear_ext::chi;
use std::fmt;

/// An invalid circuit, message, or failed GKR verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// Layer widths must be nonzero powers of two and wires must be in range.
    InvalidCircuit,
    /// An input, output, or evaluation point has the wrong length.
    DimensionMismatch,
    /// A message arrived in the wrong phase, or this verifier already rejected.
    UnexpectedMessage,
    /// A sum-check round or its completion failed.
    SumCheck(sum_check::Error),
    /// The line polynomial has degree greater than `k_{i+1}`.
    LineDegreeTooHigh,
    /// The wiring expression using `q(0)` and `q(1)` fails sum-check's final check.
    LayerMismatch,
    /// The final claim disagrees with the MLE of the public input.
    InputMismatch,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCircuit => f.write_str("invalid layer width or gate input index"),
            Self::DimensionMismatch => f.write_str("input, output, or point dimension mismatch"),
            Self::UnexpectedMessage => {
                f.write_str("unexpected protocol message or rejected session")
            }
            Self::SumCheck(error) => write!(f, "sum-check failed: {error}"),
            Self::LineDegreeTooHigh => f.write_str("line polynomial exceeds its degree bound"),
            Self::LayerMismatch => f.write_str("line endpoints do not satisfy the layer claim"),
            Self::InputMismatch => f.write_str("final claim differs from the public input's MLE"),
        }
    }
}

impl std::error::Error for Error {}

impl From<sum_check::Error> for Error {
    fn from(error: sum_check::Error) -> Self {
        Self::SumCheck(error)
    }
}

// Evaluate chi_a(r), decoding gate label a in our shared little-endian order.
fn chi_at<F: Field>(a: usize, r: &[F]) -> F {
    let bits: Vec<bool> = (0..r.len()).map(|j| (a >> j) & 1 == 1).collect();
    chi(&bits, r).expect("bits and r have the same length")
}
