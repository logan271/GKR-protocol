use crate::{Error, chi_at};
use ark_ff::Field;

/// A fan-in-two gate; both indices refer to gates in the next layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Gate {
    /// Sum of the two input values. Repeated inputs are allowed.
    Add(usize, usize),
    /// Product of the two input values. Repeated inputs give a square.
    Mul(usize, usize),
}

impl Gate {
    /// Returns `(in_1(a), in_2(a))` in their specified order.
    pub fn inputs(self) -> (usize, usize) {
        match self {
            Self::Add(b, c) | Self::Mul(b, c) => (b, c),
        }
    }
}

/// A non-input layer of gates, indexed by their Boolean labels.
///
/// Owns the gates and their layer-local computations. Its width is a nonzero
/// power of two, so each label has `num_vars()` bits. The enclosing circuit
/// validates that every wire points to a gate in the next layer.
#[derive(Debug, Clone)]
pub struct Layer {
    gates: Vec<Gate>,
}

impl Layer {
    /// Creates a layer, rejecting empty or non-power-of-two widths.
    pub fn new(gates: Vec<Gate>) -> Result<Self, Error> {
        if !gates.len().is_power_of_two() {
            return Err(Error::InvalidCircuit);
        }
        Ok(Self { gates })
    }

    /// Returns the gates in little-endian label order.
    pub fn gates(&self) -> &[Gate] {
        &self.gates
    }

    /// Returns `S_i`, the number of gates in this layer.
    pub fn width(&self) -> usize {
        self.gates.len()
    }

    /// Returns `k_i = log2(S_i)`, the number of bits in each gate label.
    pub fn num_vars(&self) -> usize {
        self.width().ilog2() as usize
    }

    // Circuit has already checked the wire indices and next-layer input length.
    pub(crate) fn evaluate<F: Field>(&self, next: &[F]) -> Vec<F> {
        self.gates
            .iter()
            .map(|gate| match *gate {
                Gate::Add(b, c) => next[b] + next[c],
                Gate::Mul(b, c) => next[b] * next[c],
            })
            .collect()
    }

    // Circuit checks the dimensions; this layer supplies its wiring predicates.
    pub(crate) fn wiring_evaluations<F: Field>(&self, r_i: &[F], b: &[F], c: &[F]) -> (F, F) {
        let mut add_i = F::ZERO;
        let mut mult_i = F::ZERO;
        for (a, gate) in self.gates.iter().enumerate() {
            let (left, right) = gate.inputs();
            // Lemma 3.6: sum the basis values at the nonzero wiring entries.
            let weight = chi_at(a, r_i) * chi_at(left, b) * chi_at(right, c);
            match gate {
                Gate::Add(..) => add_i += weight,
                Gate::Mul(..) => mult_i += weight,
            }
        }
        (add_i, mult_i)
    }
}
