use crate::{Error, Layer};
use ark_ff::Field;

/// A layered arithmetic circuit with power-of-two layer widths.
///
/// `layers[0]` contains output gates; `layers[d-1]` reads the public input
/// layer, of size `input_size`. There is no padding or implicit rewiring.
/// An empty list of gate layers is the identity circuit on the input.
#[derive(Debug, Clone)]
pub struct Circuit {
    input_size: usize,
    layers: Vec<Layer>,
}

impl Circuit {
    /// Validates the input width and all connections between adjacent layers.
    pub fn new(input_size: usize, layers: Vec<Layer>) -> Result<Self, Error> {
        if !input_size.is_power_of_two() {
            return Err(Error::InvalidCircuit);
        }
        let mut next_width = input_size;
        for layer in layers.iter().rev() {
            for gate in layer.gates() {
                let (b, c) = gate.inputs();
                if b >= next_width || c >= next_width {
                    return Err(Error::InvalidCircuit);
                }
            }
            next_width = layer.width();
        }
        Ok(Self { input_size, layers })
    }

    /// Returns the number `d` of non-input layers.
    pub fn depth(&self) -> usize {
        self.layers.len()
    }

    /// Returns the size of the public input layer.
    pub fn input_size(&self) -> usize {
        self.input_size
    }

    /// Returns gate layers in the book's output-to-input order.
    pub fn layers(&self) -> &[Layer] {
        &self.layers
    }

    pub(crate) fn width(&self, i: usize) -> usize {
        if i == self.depth() {
            self.input_size
        } else {
            self.layers[i].width()
        }
    }

    /// Evaluates the circuit, returning all tables `[W_0, ..., W_d]`.
    ///
    /// Used by the honest prover and examples, never by the verifier.
    pub fn evaluate<F: Field>(&self, input: &[F]) -> Result<Vec<Vec<F>>, Error> {
        if input.len() != self.input_size {
            return Err(Error::DimensionMismatch);
        }
        // Computation goes from inputs to outputs, opposite to verification.
        let mut w = vec![input.to_vec()];
        for layer in self.layers.iter().rev() {
            let next = w.last().expect("input layer is present");
            w.push(layer.evaluate(next));
        }
        w.reverse();
        Ok(w)
    }

    /// Evaluates `(add_i_tilde, mult_i_tilde)` at `(r_i, b, c)`.
    ///
    /// By Lemma 3.6, each gate `a` contributes
    /// `chi_a(r_i) * chi_{in_1(a)}(b) * chi_{in_2(a)}(c)` to its gate type's
    /// wiring MLE. This sums only the nonzero entries of the wiring table.
    /// It uses `O(S_i * (k_i + k_{i+1}))` operations for arbitrary wiring.
    pub fn wiring_evaluations<F: Field>(
        &self,
        i: usize,
        r_i: &[F],
        b: &[F],
        c: &[F],
    ) -> Result<(F, F), Error> {
        if i >= self.depth() {
            return Err(Error::UnexpectedMessage);
        }
        let k_i = self.layers[i].num_vars();
        let k_next = self.width(i + 1).ilog2() as usize;
        if r_i.len() != k_i || b.len() != k_next || c.len() != k_next {
            return Err(Error::DimensionMismatch);
        }
        Ok(self.layers[i].wiring_evaluations(r_i, b, c))
    }
}
