use crate::{Circuit, Error, Gate, Layer, chi_at};
use ark_ff::Field;
use ark_poly::{DenseUVPolynomial, univariate::DensePolynomial};
use multilinear_ext::MultilinearExtension;

/// An honest prover that evaluates the circuit once and stores `W_i` as MLEs.
///
/// Start each layer with [`Self::layer`], using the point sent by the verifier.
pub struct Prover<'a, F: Field> {
    circuit: &'a Circuit,
    w: Vec<MultilinearExtension<F>>,
}

impl<'a, F: Field> Prover<'a, F> {
    /// Evaluates the circuit on `input` and stores its layer tables.
    pub fn new(circuit: &'a Circuit, input: &[F]) -> Result<Self, Error> {
        let w = circuit
            .evaluate(input)?
            .into_iter()
            .map(|values| MultilinearExtension::new(values).expect("validated layer width"))
            .collect();
        Ok(Self { circuit, w })
    }

    /// Returns `D = W_0`, the output table sent before the first challenge.
    pub fn outputs(&self) -> &[F] {
        self.w[0].evaluations()
    }

    /// Starts sum-check for Equation 4.18 at layer `i` and point `r_i`.
    pub fn layer(&self, i: usize, r_i: &[F]) -> Result<LayerProver<'_, F>, Error> {
        if i >= self.circuit.depth() {
            return Err(Error::UnexpectedMessage);
        }
        if r_i.len() != self.w[i].num_vars() {
            return Err(Error::DimensionMismatch);
        }
        let layer = &self.circuit.layers()[i];
        let w_next = &self.w[i + 1];
        let weights = (0..layer.width()).map(|a| chi_at(a, r_i)).collect();
        Ok(LayerProver {
            layer,
            w_next,
            weights,
            b_values: w_next.evaluations().to_vec(),
            c_values: w_next.evaluations().to_vec(),
            r: Vec::new(),
        })
    }
}

/// The honest prover for one GKR layer, using sparse wiring (Section 4.6.5).
///
/// The variable order is `(b_1, ..., b_k, c_1, ..., c_k)`, where `k = k_{i+1}`.
/// Each round returns a polynomial of degree at most two. Send it to the
/// verifier, then pass the returned challenge to [`Self::bind`]. After all
/// `2k` rounds, send [`Self::line_polynomial`] to reduce two claims to one.
pub struct LayerProver<'a, F: Field> {
    layer: &'a Layer,
    w_next: &'a MultilinearExtension<F>,
    // For each gate: chi_a(r_i) times the basis factors fixed by challenges.
    weights: Vec<F>,
    // W_{i+1} with the current b-prefix or c-prefix fixed, respectively.
    b_values: Vec<F>,
    c_values: Vec<F>,
    r: Vec<F>,
}

impl<F: Field> LayerProver<'_, F> {
    /// Returns `2k`, the number of sum-check rounds for this layer.
    pub fn num_rounds(&self) -> usize {
        2 * self.w_next.num_vars()
    }

    /// Computes the next quadratic `g_j` without enumerating all wire pairs.
    ///
    /// Boolean suffixes collapse each gate's wiring basis to a single suffix.
    /// The remaining contribution is a product of two linear polynomials:
    /// the current wiring factor and a gate-value expression. Thus a single
    /// pass over the gates suffices, in `O(S_i)` field operations per round.
    pub fn round_polynomial(&self) -> Result<DensePolynomial<F>, Error> {
        if self.r.len() == self.num_rounds() {
            return Err(Error::UnexpectedMessage);
        }
        let k = self.w_next.num_vars();
        let j = self.r.len();
        let in_b = j < k;
        let coordinate = if in_b { j } else { j - k };
        let mut coefficients = vec![F::ZERO; 3];

        for (a, gate) in self.layer.gates().iter().enumerate() {
            let (left, right) = gate.inputs();
            let (label, values, other_value) = if in_b {
                (left, &self.b_values, self.w_next.evaluations()[right])
            } else {
                (right, &self.c_values, self.b_values[0])
            };

            // After fixing the prefix, adjacent entries give W(..., 0, suffix)
            // and W(..., 1, suffix). Interpolate the current free variable X.
            let pair = (label >> coordinate) & !1;
            let w_0 = values[pair];
            let w_1 = values[pair + 1];
            let slope = w_1 - w_0;
            let (value_0, value_1) = match gate {
                Gate::Add(..) => (w_0 + other_value, slope),
                Gate::Mul(..) => (w_0 * other_value, slope * other_value),
            };

            // chi_bit(X) is X for bit 1, or 1-X for bit 0.
            let bit_is_one = (label >> coordinate) & 1 == 1;
            let (basis_0, basis_1) = if bit_is_one {
                (F::ZERO, F::ONE)
            } else {
                (F::ONE, -F::ONE)
            };

            // Expand weight * (basis_0 + basis_1 X) * (value_0 + value_1 X).
            let weight = self.weights[a];
            coefficients[0] += weight * basis_0 * value_0;
            coefficients[1] += weight * (basis_0 * value_1 + basis_1 * value_0);
            coefficients[2] += weight * basis_1 * value_1;
        }
        Ok(DensePolynomial::from_coefficients_vec(coefficients))
    }

    /// Fixes the current variable to the challenge `r_j` sent by the verifier.
    pub fn bind(&mut self, r_j: F) -> Result<(), Error> {
        if self.r.len() == self.num_rounds() {
            return Err(Error::UnexpectedMessage);
        }
        let k = self.w_next.num_vars();
        let j = self.r.len();
        let in_b = j < k;
        let coordinate = if in_b { j } else { j - k };

        for (weight, gate) in self.weights.iter_mut().zip(self.layer.gates()) {
            let (left, right) = gate.inputs();
            let label = if in_b { left } else { right };
            let bit_is_one = (label >> coordinate) & 1 == 1;
            *weight *= if bit_is_one { r_j } else { F::ONE - r_j };
        }

        // Fold the evaluation table: W(r_j, suffix) = (1-r_j)W(0,suffix)
        //                                             + r_j W(1,suffix).
        let values = if in_b {
            &mut self.b_values
        } else {
            &mut self.c_values
        };
        for index in 0..values.len() / 2 {
            values[index] = (F::ONE - r_j) * values[2 * index] + r_j * values[2 * index + 1];
        }
        values.truncate(values.len() / 2);
        self.r.push(r_j);
        Ok(())
    }

    /// Returns `q(T) = W_{i+1}_tilde(b* + T(c* - b*))`, of degree at most `k`.
    ///
    /// We fold the original table along the line, just as `bind` folds at a
    /// field element, but now each entry is a polynomial in `T`. Coefficient
    /// arithmetic avoids interpolation divisions and works in any field.
    pub fn line_polynomial(&self) -> Result<DensePolynomial<F>, Error> {
        if self.r.len() != self.num_rounds() {
            return Err(Error::UnexpectedMessage);
        }
        let k = self.w_next.num_vars();
        let (b, c) = self.r.split_at(k);
        let mut table: Vec<Vec<F>> = self.w_next.evaluations().iter().map(|&w| vec![w]).collect();
        for j in 0..k {
            let mut next_table = Vec::with_capacity(table.len() / 2);
            let direction = c[j] - b[j];
            for [q_0, q_1] in table.as_chunks::<2>().0 {
                let mut q = vec![F::ZERO; q_0.len() + 1];
                for power in 0..q_0.len() {
                    // (1 - ell_j(T)) q_0(T) + ell_j(T) q_1(T),
                    // where ell_j(T) = b_j + T(c_j - b_j).
                    q[power] += (F::ONE - b[j]) * q_0[power] + b[j] * q_1[power];
                    q[power + 1] += direction * (q_1[power] - q_0[power]);
                }
                next_table.push(q);
            }
            table = next_table;
        }
        Ok(DensePolynomial::from_coefficients_vec(
            table.pop().expect("nonempty layer table"),
        ))
    }
}
