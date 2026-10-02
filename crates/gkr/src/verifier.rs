use crate::{Circuit, Error};
use ark_ff::Field;
use ark_poly::{Polynomial, univariate::DensePolynomial};
use ark_std::rand::{CryptoRng, RngCore};
use multilinear_ext::MultilinearExtension;
use sum_check::{Subclaim, Verifier as SumCheckVerifier};

/// The interactive verifier of Figure 4.13.
///
/// Knows only the circuit wiring, public input, and claimed output. It never
/// constructs internal layer values. Only [`Self::finish`] accepts; any failed
/// message permanently rejects this session. The RNG must be privately seeded
/// and challenges must be revealed only after the corresponding prover message.
pub struct Verifier<'a, F: Field> {
    circuit: &'a Circuit,
    input: MultilinearExtension<F>,
    i: usize,
    r_i: Vec<F>,
    m_i: F,
    sum_check: Option<SumCheckVerifier<F>>,
    rejected: bool,
}

impl<'a, F: Field> Verifier<'a, F> {
    /// Receives the output table `D`, then samples `r_0` and sets `m_0 = D_tilde(r_0)`.
    ///
    /// Input and output lengths must match the public circuit exactly.
    pub fn new<R: RngCore + CryptoRng>(
        circuit: &'a Circuit,
        input: &[F],
        claimed_output: &[F],
        rng: &mut R,
    ) -> Result<Self, Error> {
        if input.len() != circuit.input_size() || claimed_output.len() != circuit.width(0) {
            return Err(Error::DimensionMismatch);
        }
        let input = MultilinearExtension::new(input.to_vec()).expect("validated input width");
        let d = MultilinearExtension::new(claimed_output.to_vec()).expect("validated output width");
        let r_i: Vec<F> = (0..d.num_vars()).map(|_| F::rand(rng)).collect();
        let m_i = d.evaluate(&r_i).expect("point matches output dimension");
        let mut verifier = Self {
            circuit,
            input,
            i: 0,
            r_i,
            m_i,
            sum_check: None,
            rejected: false,
        };
        verifier.start_sum_check();
        Ok(verifier)
    }

    /// Returns the current layer point `r_i`, sent to the prover.
    pub fn point(&self) -> &[F] {
        &self.r_i
    }

    fn start_sum_check(&mut self) {
        if self.i < self.circuit.depth() {
            let k_next = self.circuit.width(self.i + 1).ilog2() as usize;
            // A width-one next layer has no variables: skip sum-check rounds,
            // but still check the constant line polynomial and layer equation.
            if k_next > 0 {
                self.sum_check = Some(
                    SumCheckVerifier::new(self.m_i, vec![2; 2 * k_next])
                        .expect("positive number of sum-check variables"),
                );
            }
        }
    }

    /// Receives `g_j`, checks its degree and sum, then sends a fresh `r_j`.
    pub fn verify_round<R: RngCore + CryptoRng>(
        &mut self,
        g_j: &DensePolynomial<F>,
        rng: &mut R,
    ) -> Result<F, Error> {
        if self.rejected {
            return Err(Error::UnexpectedMessage);
        }
        // A fallible check leaves the session rejected unless it fully succeeds.
        self.rejected = true;
        let sum_check = self.sum_check.as_mut().ok_or(Error::UnexpectedMessage)?;
        let r_j = sum_check.verify_round(g_j, rng)?;
        self.rejected = false;
        Ok(r_j)
    }

    /// Receives `q`, checks the final sum-check equation, then samples `r*`.
    ///
    /// Uses `q(0)` and `q(1)` for the two claimed next-layer values, as in
    /// Figure 4.13. Then sets `r_{i+1} = ell(r*)` and `m_{i+1} = q(r*)`.
    /// The line claim remains unproven until later layers and the public input
    /// establish it. No new challenge is sampled for an invalid message.
    pub fn verify_line<R: RngCore + CryptoRng>(
        &mut self,
        q: &DensePolynomial<F>,
        rng: &mut R,
    ) -> Result<Vec<F>, Error> {
        if self.rejected || self.i == self.circuit.depth() {
            self.rejected = true;
            return Err(Error::UnexpectedMessage);
        }
        self.rejected = true;
        let k_next = self.circuit.width(self.i + 1).ilog2() as usize;

        // 1. W_{i+1} is multilinear, so its restriction to a line has degree <= k_next.
        let degree = q.coeffs.iter().rposition(|c| !c.is_zero()).unwrap_or(0);
        if degree > k_next {
            return Err(Error::LineDegreeTooHigh);
        }
        let subclaim = match self.sum_check.take() {
            Some(sum_check) => sum_check.reduce()?,
            None => Subclaim {
                point: Vec::new(),
                value: self.m_i,
            },
        };
        let (b, c) = subclaim.point.split_at(k_next);

        // 2. Complete sum-check conditionally on the line endpoints being true.
        let (add_i, mult_i) = self.circuit.wiring_evaluations(self.i, &self.r_i, b, c)?;
        let w_b = q.evaluate(&F::ZERO);
        let w_c = q.evaluate(&F::ONE);
        let f_at_b_c = add_i * (w_b + w_c) + mult_i * w_b * w_c;
        if subclaim.value != f_at_b_c {
            return Err(Error::LayerMismatch);
        }

        // 3. Reduce the two endpoint claims to one random point on the line.
        // q must be received and checked BEFORE this challenge is sampled.
        let r_star = F::rand(rng);
        self.r_i = b
            .iter()
            .zip(c)
            .map(|(&b_j, &c_j)| b_j + r_star * (c_j - b_j))
            .collect();
        self.m_i = q.evaluate(&r_star);
        self.i += 1;
        self.start_sum_check();
        self.rejected = false;
        Ok(self.r_i.clone())
    }

    /// Accepts only when all layers have reduced to the correct public-input MLE.
    pub fn finish(self) -> Result<(), Error> {
        if self.rejected || self.i != self.circuit.depth() {
            return Err(Error::UnexpectedMessage);
        }
        let w_d_at_r_d = self
            .input
            .evaluate(&self.r_i)
            .expect("point matches input dimension");
        if self.m_i != w_d_at_r_d {
            return Err(Error::InputMismatch);
        }
        Ok(())
    }
}
