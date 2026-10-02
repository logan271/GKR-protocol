//! Figure 4.12: prove the two outputs [36, 6] from the book's multiplication circuit.

use ark_bn254::Fr;
use ark_std::rand::rngs::OsRng;
use gkr::{Circuit, Gate, Layer, Prover, Verifier};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // The book's Boolean labels (00, 01, 10, 11) must be reordered to our
    // little-endian table order (00, 10, 01, 11). Thus W_2 is [3, 3, 2, 1].
    let input: Vec<Fr> = [3, 3, 2, 1].into_iter().map(Fr::from).collect();
    let circuit = Circuit::new(
        4,
        vec![
            // Layer 0: W_0 = [9*4, 6*1] = [36, 6].
            Layer::new(vec![Gate::Mul(0, 2), Gate::Mul(1, 3)])?,
            // Layer 1: W_1 = [3*3, 2*3, 2*2, 1*1] = [9, 6, 4, 1].
            Layer::new(vec![
                Gate::Mul(0, 0),
                Gate::Mul(2, 1),
                Gate::Mul(2, 2),
                Gate::Mul(3, 3),
            ])?,
        ],
    )?;

    // P sends D, the claimed output table. Only then does V sample r_0.
    let prover = Prover::new(&circuit, &input)?;
    let mut rng = OsRng;
    let mut verifier = Verifier::new(&circuit, &input, prover.outputs(), &mut rng)?;

    for i in 0..circuit.depth() {
        let mut layer = prover.layer(i, verifier.point())?;
        // Sum-check reduces m_i = W_i_tilde(r_i) to values at (b*, c*).
        for _ in 0..layer.num_rounds() {
            let g_j = layer.round_polynomial()?;
            let r_j = verifier.verify_round(&g_j, &mut rng)?;
            layer.bind(r_j)?;
        }
        // P sends q(T) = W_{i+1}_tilde(b* + T(c* - b*)).
        // V checks the endpoints, samples r*, and continues at ell(r*).
        let q = layer.line_polynomial()?;
        verifier.verify_line(&q, &mut rng)?;
    }

    // V checks the final claim against the MLE of the public input.
    verifier.finish()?;
    assert_eq!(prover.outputs(), &[Fr::from(36), Fr::from(6)]);
    println!("Accepted the book's circuit outputs: [36, 6].");
    Ok(())
}
