//! Completeness, the book's identities, and rejection of malicious messages.

use ark_bn254::Fr;
use ark_ff::{AdditiveGroup, Field, UniformRand};
use ark_poly::{DenseUVPolynomial, Polynomial, univariate::DensePolynomial};
use ark_std::rand::{Rng, RngCore, SeedableRng, rngs::StdRng};
use gkr::{Circuit, Error, Gate, Layer, Prover, Verifier};
use multilinear_ext::MultilinearExtension;

// Keep circuit fixtures compact while exercising both constructors' validation.
fn make_circuit(input_size: usize, gates: Vec<Vec<Gate>>) -> Result<Circuit, Error> {
    let layers = gates
        .into_iter()
        .map(Layer::new)
        .collect::<Result<_, _>>()?;
    Circuit::new(input_size, layers)
}

fn book_circuit() -> Circuit {
    make_circuit(
        4,
        vec![
            vec![Gate::Mul(0, 2), Gate::Mul(1, 3)],
            vec![
                Gate::Mul(0, 0),
                Gate::Mul(2, 1),
                Gate::Mul(2, 2),
                Gate::Mul(3, 3),
            ],
        ],
    )
    .unwrap()
}

fn book_input() -> Vec<Fr> {
    [3, 3, 2, 1].into_iter().map(Fr::from).collect()
}

fn poly(coefficients: &[u64]) -> DensePolynomial<Fr> {
    DensePolynomial::from_coefficients_vec(coefficients.iter().copied().map(Fr::from).collect())
}

fn boolean_point(index: usize, k: usize) -> Vec<Fr> {
    (0..k)
        .map(|j| Fr::from(((index >> j) & 1) as u64))
        .collect()
}

// The verifier's public input may differ from the dishonest prover's input.
fn run(
    circuit: &Circuit,
    prover_input: &[Fr],
    public_input: &[Fr],
    output: &[Fr],
) -> Result<(), Error> {
    let prover = Prover::new(circuit, prover_input)?;
    let mut rng = StdRng::seed_from_u64(46);
    let mut verifier = Verifier::new(circuit, public_input, output, &mut rng)?;
    for i in 0..circuit.depth() {
        let mut layer = prover.layer(i, verifier.point())?;
        for _ in 0..layer.num_rounds() {
            let g_j = layer.round_polynomial()?;
            layer.bind(verifier.verify_round(&g_j, &mut rng)?)?;
        }
        verifier.verify_line(&layer.line_polynomial()?, &mut rng)?;
    }
    verifier.finish()
}

#[test]
fn reproduces_figure_4_12() {
    let circuit = book_circuit();
    let input = book_input();
    let w = circuit.evaluate(&input).unwrap();
    assert_eq!(w[0], vec![Fr::from(36), Fr::from(6)]);
    assert_eq!(w[1], vec![Fr::from(9), Fr::from(6), Fr::from(4), Fr::ONE]);
    assert_eq!(w[2], input);
    run(&circuit, &input, &input, &w[0]).unwrap();
}

#[test]
fn verifies_mixed_gates_repeated_wires_and_varying_widths() {
    let mut rng = StdRng::seed_from_u64(1234);
    for _ in 0..24 {
        let input_size = 1 << rng.gen_range(0..=3);
        let mut next_width = input_size;
        let mut layers = Vec::new();
        for _ in 0..rng.gen_range(1..=4) {
            let width = 1 << rng.gen_range(0..=3);
            let gates = (0..width)
                .map(|_| {
                    let b = rng.gen_range(0..next_width);
                    let c = rng.gen_range(0..next_width);
                    if rng.gen_bool(0.5) {
                        Gate::Add(b, c)
                    } else {
                        Gate::Mul(b, c)
                    }
                })
                .collect();
            layers.push(gates);
            next_width = width;
        }
        layers.reverse();
        let circuit = make_circuit(input_size, layers).unwrap();
        let input: Vec<Fr> = (0..input_size).map(|_| Fr::rand(&mut rng)).collect();
        let w = circuit.evaluate(&input).unwrap();
        run(&circuit, &input, &input, &w[0]).unwrap();
    }
}

#[test]
fn wiring_mles_match_boolean_predicates() {
    let circuit = make_circuit(4, vec![vec![Gate::Add(0, 3), Gate::Mul(2, 2)]]).unwrap();
    for a in 0..2 {
        for b in 0..4 {
            for c in 0..4 {
                let (add, mult) = circuit
                    .wiring_evaluations(
                        0,
                        &boolean_point(a, 1),
                        &boolean_point(b, 2),
                        &boolean_point(c, 2),
                    )
                    .unwrap();
                assert_eq!(add, Fr::from(u64::from(a == 0 && b == 0 && c == 3)));
                assert_eq!(mult, Fr::from(u64::from(a == 1 && b == 2 && c == 2)));
            }
        }
    }
}

// Evaluate Equation 4.18 directly, independently of the sparse round algorithm.
fn f_at(
    circuit: &Circuit,
    i: usize,
    r_i: &[Fr],
    w_next: &MultilinearExtension<Fr>,
    point: &[Fr],
) -> Fr {
    let (b, c) = point.split_at(w_next.num_vars());
    let (add_i, mult_i) = circuit.wiring_evaluations(i, r_i, b, c).unwrap();
    let w_b = w_next.evaluate(b).unwrap();
    let w_c = w_next.evaluate(c).unwrap();
    add_i * (w_b + w_c) + mult_i * w_b * w_c
}

#[test]
fn sparse_rounds_match_direct_sums_of_equation_4_18_and_line_restriction() {
    let circuit = make_circuit(
        4,
        vec![
            vec![Gate::Add(1, 0), Gate::Mul(0, 0)],
            vec![Gate::Mul(2, 3), Gate::Add(1, 1)],
        ],
    )
    .unwrap();
    let input = book_input();
    let w = circuit.evaluate(&input).unwrap();
    let prover = Prover::new(&circuit, &input).unwrap();
    let mut rng = StdRng::seed_from_u64(99);
    for i in 0..circuit.depth() {
        let w_i = MultilinearExtension::new(w[i].clone()).unwrap();
        let w_next = MultilinearExtension::new(w[i + 1].clone()).unwrap();
        let r_i: Vec<Fr> = (0..w_i.num_vars()).map(|_| Fr::rand(&mut rng)).collect();
        let mut layer = prover.layer(i, &r_i).unwrap();
        let mut r = Vec::new();
        let mut claim = w_i.evaluate(&r_i).unwrap();
        for j in 0..layer.num_rounds() {
            let g_j = layer.round_polynomial().unwrap();
            assert!(g_j.degree() <= 2);
            assert_eq!(g_j.evaluate(&Fr::ZERO) + g_j.evaluate(&Fr::ONE), claim);
            for t in [Fr::ZERO, Fr::ONE, Fr::from(2), Fr::rand(&mut rng)] {
                let suffix_len = layer.num_rounds() - j - 1;
                let mut expected = Fr::ZERO;
                for bits in 0..1 << suffix_len {
                    let mut point = r.clone();
                    point.push(t);
                    point.extend(boolean_point(bits, suffix_len));
                    expected += f_at(&circuit, i, &r_i, &w_next, &point);
                }
                assert_eq!(g_j.evaluate(&t), expected);
            }
            let r_j = Fr::rand(&mut rng);
            claim = g_j.evaluate(&r_j);
            layer.bind(r_j).unwrap();
            r.push(r_j);
        }
        assert_eq!(claim, f_at(&circuit, i, &r_i, &w_next, &r));
        let q = layer.line_polynomial().unwrap();
        assert!(q.degree() <= w_next.num_vars());
        let (b, c) = r.split_at(w_next.num_vars());
        for t in [Fr::ZERO, Fr::ONE, Fr::from(2), Fr::rand(&mut rng)] {
            let ell: Vec<Fr> = b.iter().zip(c).map(|(&b, &c)| b + t * (c - b)).collect();
            assert_eq!(q.evaluate(&t), w_next.evaluate(&ell).unwrap());
        }
    }
}

#[test]
fn handles_single_gate_layers_identity_and_zero_values() {
    for circuit in [
        make_circuit(1, vec![]).unwrap(),
        make_circuit(1, vec![vec![Gate::Mul(0, 0)], vec![Gate::Add(0, 0)]]).unwrap(),
        make_circuit(4, vec![]).unwrap(),
        make_circuit(4, vec![vec![Gate::Add(0, 2)], vec![Gate::Mul(0, 1); 4]]).unwrap(),
    ] {
        for value in [Fr::ZERO, Fr::from(3)] {
            let input = vec![value; circuit.input_size()];
            let w = circuit.evaluate(&input).unwrap();
            run(&circuit, &input, &input, &w[0]).unwrap();
        }
    }
}

#[test]
fn rejects_false_output_and_checks_public_input_at_the_end() {
    let circuit = book_circuit();
    let input = book_input();
    let mut output = circuit.evaluate(&input).unwrap()[0].clone();
    output[0] += Fr::ONE;
    assert!(run(&circuit, &input, &input, &output).is_err());

    // The prover supplies a perfectly consistent execution of the wrong input.
    let other_input = vec![Fr::from(5); 4];
    let other_output = circuit.evaluate(&other_input).unwrap()[0].clone();
    assert_eq!(
        run(&circuit, &other_input, &input, &other_output),
        Err(Error::InputMismatch)
    );
}

#[test]
fn rejects_bad_sum_check_messages_without_sampling_or_recovery() {
    let circuit = book_circuit();
    let input = book_input();
    let prover = Prover::new(&circuit, &input).unwrap();
    for too_high_degree in [false, true] {
        let mut rng = StdRng::seed_from_u64(101);
        let mut verifier = Verifier::new(&circuit, &input, prover.outputs(), &mut rng).unwrap();
        let layer = prover.layer(0, verifier.point()).unwrap();
        let mut g_j = layer.round_polynomial().unwrap();
        if too_high_degree {
            g_j.coeffs.resize(4, Fr::ONE);
        } else {
            g_j.coeffs[0] += Fr::ONE;
        }
        let mut untouched = rng.clone();
        let expected = if too_high_degree {
            sum_check::Error::DegreeTooHigh
        } else {
            sum_check::Error::InconsistentSum
        };
        assert_eq!(
            verifier.verify_round(&g_j, &mut rng),
            Err(Error::SumCheck(expected))
        );
        assert_eq!(rng.next_u64(), untouched.next_u64());
        assert_eq!(
            verifier.verify_round(&layer.round_polynomial().unwrap(), &mut rng),
            Err(Error::UnexpectedMessage)
        );
        assert_eq!(verifier.finish(), Err(Error::UnexpectedMessage));
    }
}

#[test]
fn rejects_high_degree_and_wrong_endpoint_line_messages_without_sampling() {
    let circuit = make_circuit(2, vec![vec![Gate::Add(0, 1)]]).unwrap();
    let input = vec![Fr::from(2), Fr::from(3)];
    let prover = Prover::new(&circuit, &input).unwrap();
    for too_high_degree in [false, true] {
        let mut rng = StdRng::seed_from_u64(102);
        let mut verifier = Verifier::new(&circuit, &input, prover.outputs(), &mut rng).unwrap();
        let mut layer = prover.layer(0, verifier.point()).unwrap();
        for _ in 0..layer.num_rounds() {
            layer
                .bind(
                    verifier
                        .verify_round(&layer.round_polynomial().unwrap(), &mut rng)
                        .unwrap(),
                )
                .unwrap();
        }
        let mut q = layer.line_polynomial().unwrap();
        if too_high_degree {
            q.coeffs.resize(3, Fr::ONE);
        } else {
            q.coeffs[0] += Fr::ONE;
        }
        let mut untouched = rng.clone();
        let expected = if too_high_degree {
            Error::LineDegreeTooHigh
        } else {
            Error::LayerMismatch
        };
        assert_eq!(verifier.verify_line(&q, &mut rng), Err(expected));
        assert_eq!(rng.next_u64(), untouched.next_u64());
        assert_eq!(
            verifier.verify_line(&layer.line_polynomial().unwrap(), &mut rng),
            Err(Error::UnexpectedMessage)
        );
        assert_eq!(verifier.finish(), Err(Error::UnexpectedMessage));
    }
}

#[test]
fn catches_forged_line_that_preserves_both_endpoints() {
    let circuit = make_circuit(4, vec![vec![Gate::Add(0, 1)]]).unwrap();
    let input = book_input();
    let prover = Prover::new(&circuit, &input).unwrap();
    let mut rng = StdRng::seed_from_u64(103);
    let mut verifier = Verifier::new(&circuit, &input, prover.outputs(), &mut rng).unwrap();
    let mut layer = prover.layer(0, verifier.point()).unwrap();
    for _ in 0..layer.num_rounds() {
        layer
            .bind(
                verifier
                    .verify_round(&layer.round_polynomial().unwrap(), &mut rng)
                    .unwrap(),
            )
            .unwrap();
    }
    let mut q = layer.line_polynomial().unwrap();
    // Add T(T-1): this changes the line while preserving q(0), q(1), and degree <= 2.
    q.coeffs.resize(3, Fr::ZERO);
    q.coeffs[1] -= Fr::ONE;
    q.coeffs[2] += Fr::ONE;
    verifier.verify_line(&q, &mut rng).unwrap();
    assert_eq!(verifier.finish(), Err(Error::InputMismatch));
}

#[test]
fn rejects_missing_extra_or_reordered_messages() {
    let circuit = make_circuit(2, vec![vec![Gate::Add(0, 1)]]).unwrap();
    let input = vec![Fr::ONE; 2];
    let prover = Prover::new(&circuit, &input).unwrap();
    let mut rng = StdRng::seed_from_u64(104);
    let verifier = Verifier::new(&circuit, &input, prover.outputs(), &mut rng).unwrap();
    assert_eq!(verifier.finish(), Err(Error::UnexpectedMessage));
    let mut verifier = Verifier::new(&circuit, &input, prover.outputs(), &mut rng).unwrap();
    assert_eq!(
        verifier.verify_line(&poly(&[1]), &mut rng),
        Err(Error::SumCheck(sum_check::Error::Incomplete))
    );
    let mut verifier = Verifier::new(&circuit, &input, prover.outputs(), &mut rng).unwrap();
    let mut layer = prover.layer(0, verifier.point()).unwrap();
    assert_eq!(layer.line_polynomial(), Err(Error::UnexpectedMessage));
    for _ in 0..layer.num_rounds() {
        layer
            .bind(
                verifier
                    .verify_round(&layer.round_polynomial().unwrap(), &mut rng)
                    .unwrap(),
            )
            .unwrap();
    }
    assert_eq!(layer.round_polynomial(), Err(Error::UnexpectedMessage));
    assert_eq!(layer.bind(Fr::ONE), Err(Error::UnexpectedMessage));
    // An extra sum-check round poisons the session, even if followed by a valid line.
    assert_eq!(
        verifier.verify_round(&poly(&[1]), &mut rng),
        Err(Error::SumCheck(sum_check::Error::InvalidRound))
    );
    assert_eq!(
        verifier.verify_line(&layer.line_polynomial().unwrap(), &mut rng),
        Err(Error::UnexpectedMessage)
    );

    for send_line in [false, true] {
        let mut verifier = Verifier::new(&circuit, &input, prover.outputs(), &mut rng).unwrap();
        let mut layer = prover.layer(0, verifier.point()).unwrap();
        for _ in 0..layer.num_rounds() {
            layer
                .bind(
                    verifier
                        .verify_round(&layer.round_polynomial().unwrap(), &mut rng)
                        .unwrap(),
                )
                .unwrap();
        }
        verifier
            .verify_line(&layer.line_polynomial().unwrap(), &mut rng)
            .unwrap();
        if send_line {
            assert_eq!(
                verifier.verify_line(&poly(&[1]), &mut rng),
                Err(Error::UnexpectedMessage)
            );
        } else {
            assert_eq!(
                verifier.verify_round(&poly(&[1]), &mut rng),
                Err(Error::UnexpectedMessage)
            );
        }
        assert_eq!(verifier.finish(), Err(Error::UnexpectedMessage));
    }
}

#[test]
fn rejects_invalid_circuits_and_dimensions() {
    for (size, layers) in [
        (0, vec![]),
        (3, vec![]),
        (2, vec![vec![]]),
        (2, vec![vec![Gate::Add(0, 1); 3]]),
        (2, vec![vec![Gate::Add(0, 2)]]),
        (2, vec![vec![Gate::Mul(1, 0)], vec![Gate::Add(0, 1)]]),
    ] {
        assert!(matches!(
            make_circuit(size, layers),
            Err(Error::InvalidCircuit)
        ));
    }
    let circuit = book_circuit();
    assert_eq!(circuit.evaluate(&[Fr::ZERO]), Err(Error::DimensionMismatch));
    assert!(matches!(
        Prover::new(&circuit, &[] as &[Fr]),
        Err(Error::DimensionMismatch)
    ));
    let input = book_input();
    let prover = Prover::new(&circuit, &input).unwrap();
    assert!(matches!(
        prover.layer(2, &[]),
        Err(Error::UnexpectedMessage)
    ));
    assert!(matches!(
        prover.layer(0, &[]),
        Err(Error::DimensionMismatch)
    ));
    assert_eq!(
        circuit.wiring_evaluations(0, &[], &[Fr::ZERO; 2], &[Fr::ZERO; 2]),
        Err(Error::DimensionMismatch)
    );
    assert_eq!(
        circuit.wiring_evaluations::<Fr>(2, &[], &[], &[]),
        Err(Error::UnexpectedMessage)
    );
    let mut rng = StdRng::seed_from_u64(105);
    let mut untouched = rng.clone();
    assert!(matches!(
        Verifier::new(&circuit, &input, &[Fr::ZERO], &mut rng),
        Err(Error::DimensionMismatch)
    ));
    assert!(matches!(
        Verifier::new(&circuit, &input[..3], prover.outputs(), &mut rng),
        Err(Error::DimensionMismatch)
    ));
    assert_eq!(rng.next_u64(), untouched.next_u64());
}

#[test]
fn checks_width_one_layers_without_sum_check_rounds() {
    let circuit = make_circuit(1, vec![vec![Gate::Add(0, 0)]]).unwrap();
    let input = vec![Fr::from(3)];
    assert_eq!(
        run(&circuit, &input, &input, &[Fr::from(7)]),
        Err(Error::LayerMismatch)
    );
    let mut rng = StdRng::seed_from_u64(106);
    let mut verifier = Verifier::new(&circuit, &input, &[Fr::from(6)], &mut rng).unwrap();
    assert_eq!(
        verifier.verify_line(&poly(&[3, 1]), &mut rng),
        Err(Error::LineDegreeTooHigh)
    );
    let mut verifier = Verifier::new(&circuit, &input, &[Fr::from(6)], &mut rng).unwrap();
    assert_eq!(
        verifier.verify_round(&poly(&[3]), &mut rng),
        Err(Error::UnexpectedMessage)
    );
    assert_eq!(verifier.finish(), Err(Error::UnexpectedMessage));
}

#[test]
fn accepts_non_normalized_line_coefficients() {
    let circuit = make_circuit(1, vec![vec![Gate::Add(0, 0)]]).unwrap();
    let input = vec![Fr::from(3)];
    let mut rng = StdRng::seed_from_u64(107);
    let mut verifier = Verifier::new(&circuit, &input, &[Fr::from(6)], &mut rng).unwrap();
    let q = DensePolynomial {
        coeffs: vec![Fr::from(3), Fr::ZERO, Fr::ZERO],
    };
    verifier.verify_line(&q, &mut rng).unwrap();
    verifier.finish().unwrap();
}
