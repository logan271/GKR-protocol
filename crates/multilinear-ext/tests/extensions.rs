//! Book examples, interpolation identities, and comparison with arkworks.

use ark_bn254::Fr;
use ark_ff::{AdditiveGroup, Field, Fp64, MontBackend, MontConfig, UniformRand};
use ark_poly::{DenseMultilinearExtension, Polynomial};
use ark_std::rand::{SeedableRng, rngs::StdRng};
use multilinear_ext::{Error, MultilinearExtension, chi};

#[derive(MontConfig)]
#[modulus = "5"]
#[generator = "2"]
struct F5Config;
type F5 = Fp64<MontBackend<F5Config, 1>>;

#[derive(MontConfig)]
#[modulus = "11"]
#[generator = "2"]
struct F11Config;
type F11 = Fp64<MontBackend<F11Config, 1>>;

fn boolean_point(index: usize, v: usize) -> Vec<bool> {
    (0..v).map(|i| (index >> i) & 1 == 1).collect()
}

#[test]
fn basis_is_one_at_w_and_zero_at_other_boolean_points() {
    for v in 0..=3 {
        for w_index in 0..1 << v {
            let w = boolean_point(w_index, v);
            for y_index in 0..1 << v {
                let y: Vec<Fr> = boolean_point(y_index, v)
                    .into_iter()
                    .map(|bit| Fr::from(u64::from(bit)))
                    .collect();
                let expected = if w_index == y_index {
                    Fr::ONE
                } else {
                    Fr::ZERO
                };
                assert_eq!(chi(&w, &y).unwrap(), expected);
            }
        }
    }
}

#[test]
fn basis_values_sum_to_one_away_from_boolean_points() {
    let r = [Fr::from(2), Fr::from(3), Fr::from(7)];
    let sum: Fr = (0..8)
        .map(|index| chi(&boolean_point(index, 3), &r).unwrap())
        .sum();
    assert_eq!(sum, Fr::ONE);
}

#[test]
fn reproduces_figure_3_2_over_f5() {
    // f(0,0)=1, f(0,1)=2, f(1,0)=1, f(1,1)=4.
    let f = [1, 1, 2, 4].into_iter().map(F5::from).collect();
    let f_tilde = MultilinearExtension::new(f).unwrap();
    assert_eq!(f_tilde.num_vars(), 2);

    for x_1 in 0..5 {
        for x_2 in 0..5 {
            let x_1 = F5::from(x_1);
            let x_2 = F5::from(x_2);
            // The four Lagrange terms in the figure simplify to this polynomial.
            let expected = F5::ONE + x_2 + F5::from(2) * x_1 * x_2;
            assert_eq!(f_tilde.evaluate(&[x_1, x_2]).unwrap(), expected);
            assert_eq!(f_tilde.evaluate_direct(&[x_1, x_2]).unwrap(), expected);
        }
    }
}

#[test]
fn reproduces_exercise_3_3_over_f11() {
    // First table: f_tilde(X_1, X_2) = 3 - 2 X_1 + X_2.
    let f = [3, 1, 4, 2].into_iter().map(F11::from).collect();
    let f_tilde = MultilinearExtension::new(f).unwrap();
    let r = [F11::from(2), F11::from(4)];
    assert_eq!(f_tilde.evaluate(&r).unwrap(), F11::from(3));
    assert_eq!(f_tilde.evaluate_direct(&r).unwrap(), F11::from(3));

    // Second table: f_tilde(X_1, X_2, X_3) = 1 + 2 X_1 + X_2 + 4 X_3.
    let f = [1, 3, 2, 4, 5, 7, 6, 8]
        .into_iter()
        .map(F11::from)
        .collect();
    let f_tilde = MultilinearExtension::new(f).unwrap();
    let r = [F11::from(2), F11::from(4), F11::from(6)];
    assert_eq!(f_tilde.evaluate(&r).unwrap(), F11::ZERO);
    assert_eq!(f_tilde.evaluate_direct(&r).unwrap(), F11::ZERO);
}

#[test]
fn extends_every_boolean_evaluation_in_arkworks_order() {
    let f: Vec<Fr> = (0..8).map(|i| Fr::from(i * i + 3)).collect();
    let f_tilde = MultilinearExtension::new(f.clone()).unwrap();
    assert_eq!(f_tilde.evaluations(), f);

    for (index, value) in f.into_iter().enumerate() {
        let w: Vec<Fr> = boolean_point(index, 3)
            .into_iter()
            .map(|bit| Fr::from(u64::from(bit)))
            .collect();
        assert_eq!(f_tilde.evaluate(&w).unwrap(), value);
        assert_eq!(f_tilde.evaluate_direct(&w).unwrap(), value);
    }
}

#[test]
fn both_algorithms_match_arkworks_on_random_tables_and_points() {
    let mut rng = StdRng::seed_from_u64(35);
    for v in 0..=6 {
        for _ in 0..8 {
            let f: Vec<Fr> = (0..1 << v).map(|_| Fr::rand(&mut rng)).collect();
            let r: Vec<Fr> = (0..v).map(|_| Fr::rand(&mut rng)).collect();
            let arkworks = DenseMultilinearExtension::from_evaluations_vec(v, f.clone());
            let f_tilde = MultilinearExtension::new(f).unwrap();
            let expected = arkworks.evaluate(&r);
            assert_eq!(f_tilde.evaluate(&r).unwrap(), expected);
            assert_eq!(f_tilde.evaluate_direct(&r).unwrap(), expected);
        }
    }
}

#[test]
fn is_linear_in_each_variable_with_other_variables_fixed() {
    let f = [4, 1, 9, 2, 7, 3, 8, 6].into_iter().map(Fr::from).collect();
    let f_tilde = MultilinearExtension::new(f).unwrap();
    let r = [Fr::from(2), Fr::from(3), Fr::from(5)];
    for i in 0..r.len() {
        let mut at_zero = r;
        at_zero[i] = Fr::ZERO;
        let mut at_one = r;
        at_one[i] = Fr::ONE;
        let expected = (Fr::ONE - r[i]) * f_tilde.evaluate(&at_zero).unwrap()
            + r[i] * f_tilde.evaluate(&at_one).unwrap();
        assert_eq!(f_tilde.evaluate(&r).unwrap(), expected);
    }
}

#[test]
fn handles_constant_zero_and_zero_variable_tables() {
    for v in 0..=4 {
        for value in [Fr::ZERO, Fr::from(7)] {
            let f_tilde = MultilinearExtension::new(vec![value; 1 << v]).unwrap();
            let r = vec![Fr::from(3); v];
            assert_eq!(f_tilde.num_vars(), v);
            assert_eq!(f_tilde.evaluate(&r).unwrap(), value);
            assert_eq!(f_tilde.evaluate_direct(&r).unwrap(), value);
        }
    }
    assert_eq!(chi::<Fr>(&[], &[]), Ok(Fr::ONE));
}

#[test]
fn rejects_invalid_table_sizes_and_dimensions() {
    for size in [0, 3, 5, 6] {
        assert_eq!(
            MultilinearExtension::new(vec![Fr::ZERO; size]),
            Err(Error::InvalidTableLength)
        );
    }
    let f_tilde = MultilinearExtension::new(vec![Fr::ZERO; 4]).unwrap();
    for r in [vec![], vec![Fr::ONE], vec![Fr::ONE; 3]] {
        assert_eq!(f_tilde.evaluate(&r), Err(Error::DimensionMismatch));
        assert_eq!(f_tilde.evaluate_direct(&r), Err(Error::DimensionMismatch));
    }
    assert_eq!(chi(&[false], &[Fr::ONE; 2]), Err(Error::DimensionMismatch));
    assert_eq!(
        chi(&[false, true], &[Fr::ONE]),
        Err(Error::DimensionMismatch)
    );
    let constant = MultilinearExtension::new(vec![Fr::ONE]).unwrap();
    assert_eq!(constant.evaluate(&[Fr::ONE]), Err(Error::DimensionMismatch));
}
