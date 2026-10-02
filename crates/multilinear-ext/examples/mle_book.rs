//! Evaluates the multilinear extension from Figure 3.2 over F_5.

use ark_ff::{Fp64, MontBackend, MontConfig};
use multilinear_ext::MultilinearExtension;

#[derive(MontConfig)]
#[modulus = "5"]
#[generator = "2"]
struct F5Config;
type F5 = Fp64<MontBackend<F5Config, 1>>;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // The first variable changes fastest in arkworks' table order:
    // (0,0), (1,0), (0,1), (1,1).
    let f = [1, 1, 2, 4].into_iter().map(F5::from).collect();
    let f_tilde = MultilinearExtension::new(f)?;

    // Figure 3.2 gives:
    // f_tilde(X_1, X_2) = (1-X_1)(1-X_2) + 2(1-X_1)X_2
    //                    + X_1(1-X_2) + 4 X_1 X_2
    //                  = 1 + X_2 + 2 X_1 X_2.
    let r = [F5::from(2), F5::from(3)];
    let direct = f_tilde.evaluate_direct(&r)?;
    let memoized = f_tilde.evaluate(&r)?;
    assert_eq!(direct, memoized);
    assert_eq!(direct, F5::from(16)); // 1 + 3 + 2*2*3 = 16 = 1 mod 5.
    println!("Both methods give f_tilde(2, 3) = {direct} in F_5.");
    Ok(())
}
