use blstrs::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use ff::{Field, PrimeField};
use group::prime::PrimeCurveAffine;
use group::Group;
use halo2_proofs::arithmetic::best_fft;

/*
    This module contains the functions that will be exported to C.
    Besides this, it contains a helper function that will be used by the exported functions.

    The main two functions are `get_poly_commitment_g1` and `get_poly_commitment_g2`.
    The helper function is `get_coeff_from_roots`, which efficiently calculates the coefficients of the polynomial
    with roots given by its input. The two main functions will use this helper function to calculate
    the polynomial commitment over a set of curve points via an MSM (multi-scalar multiplication).

*/

/*
    Performs polynomial multiplication using the Fast Fourier Transform (FFT) algorithm.
*/
pub fn fft_mul(left: &[Scalar], right: &[Scalar]) -> Vec<Scalar> {
    let degree_image = left.len() + right.len() - 1;

    // This is the 2^32th root of unity
    const ROOT_OF_UNITY: Scalar = Scalar::ROOT_OF_UNITY;

    // Calculate the smallest n = 2^s such that 2^s >= degree_image
    let s: u32 = degree_image.next_power_of_two().trailing_zeros();
    let n: usize = 1 << s;

    // Calculate the n-th root of unity and its inverse
    let omega = ROOT_OF_UNITY.pow_vartime(&[(1u64 << (32 - s)) as u64]);

    // Clone and resize the vectors
    let mut left = left.to_vec();
    let mut right = right.to_vec();
    left.resize(n, Scalar::ZERO);
    right.resize(n, Scalar::ZERO);

    // Perform FFT on the left and right vectors
    best_fft(&mut left, omega, s);
    best_fft(&mut right, omega, s);

    // Perform point-wise multiplication of the transformed vectors
    let mut result: Vec<Scalar> = left
        .iter()
        .zip(right.iter())
        .map(|(a, b)| *a * *b)
        .collect();

    // Perform inverse FFT
    best_fft(&mut result, omega.invert().unwrap(), s);

    // Normalize the result by dividing by n
    let n_inv = Scalar::from(n as u64).invert().unwrap();
    result.iter_mut().for_each(|x| *x *= n_inv);

    // Remove trailing zeros
    result.truncate(degree_image);

    result
}

/*
    This function calculates the coefficients of the polynomial with roots given by the input `roots`.
    The polynomial is of the form `f(x) = (x - roots[0]) * (x - roots[1]) * ... * (x - roots[n-1])`.
    The function returns the coefficients of the polynomial in the form of a vector.
*/
pub fn get_coeff_from_roots(roots: &[Scalar]) -> Vec<Scalar> {
    let n = roots.len();

    if n == 0 {
        return vec![Scalar::ONE];
    }

    if n == 1 {
        return vec![roots[0], Scalar::ONE];
    }

    let m = n / 2;

    // Spawn parallel tasks for left and right halves (divide and conquer)
    let (left, right) = rayon::join(
        || get_coeff_from_roots(&roots[..m]),
        || get_coeff_from_roots(&roots[m..]),
    );

    // Multiply the coefficients of the left and right halves
    fft_mul(&left, &right)
}

#[no_mangle]
pub extern "C" fn get_poly_commitment_g1(
    return_point: *mut G1Projective,
    scalars_ptr: *const Scalar,
    scalars_len: usize,
    points_ptr: *const G1Projective,
    points_len: usize,
) {
    // Safety block to handle raw pointers
    unsafe {
        // Create slices from the raw pointers
        let scalars: &[Scalar] = std::slice::from_raw_parts(scalars_ptr, scalars_len);
        let points: &[G1Projective] = std::slice::from_raw_parts(points_ptr, points_len);

        // Get the roots polynomial coefficients using the provided scalars
        let roots_poly = get_coeff_from_roots(scalars);

        // Perform MSM (Multi-Scalar Multiplication) with the polynomial coefficients and points
        let commitment = G1Projective::multi_exp(points, &roots_poly);

        // Store the result in the return_point
        *return_point = commitment;
    }
}

#[no_mangle]
pub extern "C" fn get_poly_commitment_g2(
    return_point: *mut G2Projective,
    scalars_ptr: *const Scalar,
    scalars_len: usize,
    points_ptr: *const G2Projective,
    points_len: usize,
) {
    // Safety block to handle raw pointers
    unsafe {
        // Create slices from the raw pointers
        let scalars: &[Scalar] = std::slice::from_raw_parts(scalars_ptr, scalars_len);
        let points: &[G2Projective] = std::slice::from_raw_parts(points_ptr, points_len);

        // Get the roots polynomial coefficients using the provided scalars
        let roots_poly = get_coeff_from_roots(scalars);

        // Perform MSM (Multi-Scalar Multiplication) with the polynomial coefficients and points
        let commitment = G2Projective::multi_exp(points, &roots_poly);

        // Store the result in the return_point
        *return_point = commitment;
    }
}

#[cfg(test)]
mod test_get_poly_commitments {
    use super::*;
    // in this test we will calculate the polynomial commitment a = g1^f(tau) and b = g2^f(tau)
    // of the polynomial f = (x + 1)^5. Then do the pairing check
    //       e(a,g2) = e(g1,b)
    // where e is the bilinear pairing

    #[test]
    fn test_get_coeff_from_roots() {
        const N: usize = 5;
        // This represents the roots of the polynomial (x + 1)^5 = x^5 + 5x^4 + 10x^3 + 10x^2 + 5x + 1
        // which is a polynomial of degree 5 (so it has 6 coefficients)
        let roots = vec![
            Scalar::ONE,
            Scalar::ONE,
            Scalar::ONE,
            Scalar::ONE,
            Scalar::ONE,
        ];
        // Set a value of tau for a trusted setup
        let scalar_tau = Scalar::from_bytes_be(&{
            let mut bytes = [0u8; 32];
            bytes[31] = 10;
            bytes
        })
        .unwrap();

        // Initialize a vector with the "zero't" power of tau (tau^0 = 1)
        let mut scalar_power_of_tau: Vec<Scalar> = vec![Scalar::ONE];

        // Add the powers of tau to the vector if size N+1 (to fit the polynomial coefficients)
        scalar_power_of_tau.extend((0..N).scan(Scalar::ONE, |state, _| {
            // Multiply by tau to get the next power
            *state = *state * scalar_tau;
            // Return the new power of tau
            Some(*state)
        }));

        // Compute the powers of tau over G1
        let g1_setup: Vec<G1Projective> = scalar_power_of_tau
            .iter()
            .map(|x| G1Projective::generator() * x)
            .collect();
        // Compute the powers of tau over G2
        let g2_setup: Vec<G2Projective> = scalar_power_of_tau
            .iter()
            .map(|x| G2Projective::generator() * x)
            .collect();

        // setup a commitment
        let mut g1_commitment = G1Projective::identity();
        let mut g2_commitment = G2Projective::identity();

        // calculate the commitment using the main function for G1
        get_poly_commitment_g1(
            &mut g1_commitment,
            roots.as_ptr(),
            roots.len(),
            g1_setup.as_ptr(),
            g1_setup.len(),
        );

        // calculate the commitment using the main function for G2
        get_poly_commitment_g2(
            &mut g2_commitment,
            roots.as_ptr(),
            roots.len(),
            g2_setup.as_ptr(),
            g2_setup.len(),
        );

        // Perform pairing check
        let g1_affine = G1Affine::from(g1_commitment);
        let g2_affine = G2Affine::from(g2_commitment);
        let g1_gen_affine = G1Affine::generator();
        let g2_gen_affine = G2Affine::generator();

        let pairing_a_g2 = pairing(&g1_affine, &g2_gen_affine); // e(a, g2)
        let pairing_g1_b = pairing(&g1_gen_affine, &g2_affine); // e(g1, b)

        // Check that the pairings are equal
        assert_eq!(pairing_a_g2, pairing_g1_b, "Pairing check failed!");

        println!("Pairing check passed!");
    }
}
