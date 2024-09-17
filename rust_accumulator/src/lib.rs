use blstrs::{G1Projective, G2Projective, Scalar};
use ff::{Field, PrimeField};
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

    if n == 1 {
        return vec![roots[0], Scalar::ONE];
    }

    let m = n / 2;

    // Spawn parallel tasks for left and right halves
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
    scalars_ptr: *mut Scalar,
    scalars_len: usize,
    points_ptr: *mut G1Projective,
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
    scalars_ptr: *mut Scalar,
    scalars_len: usize,
    points_ptr: *mut G2Projective,
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
