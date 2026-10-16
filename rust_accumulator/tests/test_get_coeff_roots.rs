use blstrs::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use ff::Field;
use group::{prime::PrimeCurveAffine, Group};
use rand::{rngs::StdRng, SeedableRng};
use rust_accumulator::{get_coeff_from_roots, get_poly_commitment_g1, get_poly_commitment_g2};

// Independent quadratic oracle: insert each (x + input) into an ascending
// coefficient array. This replaces the unavailable FLINT test dependency.
fn reference(inputs: &[Scalar]) -> Vec<Scalar> {
    let mut coefficients = vec![Scalar::ONE];
    for input in inputs {
        coefficients.push(Scalar::ZERO);
        for i in (1..coefficients.len()).rev() {
            coefficients[i] = coefficients[i] * input + coefficients[i - 1];
        }
        coefficients[0] *= input;
    }
    coefficients
}

#[test]
fn coefficients_match_independent_product() {
    let mut rng = StdRng::seed_from_u64(0xacc);
    for n in [0, 1, 2, 3, 5, 8, 17, 32, 65, 128] {
        let inputs: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let actual = get_coeff_from_roots(&inputs);
        assert_eq!(actual, reference(&inputs), "input count {n}");
        assert_eq!(actual.len(), n + 1);
        assert_eq!(actual.last(), Some(&Scalar::ONE));
        let mut reversed = inputs.clone();
        reversed.reverse();
        assert_eq!(actual, get_coeff_from_roots(&reversed));
    }
}

#[test]
fn sign_zero_and_multiplicity_are_preserved() {
    for inputs in [
        vec![],
        vec![Scalar::ZERO],
        vec![-Scalar::ONE],
        vec![Scalar::ONE; 5],
        vec![Scalar::ZERO, Scalar::ONE, -Scalar::ONE],
    ] {
        assert_eq!(get_coeff_from_roots(&inputs), reference(&inputs));
    }
    assert_eq!(get_coeff_from_roots(&[Scalar::ONE]), vec![Scalar::ONE; 2]);
    assert_eq!(
        get_coeff_from_roots(&[Scalar::ONE; 2]),
        vec![Scalar::ONE, Scalar::from(2), Scalar::ONE]
    );
}

#[test]
fn both_commitments_equal_direct_polynomial_evaluation() {
    // Public test fixture only: a real setup must not disclose tau.
    let tau = Scalar::from(7);
    let mut rng = StdRng::seed_from_u64(0xc01117);
    for n in [0, 1, 2, 5, 17] {
        let inputs: Vec<_> = (0..n).map(|_| Scalar::random(&mut rng)).collect();
        let value = inputs.iter().fold(Scalar::ONE, |acc, x| acc * (tau + x));
        let powers: Vec<_> = (0..=n)
            .scan(Scalar::ONE, |power, _| {
                let current = *power;
                *power *= tau;
                Some(current)
            })
            .collect();
        let g1: Vec<_> = powers
            .iter()
            .map(|x| G1Projective::generator() * x)
            .collect();
        let g2: Vec<_> = powers
            .iter()
            .map(|x| G2Projective::generator() * x)
            .collect();
        let mut c1 = G1Projective::identity();
        let mut c2 = G2Projective::identity();
        get_poly_commitment_g1(&mut c1, inputs.as_ptr(), n, g1.as_ptr(), n + 1);
        get_poly_commitment_g2(&mut c2, inputs.as_ptr(), n, g2.as_ptr(), n + 1);
        assert_eq!(c1, G1Projective::generator() * value);
        assert_eq!(c2, G2Projective::generator() * value);
        assert_eq!(
            pairing(&G1Affine::from(c1), &G2Affine::generator()),
            pairing(&G1Affine::generator(), &G2Affine::from(c2))
        );
    }
}
