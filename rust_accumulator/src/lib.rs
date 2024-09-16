use blstrs::{G1Projective, G2Projective, Scalar};
// use ff::Field;

#[no_mangle]
pub extern "C" fn get_poly_commitment_g1(
    return_point: *mut G1Projective,
    scalars_ptr: *mut Scalar,
    len: usize,
    points_ptr: *mut G1Projective,
    points_len: usize,
) {
    println!("Hello from Rust G1");
}

#[no_mangle]
pub extern "C" fn get_poly_commitment_g2(
    return_point: *mut G2Projective,
    scalars_ptr: *mut Scalar,
    len: usize,
    points_ptr: *mut G2Projective,
    points_len: usize,
) {
    println!("Hello from Rust G2");
}
