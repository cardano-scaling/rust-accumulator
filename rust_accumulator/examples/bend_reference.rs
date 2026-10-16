//! Line-oriented reference for the Bend experiment; the setup below is test-only.
use blstrs::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use ff::Field;
use group::{prime::PrimeCurveAffine, Group};
use rust_accumulator::{get_coeff_from_roots, get_poly_commitment_g1, get_poly_commitment_g2};
use std::io::{self, BufRead, Write};
use std::time::Instant;

type Coefficients = unsafe extern "C" fn(*const u8, usize, usize, *mut u8, usize) -> i32;

// Keep the loaded library alive until process exit: Bend owns a process-lifetime runtime.
struct Native {
    _handle: *mut libc::c_void,
    coefficients: Coefficients,
}

impl Native {
    fn load(path: &std::ffi::OsStr) -> Self {
        use std::os::unix::ffi::OsStrExt;
        let path = std::ffi::CString::new(path.as_bytes()).unwrap();
        // The symbol and signature are the public API declared in bend/adapter.h.
        unsafe {
            let handle = libc::dlopen(path.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL);
            assert!(
                !handle.is_null(),
                "dlopen: {:?}",
                std::ffi::CStr::from_ptr(libc::dlerror())
            );
            let symbol = libc::dlsym(handle, b"bend_coefficients\0".as_ptr().cast());
            assert!(!symbol.is_null(), "missing bend_coefficients");
            Self {
                _handle: handle,
                coefficients: std::mem::transmute::<*mut libc::c_void, Coefficients>(symbol),
            }
        }
    }

    fn coefficients(&self, inputs: &[[u8; 32]], basis: usize, output: &mut [[u8; 32]]) -> i32 {
        // Slices provide the exact readable/writable lengths given to the C API.
        unsafe {
            (self.coefficients)(
                inputs.as_ptr().cast(),
                inputs.len(),
                basis,
                output.as_mut_ptr().cast(),
                output.len(),
            )
        }
    }
}

// Match Bend's public contract, including canonical decoding, validation, byte
// serialization and leaving the caller's buffer untouched on rejection.
fn checked_coefficients(inputs: &[[u8; 32]], basis: usize, output: &mut [[u8; 32]]) -> i32 {
    checked_with(inputs, basis, output, get_coeff_from_roots)
}

fn checked_with(
    inputs: &[[u8; 32]],
    basis: usize,
    output: &mut [[u8; 32]],
    coefficients: fn(&[Scalar]) -> Vec<Scalar>,
) -> i32 {
    if inputs.len() > 256 || output.len() != inputs.len() + 1 || basis > 257 {
        return 2;
    }
    if basis != inputs.len() + 1 {
        return 1;
    }
    let Some(xs) = inputs
        .iter()
        .map(|x| Option::<Scalar>::from(Scalar::from_bytes_le(x)))
        .collect::<Option<Vec<_>>>()
    else {
        return 1;
    };
    for (out, coefficient) in output.iter_mut().zip(coefficients(&xs)) {
        *out = coefficient.to_bytes_le();
    }
    0
}

// Benchmark-only alternative: the same 32-input product-tree cutoff, monic
// leading-term omission and nine-product Karatsuba leaf as Bend. Rust's field
// representation is already Montgomery; ordinary Scalar operations suffice.
fn streaming(xs: &[Scalar]) -> Vec<Scalar> {
    let mut out = Vec::with_capacity(xs.len() + 1);
    out.push(Scalar::ONE);
    for r in xs.iter().rev() {
        let n = out.len();
        out.push(Scalar::ONE);
        for j in (1..n).rev() {
            out[j] = out[j - 1] + out[j] * r;
        }
        out[0] *= r;
    }
    out
}

fn add_slices(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    let mut out = vec![Scalar::ZERO; a.len().max(b.len())];
    for (to, from) in out.iter_mut().zip(a) {
        *to += from;
    }
    for (to, from) in out.iter_mut().zip(b) {
        *to += from;
    }
    out
}

fn two(a: Scalar, b: Scalar, c: Scalar, d: Scalar) -> [Scalar; 3] {
    let lo = a * c;
    let hi = b * d;
    [lo, (a + b) * (c + d) - lo - hi, hi]
}

fn convolution(depth: usize, width: usize, a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    if a.is_empty() || b.is_empty() {
        return vec![Scalar::ZERO; 2 * width - 1];
    }
    if depth == 0 {
        let mut x = [Scalar::ZERO; 4];
        let mut y = [Scalar::ZERO; 4];
        x[..a.len()].copy_from_slice(a);
        y[..b.len()].copy_from_slice(b);
        let lo = two(x[0], x[1], y[0], y[1]);
        let hi = two(x[2], x[3], y[2], y[3]);
        let mid = two(x[0] + x[2], x[1] + x[3], y[0] + y[2], y[1] + y[3]);
        return vec![
            lo[0],
            lo[1],
            lo[2] + mid[0] - lo[0] - hi[0],
            mid[1] - lo[1] - hi[1],
            hi[0] + mid[2] - lo[2] - hi[2],
            hi[1],
            hi[2],
        ];
    }
    let half = width / 2;
    let (a0, a1) = a.split_at(a.len().min(half));
    let (b0, b1) = b.split_at(b.len().min(half));
    let lo = convolution(depth - 1, half, a0, b0);
    let hi = convolution(depth - 1, half, a1, b1);
    let mid = convolution(depth - 1, half, &add_slices(a0, a1), &add_slices(b0, b1));
    let mut out = vec![Scalar::ZERO; 2 * width - 1];
    for i in 0..lo.len() {
        out[i] += lo[i];
        out[i + half] += mid[i] - lo[i] - hi[i];
        out[i + 2 * half] += hi[i];
    }
    out
}

fn hybrid(xs: &[Scalar]) -> Vec<Scalar> {
    if xs.len() <= 32 {
        return streaming(xs);
    }
    let left_degree = xs.len() / 2;
    let right_degree = xs.len() - left_degree;
    let left = hybrid(&xs[..left_degree]);
    let right = hybrid(&xs[left_degree..]);
    let (mut depth, mut width) = (0, 4);
    while width < right_degree {
        depth += 1;
        width *= 2;
    }
    let mut out = convolution(depth, width, &left[..left_degree], &right[..right_degree]);
    out.truncate(xs.len() - 1);
    out.resize(xs.len() + 1, Scalar::ZERO);
    for i in 0..left_degree {
        out[i + right_degree] += left[i];
    }
    for i in 0..right_degree {
        out[i + left_degree] += right[i];
    }
    out[xs.len()] = Scalar::ONE;
    out
}

fn checked_hybrid(inputs: &[[u8; 32]], basis: usize, output: &mut [[u8; 32]]) -> i32 {
    // Give this comparator the same empty/singleton allocation-free paths.
    if inputs.len() <= 1 {
        if output.len() != inputs.len() + 1 || basis > 257 {
            return 2;
        }
        if basis != inputs.len() + 1 {
            return 1;
        }
        if let Some(x) = inputs.first() {
            if bool::from(Scalar::from_bytes_le(x).is_none()) {
                return 1;
            }
            output[0] = *x;
        }
        output[inputs.len()] = Scalar::ONE.to_bytes_le();
        return 0;
    }
    checked_with(inputs, basis, output, hybrid)
}

fn batch_ns(iterations: usize, operation: &mut impl FnMut()) -> u128 {
    let start = Instant::now();
    for _ in 0..iterations {
        operation();
    }
    start.elapsed().as_nanos()
}

fn batch_size(operation: &mut impl FnMut()) -> usize {
    operation();
    let mut iterations = 1;
    while batch_ns(iterations, operation) < 1_000_000 && iterations < 65_536 {
        iterations *= 2;
    }
    iterations
}

fn median(samples: &mut [u128]) -> u128 {
    samples.sort_unstable();
    let middle = samples.len() / 2;
    if samples.len() % 2 == 0 {
        (samples[middle - 1] + samples[middle]) / 2
    } else {
        samples[middle]
    }
}

// Amortize clock overhead and alternate execution order to reduce drift bias.
fn paired_ns(
    repeats: u32,
    mut left: impl FnMut(),
    mut right: impl FnMut(),
) -> (u128, u128, usize, usize) {
    let l = batch_size(&mut left);
    let r = batch_size(&mut right);
    let mut ls = Vec::new();
    let mut rs = Vec::new();
    for sample in 0..repeats {
        let (a, b) = if sample % 2 == 0 {
            (batch_ns(l, &mut left), batch_ns(r, &mut right))
        } else {
            let b = batch_ns(r, &mut right);
            (batch_ns(l, &mut left), b)
        };
        ls.push(a);
        rs.push(b);
    }
    (
        median(&mut ls) / l as u128,
        median(&mut rs) / r as u128,
        l,
        r,
    )
}

fn native_contract(native: &Native) {
    let mut invalid = Scalar::ZERO.to_bytes_le();
    invalid.fill(255);
    for (input, basis, size, status) in [
        (vec![], 1, 1, 0),
        (vec![Scalar::ONE.to_bytes_le()], 2, 2, 0),
        (vec![invalid], 2, 2, 1),
        (vec![Scalar::ONE.to_bytes_le()], 1, 2, 1),
        (vec![], 258, 1, 2),
        (vec![], 1, 0, 2),
        (vec![[0; 32]; 257], 258, 258, 2),
    ] {
        let mut bend = vec![[0xa5; 32]; size];
        let mut rust = bend.clone();
        let mut optimized = bend.clone();
        assert_eq!(native.coefficients(&input, basis, &mut bend), status);
        assert_eq!(checked_coefficients(&input, basis, &mut rust), status);
        assert_eq!(checked_hybrid(&input, basis, &mut optimized), status);
        assert_eq!(bend, rust);
        assert_eq!(bend, optimized);
        if status != 0 {
            assert_eq!(bend, vec![[0xa5; 32]; size]);
        }
    }
}

fn scalar(s: &str) -> Scalar {
    assert_eq!(s.len(), 64);
    let mut bytes = [0; 32];
    for (i, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
    }
    Scalar::from_bytes_le(&bytes).unwrap()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn setup(n: usize) -> (Vec<G1Projective>, Vec<G2Projective>) {
    // Known tau is strictly a deterministic test fixture, never a secure SRS.
    let powers: Vec<_> = (0..=n)
        .scan(Scalar::ONE, |p, _| {
            let value = *p;
            *p *= Scalar::from(7);
            Some(value)
        })
        .collect();
    (
        powers
            .iter()
            .map(|x| G1Projective::generator() * x)
            .collect(),
        powers
            .iter()
            .map(|x| G2Projective::generator() * x)
            .collect(),
    )
}

fn median_ns(repeats: u32, mut operation: impl FnMut()) -> u128 {
    operation();
    let mut samples: Vec<_> = (0..repeats)
        .map(|_| {
            let start = Instant::now();
            operation();
            start.elapsed().as_nanos()
        })
        .collect();
    samples.sort_unstable();
    let middle = samples.len() / 2;
    if samples.len() % 2 == 0 {
        (samples[middle - 1] + samples[middle]) / 2
    } else {
        samples[middle]
    }
}

fn main() {
    let native = std::env::var_os("BEND_LIBRARY").map(|path| Native::load(&path));
    let baseline = std::env::var_os("BEND_BASELINE_LIBRARY").map(|path| Native::load(&path));
    if let Some(native) = &native {
        native_contract(native);
    }
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        let mut words = line.split_whitespace();
        match words.next().expect("command") {
            command @ ("coeff" | "coeff-hybrid") => {
                let xs: Vec<_> = words.map(scalar).collect();
                let coefficients = if command == "coeff-hybrid" {
                    hybrid(&xs)
                } else {
                    get_coeff_from_roots(&xs)
                };
                println!(
                    "{}",
                    coefficients
                        .iter()
                        .map(|x| hex(&x.to_bytes_le()))
                        .collect::<Vec<_>>()
                        .join(" ")
                );
            }
            "field" => {
                let a = scalar(words.next().unwrap());
                let b = scalar(words.next().unwrap());
                println!(
                    "{} {} {}",
                    hex(&(a + b).to_bytes_le()),
                    hex(&(a - b).to_bytes_le()),
                    hex(&(a * b).to_bytes_le())
                );
            }
            "commit" => {
                let n: usize = words.next().unwrap().parse().unwrap();
                let all: Vec<_> = words.map(scalar).collect();
                assert_eq!(all.len(), 2 * n + 1);
                let (xs, coefficients) = all.split_at(n);
                assert_eq!(coefficients, get_coeff_from_roots(xs));
                let (g1, g2) = setup(n);
                let c1 = G1Projective::multi_exp(&g1, coefficients);
                let c2 = G2Projective::multi_exp(&g2, coefficients);
                let mut reference1 = G1Projective::identity();
                let mut reference2 = G2Projective::identity();
                get_poly_commitment_g1(&mut reference1, xs.as_ptr(), n, g1.as_ptr(), n + 1);
                get_poly_commitment_g2(&mut reference2, xs.as_ptr(), n, g2.as_ptr(), n + 1);
                let value = xs
                    .iter()
                    .fold(Scalar::ONE, |a, x| a * (Scalar::from(7) + x));
                assert_eq!(c1, reference1);
                assert_eq!(c2, reference2);
                assert_eq!(c1, G1Projective::generator() * value);
                assert_eq!(c2, G2Projective::generator() * value);
                assert_eq!(
                    pairing(&G1Affine::from(c1), &G2Affine::generator()),
                    pairing(&G1Affine::generator(), &G2Affine::from(c2))
                );
                println!(
                    "{} {}",
                    hex(&G1Affine::from(c1).to_compressed()),
                    hex(&G2Affine::from(c2).to_compressed())
                );
            }
            command @ ("bench-native" | "bench-hybrid") => {
                let checked = if command == "bench-hybrid" {
                    checked_hybrid
                } else {
                    checked_coefficients
                };
                let repeats: u32 = words.next().unwrap().parse().unwrap();
                assert!(repeats > 0);
                let xs: Vec<_> = words.map(scalar).collect();
                let inputs: Vec<_> = xs.iter().map(Scalar::to_bytes_le).collect();
                let expected: Vec<_> = get_coeff_from_roots(&xs)
                    .iter()
                    .map(Scalar::to_bytes_le)
                    .collect();
                let mut bend_out = vec![[0xa5; 32]; xs.len() + 1];
                let mut rust_out = bend_out.clone();
                let native = native
                    .as_ref()
                    .expect("set BEND_LIBRARY for native benchmarks");
                assert_eq!(native.coefficients(&inputs, xs.len() + 1, &mut bend_out), 0);
                assert_eq!(checked(&inputs, xs.len() + 1, &mut rust_out), 0);
                assert_eq!(bend_out, expected);
                assert_eq!(rust_out, expected);
                let (bend_ns, rust_ns, bend_batch, rust_batch) = paired_ns(
                    repeats,
                    || {
                        assert_eq!(
                            native.coefficients(
                                std::hint::black_box(&inputs),
                                xs.len() + 1,
                                std::hint::black_box(&mut bend_out)
                            ),
                            0
                        );
                        std::hint::black_box(&bend_out);
                    },
                    || {
                        assert_eq!(
                            checked(
                                std::hint::black_box(&inputs),
                                xs.len() + 1,
                                std::hint::black_box(&mut rust_out)
                            ),
                            0
                        );
                        std::hint::black_box(&rust_out);
                    },
                );
                let (comparison_ns, baseline_ns, baseline_batch) = if let Some(baseline) =
                    baseline.as_ref().filter(|_| command == "bench-native")
                {
                    let mut output = bend_out.clone();
                    assert_eq!(baseline.coefficients(&inputs, xs.len() + 1, &mut output), 0);
                    assert_eq!(output, expected);
                    let (current, old, _, batch) = paired_ns(
                        repeats,
                        || {
                            assert_eq!(
                                native.coefficients(
                                    std::hint::black_box(&inputs),
                                    xs.len() + 1,
                                    std::hint::black_box(&mut bend_out)
                                ),
                                0
                            );
                            std::hint::black_box(&bend_out);
                        },
                        || {
                            assert_eq!(
                                baseline.coefficients(
                                    std::hint::black_box(&inputs),
                                    xs.len() + 1,
                                    std::hint::black_box(&mut output)
                                ),
                                0
                            );
                            std::hint::black_box(&output);
                        },
                    );
                    (current, old, batch)
                } else {
                    (0, 0, 0)
                };
                println!(
                    "{bend_ns} {rust_ns} {bend_batch} {rust_batch} {comparison_ns} {baseline_ns} {baseline_batch}"
                );
            }
            "bench" => {
                let repeats: u32 = words.next().unwrap().parse().unwrap();
                assert!(repeats > 0);
                let xs: Vec<_> = words.map(scalar).collect();
                let n = xs.len();
                let (g1, g2) = setup(n);
                let coefficients = get_coeff_from_roots(&xs);
                let coefficient_ns = median_ns(repeats, || {
                    std::hint::black_box(get_coeff_from_roots(std::hint::black_box(&xs)));
                });
                let g1_ns = median_ns(repeats, || {
                    std::hint::black_box(G1Projective::multi_exp(&g1, &coefficients));
                });
                let g2_ns = median_ns(repeats, || {
                    std::hint::black_box(G2Projective::multi_exp(&g2, &coefficients));
                });
                println!("{coefficient_ns} {g1_ns} {g2_ns}");
            }
            other => panic!("unknown command {}", other),
        }
        io::stdout().flush().unwrap();
    }
}
