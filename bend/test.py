#!/usr/bin/env python3
"""Differential tests of compiled Bend against Python integers and Rust/blstrs."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import ctypes
import json
import os
from pathlib import Path
import random
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parent
MODULUS = int("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001", 16)


def encoded(x):
    return x.to_bytes(32, "little")


def oracle(inputs):
    coefficients = [1]
    for x in inputs:
        result = [0] * (len(coefficients) + 1)
        for degree, c in enumerate(coefficients):
            result[degree] = (result[degree] + x * c) % MODULUS
            result[degree + 1] = c
        coefficients = result
    return coefficients


class Native:
    def __init__(self, path):
        self.lib = ctypes.CDLL(str(path.resolve()))
        self.lib.bend_coefficients.argtypes = [ctypes.c_void_p, ctypes.c_size_t,
            ctypes.c_size_t, ctypes.c_void_p, ctypes.c_size_t]
        self.lib.bend_coefficients.restype = ctypes.c_int
        self.lib.bend_scalar.argtypes = [ctypes.c_uint, ctypes.c_void_p,
            ctypes.c_void_p, ctypes.c_void_p]
        self.lib.bend_scalar.restype = ctypes.c_int

    def coefficients(self, xs, basis_size=None):
        n = len(xs)
        source = b"".join(map(encoded, xs))
        destination = ctypes.create_string_buffer(b"\xa5" * (32 * (n + 1)), 32 * (n + 1))
        status = self.lib.bend_coefficients(source, n, n + 1 if basis_size is None
            else basis_size, destination, n + 1)
        if status:
            assert destination.raw == b"\xa5" * (32 * (n + 1)), "error modified output"
            return status, []
        return status, [int.from_bytes(destination.raw[i:i+32], "little")
            for i in range(0, len(destination.raw), 32)]

    def field(self, operation, a, b):
        destination = ctypes.create_string_buffer(b"\xa5" * 32, 32)
        status = self.lib.bend_scalar(operation, encoded(a), encoded(b), destination)
        if status:
            assert destination.raw == b"\xa5" * 32
        return status, int.from_bytes(destination.raw, "little")


class Reference:
    def __init__(self, path, library=None, baseline=None):
        env = {**os.environ, "RAYON_NUM_THREADS": "1"}
        # Do not accidentally inherit a different library from a parent shell.
        env.pop("BEND_LIBRARY", None)
        env.pop("BEND_BASELINE_LIBRARY", None)
        if library:
            env["BEND_LIBRARY"] = str(library.resolve())
        if baseline:
            env["BEND_BASELINE_LIBRARY"] = str(baseline.resolve())
        self.process = subprocess.Popen([str(path.resolve())], stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, text=True, env=env)

    def query(self, command, xs=()):
        self.process.stdin.write(command + " " + " ".join(encoded(x).hex() for x in xs) + "\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline().strip()
        assert line, "Rust reference failed"
        return line.split()

    def close(self):
        self.process.stdin.close()
        assert self.process.wait(timeout=10) == 0


def tests(native, reference, exhaustive=False):
    rng = random.Random(0xacc)
    edges = [0, 1, 2, MODULUS - 1, MODULUS - 2, MODULUS // 2,
             2**32 - 1, 2**64, 2**128, 2**254]
    pairs = [(a, b) for a in edges for b in edges]
    # Exercise carries, borrows and reduction in both current and former radices.
    for bit in sorted(set(range(15, 255, 15)) | set(range(16, 255, 16))
                      | set(range(23, 255, 23))):
        limb = 1 << bit
        pairs += [(limb - 1, 1), (0, limb), (MODULUS - 1, limb),
                  (limb - 1, limb + 1), (MODULUS - limb, MODULUS - limb)]
    pairs += [(rng.randrange(MODULUS), rng.randrange(MODULUS)) for _ in range(1000)]
    for a, b in pairs:
        rust = [int.from_bytes(bytes.fromhex(x), "little")
                for x in reference.query("field", [a, b])] if reference else None
        for operation, expected in enumerate([(a+b) % MODULUS, (a-b) % MODULUS,
                                               (a*b) % MODULUS], 1):
            assert native.field(operation, a, b) == (0, expected), (operation, a, b)
            if rust is not None:
                assert rust[operation - 1] == expected
    cases = [[], [0], [1], [MODULUS-1], [1]*5, [0]*5, [1, 2, 3],
             [0, 1, MODULUS-1], edges]
    cases += [[rng.randrange(MODULUS) for _ in range(n)]
              for n in [2, 3, 5, 8, 13, 16] for _ in range(3)]
    cases += [[rng.randrange(MODULUS) for _ in range(n)]
              for n in [31, 32, 33, 63, 64, 65, 127, 128, 129, 253, 254, 255, 256]]
    if exhaustive:
        # Every uneven product-tree split, plus zero and cancellation-heavy
        # inputs around each crossover and near the native size limit.
        cases += [[rng.randrange(MODULUS) for _ in range(n)] for n in range(257)]
        for n in [33, 63, 64, 65, 127, 128, 129, 253, 254, 255, 256]:
            cases += [[0]*n, [1]*n, [MODULUS-1]*n,
                      [1 if i % 2 else MODULUS-1 for i in range(n)],
                      [0 if i % 3 else MODULUS-1 for i in range(n)]]
    for xs in cases:
        status, actual = native.coefficients(xs)
        assert status == 0 and actual == oracle(xs), xs
        if reference:
            rust = [int.from_bytes(bytes.fromhex(x), "little")
                    for x in reference.query("coeff", xs)]
            assert actual == rust
            hybrid = [int.from_bytes(bytes.fromhex(x), "little")
                      for x in reference.query("coeff-hybrid", xs)]
            assert actual == hybrid
        assert native.coefficients(list(reversed(xs))) == (0, actual)
        assert native.coefficients(xs, len(xs))[0] == 1
        assert native.coefficients(xs, len(xs) + 2)[0] == (2 if len(xs) == 256 else 1)
        if reference:
            commitments = reference.query(f"commit {len(xs)}", xs + actual)
            assert list(map(len, commitments)) == [96, 192]
    for bad in [MODULUS, MODULUS + 1, 2**256 - 1]:
        assert native.coefficients([1, bad, 2])[0] == 1
        assert native.coefficients([bad] + [1]*32)[0] == 1
        assert native.coefficients([1]*32 + [bad])[0] == 1
        if exhaustive:
            for position in [0, 127, 255]:
                xs = [1]*256
                xs[position] = bad
                assert native.coefficients(xs)[0] == 1
        for op in [1, 2, 3]:
            assert native.field(op, bad, 1)[0] == 1
    # Empty inputs may use NULL; bad pointers/sizes are rejected before reading.
    out = ctypes.create_string_buffer(b"\xa5" * 64, 64)
    assert native.lib.bend_coefficients(None, 1, 2, out, 2) == 2
    assert native.lib.bend_coefficients(None, 0, 1, None, 1) == 2
    assert native.lib.bend_coefficients(None, 257, 258, out, 258) == 2
    assert native.lib.bend_coefficients(None, 0, 1, out, 0) == 2
    assert out.raw == b"\xa5" * 64
    # The direct empty/singleton paths keep the same validation and aliasing contract.
    for x in edges + [MODULUS, MODULUS + 1, 2**256-1]:
        assert native.coefficients([x], 0)[0] == 1
        assert native.coefficients([x], 3)[0] == 1
        assert native.coefficients([x])[0] == (0 if x < MODULUS else 1)
    for xs in [[], [MODULUS-1], [0, 1, MODULUS-1]]:
        n = len(xs)
        for source_offset, output_offset in [(0, 0), (0, 7), (7, 0)]:
            buffer = ctypes.create_string_buffer(32*(n+1) + 16)
            data = b"".join(map(encoded, xs))
            ctypes.memmove(ctypes.byref(buffer, source_offset), data, len(data))
            status = native.lib.bend_coefficients(ctypes.byref(buffer, source_offset), n, n+1,
                ctypes.byref(buffer, output_offset), n+1)
            assert status == 0
            assert buffer.raw[output_offset:output_offset+32*(n+1)] == b"".join(map(encoded, oracle(xs)))
    bad_alias = ctypes.create_string_buffer(encoded(MODULUS) + b"\xa5"*32, 64)
    unchanged = bad_alias.raw
    assert native.lib.bend_coefficients(bad_alias, 1, 2, bad_alias, 2) == 1
    assert bad_alias.raw == unchanged
    with ThreadPoolExecutor(max_workers=4) as pool:
        assert list(pool.map(native.coefficients, cases[:8])) == [(0, oracle(xs)) for xs in cases[:8]]
    print(f"PASS: {len(pairs)*3} field comparisons; {len(cases)} polynomial cases; rejection and concurrency checks")
    if reference:
        print(f"PASS: Rust FFT/hybrid correspondence and {len(cases)} G1/G2 commitment cases")


def timed(call, repeats):
    assert call()[0] == 0  # Warm the runtime and allocator outside the samples.
    samples = []
    for _ in range(repeats):
        start = time.perf_counter_ns()
        result = call()
        duration = time.perf_counter_ns() - start
        assert result[0] == 0
        samples.append(duration)
    return int(statistics.median(samples))


def benchmark(native, reference, repeats, baseline=None, sizes=None):
    rng = random.Random(0xacc)
    a, b = MODULUS - 1, MODULUS // 3
    microbenchmarks = []
    for name, operation in [("empty", 0), ("add", 1), ("sub", 2), ("mul", 3)]:
        def call(lib):
            return lib.field(operation, a, b) if operation else lib.coefficients([])
        expected = (0, [1]) if not operation else (0, [(a+b) % MODULUS,
            (a-b) % MODULUS, (a*b) % MODULUS][operation - 1])
        assert call(native) == expected
        row = dict(operation=name, python_bend_ns=timed(lambda: call(native), repeats))
        if baseline:
            assert call(baseline) == expected
            row["python_baseline_ns"] = timed(lambda: call(baseline), repeats)
            row["speedup"] = round(row["python_baseline_ns"] / row["python_bend_ns"], 2)
        microbenchmarks.append(row)
        print(json.dumps(row), flush=True)
    results = []
    for n in sizes:
        xs = [rng.randrange(MODULUS) for _ in range(n)]
        assert native.coefficients(xs) == (0, oracle(xs))
        python_duration = timed(lambda: native.coefficients(xs), repeats)
        duration, rust_duration, bend_batch, rust_batch, comparison_duration, baseline_duration, baseline_batch = [
            int(x) for x in reference.query(f"bench-native {repeats}", xs)]
        rust = [int(x) for x in reference.query(f"bench {repeats}", xs)]
        hybrid_bend, hybrid_rust, hybrid_bend_batch, hybrid_rust_batch, *_ = [
            int(x) for x in reference.query(f"bench-hybrid {repeats}", xs)]
        row = dict(inputs=n, bend_coefficients_ns=duration,
                   rust_coefficients_ns=rust_duration,
                   bend_batch=bend_batch, rust_batch=rust_batch,
                   bend_python_ns=python_duration, rust_scalar_coefficients_ns=rust[0],
                   rust_g1_msm_ns=rust[1], rust_g2_msm_ns=rust[2])
        row["bend_over_rust"] = round(duration / rust_duration, 3)
        row.update(rust_hybrid_ns=hybrid_rust, bend_hybrid_comparison_ns=hybrid_bend,
                   hybrid_bend_batch=hybrid_bend_batch, hybrid_rust_batch=hybrid_rust_batch,
                   bend_over_rust_hybrid=round(hybrid_bend / hybrid_rust, 3))
        if baseline:
            assert baseline.coefficients(xs) == (0, oracle(xs))
            row["baseline_coefficients_ns"] = baseline_duration
            row["baseline_batch"] = baseline_batch
            row["bend_baseline_comparison_ns"] = comparison_duration
            row["speedup"] = round(baseline_duration / comparison_duration, 2)
        results.append(row)
        print(json.dumps(row), flush=True)
    return dict(repeats=repeats, statistic="warmed median of native batches", seed="0xacc",
                interface="canonical bytes to caller-owned canonical bytes; validation included",
                timer="Rust Instant; alternating execution order; batches target 1ms, capped at 65536 calls",
                cpu_affinity=sorted(os.sched_getaffinity(0)),
                python_in_native_timings=False,
                coefficient_threads=1, rust_algorithm="existing divide-and-conquer FFT",
                rust_hybrid_algorithm="benchmark-only monic product tree, cutoff 32, nine-product Karatsuba leaves; blstrs",
                microbenchmark_interface="Python ctypes round trip; not a comparison with Rust",
                microbenchmarks=microbenchmarks, coefficients=results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=Path, default=ROOT / "target/libbend_accumulator.so")
    parser.add_argument("--reference", type=Path,
        default=ROOT.parent / "rust_accumulator/target/release/examples/bend_reference")
    parser.add_argument("--benchmark", action="store_true")
    parser.add_argument("--exhaustive", action="store_true",
        help="exercise all 257 supported lengths and cancellation-heavy product trees")
    parser.add_argument("--baseline-library", type=Path,
        help="compare a saved native library on identical inputs (requires --benchmark)")
    parser.add_argument("--no-rust", action="store_true",
        help="check against Python integers only (used by the native Nix package)")
    parser.add_argument("--repeats", type=int, default=31)
    parser.add_argument("--sizes", nargs="+", type=int,
        default=[0, 1, 2, 4, 8, 16, 24, 32, 33, 48, 63, 64, 65, 96, 127, 128, 129, 160, 192, 224, 255, 256],
        help="benchmark lengths (default includes powers of two and uneven splits)")
    parser.add_argument("--cpu", type=int,
        help="pin the test and native reference to one allowed Linux CPU for repeatable timings")
    parser.add_argument("--results", type=Path)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    if any(n < 0 or n > 256 for n in args.sizes):
        parser.error("--sizes must lie between 0 and 256")
    if args.no_rust and args.benchmark:
        parser.error("--benchmark requires the Rust reference")
    if args.baseline_library and not args.benchmark:
        parser.error("--baseline-library requires --benchmark")
    if args.cpu is not None:
        if args.cpu not in os.sched_getaffinity(0):
            parser.error("--cpu must be in the process's allowed CPU set")
        os.sched_setaffinity(0, {args.cpu})
    native = Native(args.library)
    baseline = Native(args.baseline_library) if args.baseline_library else None
    reference = None if args.no_rust else Reference(args.reference,
        args.library if args.benchmark else None, args.baseline_library)
    try:
        tests(native, reference, args.exhaustive)
        if args.benchmark:
            results = benchmark(native, reference, args.repeats, baseline, args.sizes)
            metadata = args.library.resolve().with_name("build.json")
            results["bend_build"] = json.loads(metadata.read_text()) if metadata.exists() else None
            if args.results:
                args.results.write_text(json.dumps(results, indent=2) + "\n")
    finally:
        if reference:
            reference.close()


if __name__ == "__main__":
    main()
