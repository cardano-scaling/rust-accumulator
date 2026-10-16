# rust-accumulator
An optimized rust lib for a POC vector commitment scheme over a BLS based PCS

## Bend 2 experiment

The experiment is complete. The [final report](BEND_EXPERIMENT_REPORT.md) records
the implementation, measurements, proof scope, security findings and final recommendation.

`bend/` contains an experimental coefficient kernel and a native C adapter.
The existing Rust library remains the default implementation. The prototype
computes ascending coefficients of **∏(x + input)** over the BLS12-381 scalar
field, preserving zero inputs and duplicates, then supplies those coefficients
to the existing Rust/blstrs MSM in the comparison harness.

The contract is [bend/LAWS.bend](bend/LAWS.bend). Its seven laws state:

- The empty input produces the polynomial one.
- No input is dropped: n inputs produce n+1 coefficients.
- Each coefficient matches the independent product recurrence.
- The polynomial is monic.
- Noncanonical scalars are rejected.
- A basis with the wrong number of points is rejected.
- Validation preserves the computed coefficients.

[bend/PROOF.bend](bend/PROOF.bend) proves these statements for all inputs, using
structural induction, including equivalence of the fused implementation to the
original recurrence. Both Bend's checker and its independent BendTT kernel
accept the proofs. Regression checks reject dropped inputs, sign changes,
validation bypasses and errors in the fused recurrences.

### What is proved

The Bend proofs cover coefficient assembly and validation at the Bend API entry point.
The [arithmetic and polynomial laws](bend/arithmetic/LAWS.lean) additionally prove validation,
canonical addition, subtraction and multiplication against an integer-modulo-p
specification, Montgomery conversion round trips, the product tree's literal
identity, and the concrete Karatsuba cross-term identity. The supporting proofs
cover every carry and borrow, radix conversion, and all twelve Montgomery steps.
They also prove **exact equality of Karatsuba and original coefficient encodings
for every canonical input list of length 0–256**, including short convolution
inputs, truncation, direct Montgomery leaves, and restoration of omitted leading ones. The checked
entry points agree even on noncanonical scalars and incorrect basis lengths.

These proofs use the pinned Lean 4.34.1 kernel and mathlib from nixpkgs. Every
build regenerates definitions from the actual `scalar.bend`, `polynomial.bend`,
and `karatsuba.bend` sources, then checks the proofs. The fail-closed
[scalar translator](bend/arithmetic/translate.py),
[list translator](bend/arithmetic/polynomial_translate.py), and their mapping of
Bend Base primitives to Lean integers, bit vectors and lists are an explicit
trusted boundary; that correspondence is not itself proved. The axiom audit allows only Lean's standard
`propext`, `Classical.choice` and `Quot.sound`, and rejects unfinished proofs or
native-evaluation axioms. No external solver or additional library axiom is used.

Permutation invariance is now universally proved for supported canonical inputs.
G1/G2 consistency is tested, not universally proved here.
The C adapter, compiler backend, and retained blstrs MSM are outside these proofs.
The empty/singleton byte-copy shortcuts have proved mathematical specifications;
their C implementations are tested, not formally verified.

These are not proofs of computational binding, hiding, trusted-setup validity,
or side-channel resistance. Binding relies on the scheme's cryptographic
assumptions and a suitable setup with undisclosed tau. The comparison harness
uses public tau=7 exclusively as a test fixture. The commitment here is to a
**multiset**; it does not authenticate the order of an input vector.

### Build and check

```sh
nix develop
bend bend/PROOF.bend --verdict
python3 bend/test_proofs.py
python3 bend/arithmetic/check.py --mutations
python3 bend/build.py
cargo test --manifest-path rust_accumulator/Cargo.toml --locked
cargo build --manifest-path rust_accumulator/Cargo.toml --locked --release --example bend_reference
python3 bend/test.py --benchmark --cpu 0 --results bend/target/benchmark.json
```

The Linux flake outputs pin the upstream Bend 2.0.37 Nix package, following this project's
nixpkgs. `pkgs.bend` supplies the older 0.2.37 language without proofs. A separate
nixpkgs revision supplies Lean 4.34.1 and mathlib, and builds the kernel source
**bundled with the exact Bend release**. `BENDTT` selects that kernel; no user-local installation
is needed. The development shell disables Bend's automatic version telemetry.

```sh
nix build .#bend-accumulator
nix build .#checks.x86_64-linux.bend-laws .#checks.x86_64-linux.bend-arithmetic \
  .#checks.x86_64-linux.bend-native
```

These checks run the Bend/BendTT and 149-theorem Lean proof suites, eighteen Bend negative
proof regressions, twenty arithmetic/polynomial mutations, and native
arithmetic/polynomial tests against Python. The command with the Rust
reference additionally checks every coefficient and both G1/G2 commitments.
The suite includes 3,915 field comparisons (including carries and borrows at
15-, 16- and 23-bit boundaries) and 40 polynomial cases, including partial
blocks near the 256-input limit.

### Native interface and limits

[bend/adapter.h](bend/adapter.h) exposes `bend_coefficients`. It accepts canonical
32-byte little-endian integers and returns a status; it does **not** accept raw
`blst_fr` Montgomery representations. Use `Scalar::to_bytes_le` and
`Scalar::from_bytes_le` at the Rust boundary. The original C API is unchanged.

The adapter invokes compiled Bend inside the caller's process, checks basis
length, and leaves the output untouched on rejection. It supports up to 256
inputs, serializes calls entering Bend, and retains its runtime until process exit.
Empty/singleton inputs are validated and copied directly, without runtime
initialization or field arithmetic. Overlapping input/output buffers are supported.
It relies on Bend 2.0.37's internal generated-C layout; upgrades require adapter
review and differential checks. Only the Linux CPU path has been exercised.

The adapter allocates the compiler's guarded evaluation stack without installing
its executable-oriented signal handlers. Host SIGSEGV/SIGBUS handlers and the
caller's alternate signal stack are preserved. The runtime still reserves about
**10 GiB of virtual address space** on first use (8 GiB corpus plus 2 GiB stack);
this is not resident RAM, but matters under address-space limits. Allocation and
runtime failures can terminate the process. There is no constant-time guarantee.

The sanitizer harness checks the generated C and adapter, including rejected
inputs, exact-sized buffers, overlapping buffers, concurrent calls and preservation
of host signal state:

```sh
python3 bend/sanitize.py --build bend/target/karatsuba
```

ASan, UBSan and leak detection pass on Linux. LeakSanitizer needs permission to
inspect thread state; run it outside a sandbox that blocks that inspection.
These checks do not prove memory safety inside Bend's custom allocator.

### CPU performance

The kernel keeps eight `U32` limbs at its scalar boundary and uses twelve
radix-2²³ digits for Montgomery multiplication. Each step fuses product and
reduction using native `Nat` arithmetic; two digit products plus carries fit
below Bend's checked 48-bit native limit. This replaces seventeen radix-2¹⁵
steps. The generated arithmetic has no digit-list allocation or recursive
digit traversal, and each factor's prepared multiplier is shared.

Polynomial expansion streams four factors through one traversal, avoiding
three intermediate polynomial lists per block. One to three remaining factors
use the single/pair routines. The operation order matches the original
recurrence exactly, and new structural proofs establish this equivalence
without changing any of the seven laws or the independent specification.

The benchmark now loads Bend into the Rust reference process. **Both paths
accept canonical bytes, validate inputs and basis size, and write canonical
bytes into a caller-owned buffer.** Timings include each implementation's
internal allocations and serialization. Python conversion, process messaging,
library loading and runtime warmup are outside the native measurements.
Samples alternate execution order and batch calls to amortize clock overhead.

### Experimental Karatsuba path

[bend/karatsuba.bend](bend/karatsuba.bend) adds a balanced product tree above
32 inputs. Polynomial multiplication uses three recursive half-sized products,
with fixed four-coefficient convolution leaves. Each leaf now uses **nine field
products instead of sixteen**. It omits known leading ones, avoids input padding,
skips arithmetic on empty leaf blocks, and fuses shifted additions and cross-term
subtraction. Streaming leaves start directly in Montgomery form; conversion back
to canonical scalars happens at the output. All polynomial and field arithmetic
remains in Bend 2; the adapter only copies the trivial empty/singleton results.

**This path has a machine-checked numerical equivalence proof for all supported
canonical inputs.** It also has separate
[laws](bend/karatsuba/LAWS.bend) and [proofs](bend/karatsuba/PROOF.bend), checked
by Bend and BendTT:

- The empty input produces one, and every supported input length produces n+1 coefficients.
- Splitting preserves every factor in its original order, including uneven splits.
- Noncanonical inputs and incorrect basis sizes are rejected at the entry point;
  acceptance preserves the candidate coefficients.
- Inputs of length at most 32 use the already-proved coefficient kernel.
- Every fixed leaf coefficient matches an explicit nine-product assembly.
  Lean separately proves that assembly equals numerical convolution.
- Fused subtraction, shifted carries, recursive merges and the full product-tree
  assembly agree with an explicit three-product recurrence.
- The cross-term identity follows from explicit algebraic proof inputs.

The degree-count proof in [shape.bend](bend/karatsuba/shape.bend) tracks lengths
through the actual kernel, independently of scalar values. [bounds.bend](bend/karatsuba/bounds.bend)
then checks all 257 supported lengths in the proof kernel, with a proved
composition and selection argument. These are universal proofs over arbitrary
scalar lists, not polynomial test vectors. Small certificates avoid BendTT's
per-definition reduction limit without changing the checker or adding axioms.

[structure.bend](bend/karatsuba/structure.bend) proves that the optimized kernel
preserves the explicit Karatsuba recurrence through final output conversion.
The Lean [product-tree proof](bend/arithmetic/ProductTree.lean) connects that
algorithm to ordinary polynomial multiplication and the original one-factor
recurrence, using the proved concrete scalar operations. It establishes exact
coefficient-list equality, canonical outputs, monicity, validation equivalence
and permutation invariance. The generic Bend cross-term statement remains
conditional; the Lean theorem proves the identity for the actual arithmetic.
The numerical equivalence claim covers canonical inputs within the 256-input
native limit, subject to the translation boundary described above.

Regression proofs reject lost recursive products, incorrect cross terms,
duplicated input partitions, omitted output conversion and lost leading
coefficients, as well as empty-block truncation and incorrect Montgomery leaf
seeds or factors. The original seven laws and their proofs remain unchanged.
The default build still uses the proved original recurrence. The candidate's
Montgomery one is stored as the explicit constant 2^276 mod p, avoiding costly
closed arithmetic during structural proof normalization; its value and identity
law are now proved in the arithmetic suite. No runtime proof
checks or reference recomputation have been added to the fast path.

```sh
nix develop
bend bend/karatsuba/PROOF.bend --verdict
python3 bend/build.py --algorithm karatsuba
cargo build --manifest-path rust_accumulator/Cargo.toml --locked --release --example bend_reference
python3 bend/test.py --library bend/target/karatsuba/libbend_accumulator.so \
  --exhaustive --benchmark --cpu 0 --results bend/target/benchmark-karatsuba.json
nix build .#bend-accumulator-karatsuba .#checks.x86_64-linux.bend-karatsuba-native
```

The candidate has its own output directory and Nix package. Build and benchmark
JSON identify the algorithm and proof scope. The exhaustive suite passes
3,915 field comparisons and 352 polynomial cases, covering every supported
length from 0 through 256, uneven splits, zeros, duplicates and cancellation.
The Rust reference also agrees on every coefficient and both G1/G2 commitments.

On an Intel Core Ultra 7 258V, Linux x86-64, **31 warmed batches, median per
call**, identical deterministic full-width inputs, one coefficient-computation
thread each, both pinned to CPU 0:

| Inputs | Bend (µs) | Existing Rust FFT (µs) | Rust hybrid (µs) |
| ---: | ---: | ---: | ---: |
| 0 | 0.002 | 0.022 | 0.010 |
| 1 | 0.002 | 0.067 | 0.031 |
| 2 | 0.604 | 19.611 | 0.148 |
| 8 | 4.148 | 50.981 | 0.976 |
| 32 | 46.092 | 194.928 | 11.449 |
| 33 | 68.572 | 200.092 | 15.688 |
| 64 | 150.416 | 408.517 | 35.982 |
| 65 | 231.927 | 414.918 | 55.168 |
| 128 | 470.487 | 877.243 | 112.822 |
| 129 | 758.163 | 881.813 | 177.444 |
| 160 | 1057.200 | 1028.722 | 257.260 |
| 192 | 1205.295 | 1173.708 | 289.262 |
| 224 | 1360.409 | 1345.243 | 326.586 |
| 256 | 1504.143 | 1891.387 | 354.844 |

[Full measurements](bend/benchmarks/cpu-ultra7-258v.json) include all 22 sampled
sizes, source hashes and same-run comparisons with the previous sixteen-product
Bend library. The new kernel takes about **13% less time at 256 inputs**, **13%
less at 128**, and **32% less at 129** in those paired comparisons. Sizes 2–32
retain the original arithmetic and are effectively unchanged. Empty/singleton
results now use the C byte-copy shortcut; their few-nanosecond, integer-rounded
batch timings say little about Bend arithmetic performance.

The broader sample exposes near ties or small losses against the existing FFT
at 160, 192 and 224 inputs. At 256, Bend takes about 20% less time than that FFT.
There is no across-the-board win.

For a stronger comparison, the benchmark-only
[Rust hybrid](rust_accumulator/examples/bend_reference.rs) uses a monic product
tree, nine-product convolution leaves, per-node cutoff 32, and in-place streaming
leaves over blstrs. It receives the same validated byte interface and caller-owned
output buffer. It agrees with both Bend and the existing FFT on all 352 differential
cases, but has no formal proof here. **This Rust hybrid is approximately 4.1–4.5×
faster than Bend at every sampled nontrivial size.** The improvement over the
existing FFT is primarily an algorithm comparison, not evidence that Bend
outperforms optimized Rust.

[Experiment results](bend/benchmarks/experiments.json) record the additional
trials. Removing padding, skipping empty leaf arithmetic, and generating
Montgomery leaves directly were retained. Moving the product-tree cutoff to
16 or 8 regressed several smaller sizes. Pruning entire empty recursive branches
helped a few boundary sizes by 4–6%, but was neutral or slightly slower at full
sizes and was not retained. The compiler remains at portable `clang -O2`.

For comparison against a saved library, pass
`--baseline-library /path/to/previous/libbend_accumulator.so` to
`bend/test.py --benchmark`. The default sample includes powers of two and uneven sizes through 256;
`--sizes 0 1 33 65 129 192 256` selects another sample. JSON results include
native coefficient timings, batch sizes, ratios and same-run baseline speedups.
Python arithmetic round trips and Rust timings on existing `Scalar` values,
including MSM, are separately labelled diagnostic measurements. MSM still
uses the same Rust/blstrs implementation on both paths.
The build uses portable `clang -O2`, without CPU-specific instruction flags.
There is no parallel GPU implementation or constant-time guarantee, and Rust
remains the default.


### Replacement assessment

**Speed:** the coefficient kernel improves substantially on its earlier Bend
version and often beats the existing FFT. An optimized Rust algorithm remains
about four times faster. MSM is still Rust/blstrs and unchanged, so coefficient
speedups are not end-to-end commitment speedups. Cold start, contention, other
machines and adversarial timing behavior are not covered by these latency numbers.

**Correctness:** exact arithmetic and coefficient equivalence are kernel-checked
for all canonical inputs through 256, with readable public laws, mutation checks
and exhaustive-length differential tests. Proof coverage is stronger than the
existing Rust coefficient implementation's test-only assurance. It is not an
end-to-end machine-code or cryptographic security proof: the source translators,
Base correspondence, compilers, native adapter and MSM remain trusted.

**Safety:** the adapter bounds sizes, rejects noncanonical encodings and incorrect
basis lengths, preserves output on rejection, supports overlap, and now preserves
host signal state. Sanitizers and concurrent-call tests pass. C callers must still
provide valid memory spans; calls entering Bend share a mutex, the runtime lives
for the process lifetime and reserves substantial virtual address space, and
constant-time execution is unproved. The multiset, setup and binding limitations
above apply regardless of implementation language.

**Extensibility:** the laws separate scalar arithmetic, representation, polynomial
assembly and validation, making optimization regressions checkable. Extending
past 256 inputs requires updating buffer bounds, dimension certificates and tests.
Changing representations or supported Bend syntax also requires translator and
proof work. The adapter's dependency on a pinned internal compiler ABI is a
maintenance cost. This remains a verified coefficient prototype, not a complete
drop-in replacement for the original commitment library; Rust remains the default.
