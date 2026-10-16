**Bend 2 coefficient-kernel experiment — final report**

Completed: 16 October 2026. Scope: the work, measurements and security review
performed in this repository during the experiment.

**The experiment is complete.** It produced a Bend 2 coefficient implementation
with readable laws, machine-checked arithmetic and polynomial proofs, a native
adapter, differential tests, and measured performance improvements. The final
kernel often outperforms the repository's existing Rust FFT implementation, but
an additional Rust/blstrs hybrid comparator is approximately 4.1–4.5 times faster
than Bend at the sampled nontrivial sizes. The experiment does not establish
cryptographic security assurance equivalent to blst. No production migration was
performed; the existing Rust library remains the default.

**The replacement covers coefficient computation.** For inputs `a[0] … a[n-1]`,
it returns ascending coefficients of `∏(x + a[i])` over the BLS12-381 scalar field.
Inputs are therefore the negated roots. Zero inputs and duplicate factors are
preserved. The polynomial depends on the input multiset, including multiplicity;
it does not authenticate vector order.

The native interface supports 0–256 inputs, encoded as canonical 32-byte
little-endian integers, and requires exactly `n+1` output coefficients and basis
points. It returns explicit statuses and preserves the output buffer on rejection.
It checks the declared basis size, not the validity of actual setup points.
The comparison harness supplies the coefficients to the existing Rust/blstrs
G1/G2 multiscalar multiplication (MSM). Curve arithmetic, pairing operations and
MSM were not replaced. The original raw Rust/blst C interface is unchanged.

The final Bend implementation uses Karatsuba polynomial multiplication; it does
not contain a Bend FFT/NTT implementation. The existing Rust algorithm supplies
the FFT comparison. Linux CPU execution was exercised. GPU execution, macOS
integration and distributed computation were outside the completed work.

**The toolchain and implementation are reproducible from the repository.**
The [flake](flake.nix) and [Nix configuration](nix/configuration.nix) pin Bend
2.0.37, Lean 4.34.1 and mathlib through [flake.lock](flake.lock). The locked
`nixpkgs` Bend package was the older 0.2.37 language, so the required Bend 2 comes
from the upstream Nix flake following this project's nixpkgs. The independent
BendTT checker is built from the kernel bundled with that exact Bend release.
Bend's automatic version telemetry is disabled in the development environment.

The main retained artifacts are:

| Artifact | Purpose |
| --- | --- |
| [scalar.bend](bend/scalar.bend) | Canonical scalar validation and modular arithmetic |
| [polynomial.bend](bend/polynomial.bend) | Original recurrence with fused streaming expansion |
| [karatsuba.bend](bend/karatsuba.bend) | Optimized product tree and convolution |
| [Original laws](bend/LAWS.bend), [Karatsuba laws](bend/karatsuba/LAWS.bend), [arithmetic laws](bend/arithmetic/LAWS.lean) | Readable statements of the checked contract |
| [Bend proofs](bend/PROOF.bend), [Karatsuba proofs](bend/karatsuba/PROOF.bend), [Lean checker](bend/arithmetic/check.py) | Structural and numerical verification |
| [adapter.h](bend/adapter.h), [adapter.c](bend/adapter.c) | Native byte interface and pinned runtime integration |
| [test.py](bend/test.py), [sanitize.py](bend/sanitize.py) | Differential, boundary, concurrency and sanitizer checks |
| [Rust reference](rust_accumulator/examples/bend_reference.rs) | FFT/hybrid comparisons, native timing and commitment checks |
| [Final measurements](bend/benchmarks/cpu-ultra7-258v.json), [experiments](bend/benchmarks/experiments.json) | Timing results, comparison methods and source hashes |

**Several independent changes reduced the Bend runtime cost.** Scalar values
retain eight `U32` limbs at the boundary. Montgomery multiplication uses twelve
radix-2²³ digits in place of seventeen radix-2¹⁵ steps, with bounded native
arithmetic and fused product/reduction steps. Digit processing is straight-line
code, and prepared multipliers are shared across coefficients of each factor.
Polynomial expansion streams four factors through one traversal, avoiding
intermediate polynomial lists while preserving the original operation order.

Above 32 inputs, a balanced product tree uses Karatsuba convolution. The final
implementation retains these additional optimizations:

| Change | Effect |
| --- | --- |
| Nine-product convolution leaf | Replaces sixteen field products for each four-coefficient leaf |
| Omitted leading ones | Avoids multiplying the known monic terms; restores their contribution algebraically |
| Fused shifts and cross subtraction | Avoids zero prefixes and intermediate polynomial lists |
| Unpadded convolution inputs | Avoids allocating and processing redundant input zeros |
| Empty leaf shortcut | Returns seven zeros without field arithmetic when an operand block is empty |
| Direct Montgomery leaves | Starts streaming expansion in Montgomery form, avoiding conversion of every leaf output |
| Empty/singleton native shortcuts | Validates and copies `[1]` or `[input, 1]` without initializing Bend |

All nontrivial polynomial and field arithmetic remains in Bend. The C shortcuts
perform validation and byte copies; their mathematical specifications are proved,
but their C implementations are outside the formal proofs.

Earlier tree cutoffs of 16 and 8 were tested and discarded because they regressed
several smaller sizes. A prototype that pruned entire empty recursive branches
improved a few boundary sizes by about 4–6%, but was neutral or slightly slower
at full sizes and was not integrated into the final proof suite. Earlier compiler
flag trials did not justify replacing portable `clang -O2` with `-O3` or
`-march=native`; those observations were exploratory, separate from the archived
final benchmark. The retained changes have updated proofs and regression checks.

**The final speed comparison includes a stronger Rust baseline.** Measurements
used an Intel Core Ultra 7 258V on Linux x86-64, CPU affinity 0, one coefficient
thread per implementation, and 31 warmed batches. The Rust timing harness
alternates execution order and targets roughly 1 ms per batch, capped at 65,536
calls. Results are median time per call. Inputs are deterministic, full-width
canonical scalars generated with seed `0xacc`.

Each native path accepts canonical bytes, validates the inputs and basis size,
and writes canonical bytes into a caller-owned output buffer. Measurements include
internal allocations and serialization. They exclude Python conversion, process
messaging, library loading and runtime warmup. The separately recorded Python
round trips and timings on existing Rust `Scalar` values are diagnostic results,
not the main comparison.

Selected results, in microseconds:

| Inputs | Bend Karatsuba | Existing Rust FFT | Rust hybrid |
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

The [full result file](bend/benchmarks/cpu-ultra7-258v.json) contains 22 sampled
sizes. Same-run paired comparisons against the previous sixteen-product Bend
library show latency reductions of 10.0% at 64 inputs, 12.7% at 128, 31.6% at 129,
and 12.9% at 256. These percentages use the paired baseline measurements rather
than ratios between separate benchmark runs. Sizes 2–32 keep the original
arithmetic and were effectively unchanged by the final optimization round.

At 256 inputs, Bend takes approximately 20% less time than the existing FFT.
However, sampling uneven sizes exposed near ties or small losses at 160, 192 and
224. Earlier results limited to powers of two gave an incomplete picture. The
empty/singleton results exercise the C shortcuts; their few-nanosecond,
integer-rounded timings do not demonstrate fast Bend arithmetic.

The benchmark-only Rust hybrid uses a monic product tree, nine-product
convolution leaves, a per-node cutoff of 32, and in-place streaming leaves over
blstrs. It uses the same validated byte interface. Its outputs agree with Bend
and the existing FFT on all 352 differential cases, but it has no formal proof
in this experiment. Its roughly 4.1–4.5× advantage at every sampled size of two or
more inputs shows that beating the existing FFT is primarily an algorithm result,
not evidence of superiority over optimized Rust. This comparator was not promoted
to the production library either.

These results establish neither a win on every input or machine nor an end-to-end
commitment speedup. MSM remains unchanged. Cold start, contention, throughput,
other architectures and worst-case timing leakage were not characterized by this
benchmark. The recorded medians are measurements on one host, not statistical
guarantees or a comprehensive performance profile.

**The laws establish substantial but bounded correctness properties.** The
public contract states that empty input produces one, every factor is retained,
the result is monic, coefficients follow the product recurrence, noncanonical
scalars and wrong basis lengths are rejected, and validation preserves accepted
results. The numerical laws additionally describe modular arithmetic, canonical
outputs, representation round trips, exact optimized coefficient encodings and
permutation invariance.

The two proof layers have distinct roles:

- Bend and the independent BendTT kernel check structural recurrence, assembly,
  length and validation proofs. The optimized leaf matches an explicit
  nine-product assembly. A generic Bend cross-term law is conditional on supplied
  algebraic facts.
- Lean checks the concrete scalar arithmetic and numerical polynomial meaning,
  including carries, borrows, radix conversion, Montgomery reduction, the concrete
  cross term and the complete product tree. It proves exact equality between the
  optimized Bend coefficient list and the original Bend recurrence for every
  canonical input list of length 0–256. Agreement with Rust is established by
  differential tests, not by a proof of the Rust implementation.

The build regenerates Lean definitions from the actual Bend scalar and polynomial
sources. The [scalar translator](bend/arithmetic/translate.py),
[polynomial translator](bend/arithmetic/polynomial_translate.py), and their
correspondence with Bend Base operations remain trusted. Rejecting unsupported
syntax and checking mutations help detect mistakes, but do not prove the
translators correct. The axiom audit permits only `propext`, `Classical.choice`
and `Quot.sound`; unfinished proofs and native-evaluation axioms are rejected.
The formal result is not a proof about the final machine code.

**Validation completed successfully for the final implementation.**

| Check | Recorded result |
| --- | --- |
| Bend/BendTT original and Karatsuba proof suites | Passed |
| Lean arithmetic and polynomial suite | 149 theorems passed; axiom audit passed |
| Deliberately corrupted Bend implementations | All 18 mutations rejected by proofs |
| Deliberately corrupted arithmetic/polynomial implementations | All 20 Lean mutations rejected by proofs |
| Native field arithmetic | 3,915 comparisons passed against Python and Rust/blstrs |
| Exhaustive-length polynomial suite | 352 cases passed, including every supported length 0–256 |
| Commitment correspondence | All 352 cases agreed for both G1 and G2 |
| Boundary behavior | Rejection, unchanged output on errors, overlapping buffers and concurrent calls passed |
| Sanitizers | AddressSanitizer, UndefinedBehaviorSanitizer and leak detection passed |
| Host integration | Signal-handler and alternate-stack preservation checks passed |
| Nix | All four proof/native checks passed |
| Rust | `cargo test --locked` passed |

“Every supported length” means test coverage of all 257 lengths, not testing every
possible input value. The universally quantified arithmetic and coefficient
claims come from the proofs. Differential cases also cover zeros, duplicates,
modulus boundaries, cancellation and uneven splits. Sanitizers do not prove
memory safety within the runtime's custom allocator. LeakSanitizer required a run
outside the sandbox because the sandbox blocked its inspection of thread state.

**The safety review found and fixed an integration defect.** Bend's executable
stack initializer installed process-wide SIGSEGV/SIGBUS handlers and changed the
calling thread's alternate signal stack. The adapter now allocates the guarded
evaluation stack without those side effects, and a regression harness checks
preservation of host signal state.

Other runtime constraints remain. Calls entering Bend share a mutex. Runtime
state persists until process exit and depends on the internal generated-C layout
of Bend 2.0.37. Initialization reserves about 10 GiB of virtual address space:
8 GiB for the corpus and 2 GiB for the evaluation stack. Resident consumption was
much smaller in the observed run, but address-space limits still matter.
Allocation and some runtime failures can terminate the host process. C callers
must supply valid readable and writable memory spans even though the adapter
checks null pointers and sizes.

**Security parity with blstrs/blst has not been established.** The upstream Bend
documentation states that the compiler is not fully audited, that backend behavior
can differ from the proved semantics, and that parsing and translation into the
BendTT kernel are unproved. This is an upstream disclosure reviewed during the
experiment, not a completed audit of our pinned release.
[Source: Bend limitations](https://github.com/bendlang/bend#limitations).

blstrs uses blst as its backend. blst is implemented in C and assembly and has an
NCC Group audit history and a formal-verification effort. Those provide assurance
beyond the choice of Rust as a wrapper language; they do not automatically certify
every version, wrapper or application. This experiment did not audit the Rust
stack either. [Sources: blstrs](https://github.com/filecoin-project/blstrs),
[blst status](https://github.com/supranational/blst#status).

There is no constant-time claim for the Bend implementation. In particular,
the adapter's canonicality comparison exits based on input bytes. If the inputs
are confidential, the compiled implementation needs explicit side-channel
analysis. Keeping blstrs for MSM does not establish constant-time execution of
the full application either.

The coefficient proofs do not establish computational binding, hiding,
trusted-setup validity, or resistance to timing and memory-access leakage.
The commitment harness uses public `tau=7` solely as a deterministic test fixture;
it is not a secure setup. Correct coefficients preserve the specified multiset
semantics, including their inability to authenticate input order. These scheme
properties require separate analysis regardless of the implementation language.

**The final recommendation is to retain the result as an experimental backend.**
The earlier suggestion that Bend could become the default was too broad for a
security-critical deployment. Formal coefficient equivalence makes a switch
technically credible within the supported range, but it does not establish equal
security assurance to blst. A production promotion would need independent review
of the specification, translators and native integration, explicit treatment of
secret inputs and failure handling, and integration into the actual commitment
API. A fallback would need an explicit policy for inputs above 256.

The laws separate scalar arithmetic, representation, polynomial assembly and
validation, which helps future changes remain reviewable. Extending the input
limit requires updates to buffer bounds, dimension certificates and tests.
Changing scalar representations or supported Bend syntax also requires translator
and proof changes. The pinned internal compiler ABI and persistent runtime are
additional maintenance costs. For a future effort focused primarily on speed,
the Rust hybrid offers the larger measured opportunity; for proof assurance,
reducing and reviewing the trusted translation and native boundaries is more
valuable than further small benchmark improvements. These are possible follow-up
directions, not unfinished requirements of this completed experiment.

**The recorded checks can be reproduced with the pinned environment.** From the
repository root:

```sh
nix develop
python3 bend/test_proofs.py
python3 bend/arithmetic/check.py --mutations
python3 bend/build.py --algorithm karatsuba
cargo test --manifest-path rust_accumulator/Cargo.toml --locked
cargo build --manifest-path rust_accumulator/Cargo.toml --locked --release --example bend_reference
python3 bend/test.py --library bend/target/karatsuba/libbend_accumulator.so \
  --exhaustive --benchmark --cpu 0 --results bend/target/benchmark-karatsuba.json
python3 bend/sanitize.py --build bend/target/karatsuba
nix build .#checks.x86_64-linux.bend-laws \
  .#checks.x86_64-linux.bend-arithmetic \
  .#checks.x86_64-linux.bend-native \
  .#checks.x86_64-linux.bend-karatsuba-native --no-link
```

Use an allowed CPU ID in place of 0 where necessary. The sanitizer command needs
an environment permitting leak detection. The final benchmark JSON includes
kernel, adapter and harness hashes; they were checked against the working source
when preparing this report. Historical prototype binaries and the previous Bend
baseline were temporary experiment artifacts. Their recorded measurements and
hashes are retained, but rerunning those exact historical A/B comparisons requires
recovering or reconstructing the corresponding baseline. A saved compatible
library can be supplied with `--baseline-library /path/to/library.so`.

This report closes the experiment at its tested and documented state. The retained
deliverable is a formally checked coefficient algorithm with an experimental
native implementation, measured strengths and explicit trust boundaries.
