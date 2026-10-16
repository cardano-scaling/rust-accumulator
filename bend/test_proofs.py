#!/usr/bin/env python3
"""Check the laws, then confirm the verifier rejects semantic mutations."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def check(directory, proof="PROOF.bend"):
    return subprocess.run(["bend", str(directory / proof), "--verdict"],
        env={**os.environ, "BEND_NO_TELEMETRY": "1"}, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)


def main():
    for proof in ["PROOF.bend", "karatsuba/PROOF.bend"]:
        baseline = check(ROOT, proof)
        assert baseline.returncode == 0 and "ALL PROOFS CHECK" in baseline.stdout, baseline.stdout
        print(f"PASS: {proof}", flush=True)
    mutations = [
        ("drop inputs from a block", "polynomial.bend", "extend_four(coefficients(tail), r, s, t, u)",
         "extend_pair(coefficients(tail), r, s)"),
        ("reverse the sign", "polynomial.bend", "extend_prepared(xs, F.prepare(r))",
         "extend_prepared(xs, F.prepare(F.sub(F.zero(), r)))"),
        ("bypass validation", "polynomial.bend", "gate(xs, accept(xs, basis_size))", "gate(xs, True{})"),
        ("bypass validation at the API", "library.bend", "P.checked(xs, n)", "Some{P.coefficients(xs)}"),
        ("drop the fused carry", "polynomial.bend", "F.add(F.multiply(r, next), middle)",
         "F.multiply(r, next)"),
        ("drop the four-factor carry", "polynomial.bend", "F.add(F.multiply(r, v3), middle3)",
         "F.multiply(r, v3)"),
        ("bypass candidate API validation", "karatsuba_library.bend", "K.checked(xs, n)",
         "Some{K.coefficients(xs)}"),
        ("omit a convolution leaf term", "karatsuba.bend",
         "F.add(lo2, F.sub(F.sub(mid0, lo0), hi0))", "F.sub(F.sub(mid0, lo0), hi0)"),
        ("truncate an empty convolution leaf", "karatsuba.bend",
         "case Nil{} Nil{}:\n      zeros(7n)", "case Nil{} Nil{}:\n      zeros(6n)"),
        ("use the canonical leaf seed", "karatsuba.bend",
         "case Nil{}:\n      [montgomery_one()]", "case Nil{}:\n      [F.one()]"),
        ("drop a Montgomery leaf factor", "karatsuba.bend",
         "P.extend_four(montgomery_coefficients(tail), r, s, t, u)",
         "P.extend_pair(montgomery_coefficients(tail), r, s)"),
        ("change candidate small-input behavior", "karatsuba.bend",
         "case Size{0n, width}:\n      P.coefficients(xs)", "case Size{0n, width}:\n      []"),
        ("drop the recursive high product", "karatsuba.bend",
         "shift_add(half, z0, shift_add(half, cross(z1, z0, z2), z2))",
         "shift_add(half, z0, shift_add(half, cross(z1, z0, z2), []))"),
        ("omit the second cross-term subtraction", "karatsuba.bend",
         "Con{F.sub(F.sub(a, b), c), cross(as, bs, cs)}",
         "Con{F.sub(a, b), cross(as, bs, cs)}"),
        ("duplicate the left input partition", "karatsuba.bend",
         "right = tree(p, Nat.sub(count, half), drop(xs, half))",
         "right = tree(p, Nat.sub(count, half), take(xs, half))"),
        ("omit the final Montgomery conversion", "karatsuba.bend",
         "from_montgomery(tree(1n+p, P.length(xs), xs))", "tree(1n+p, P.length(xs), xs)"),
        ("drop the leading coefficient", "karatsuba.bend",
         "append(shift_add(left_degree, shift_add(right_degree, multiply(a, b), a), b), [montgomery_one()])",
         "append(shift_add(left_degree, shift_add(right_degree, multiply(a, b), a), b), [])"),
        ("certify the wrong degree count", "karatsuba/bounds.bend",
         "Nat.is_eq(Shape.coefficients_size(n), 1n+n)", "Nat.is_eq(Shape.coefficients_size(n), n)"),
    ]
    for name, filename, before, after in mutations:
        with tempfile.TemporaryDirectory(prefix="accumulator-proof-") as temporary:
            directory = Path(temporary)
            for source in ROOT.rglob("*.bend"):
                if "target" in source.relative_to(ROOT).parts:
                    continue
                destination = directory / source.relative_to(ROOT)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, destination)
            path = directory / filename
            text = path.read_text()
            assert text.count(before) == 1
            path.write_text(text.replace(before, after))
            proof = "karatsuba/PROOF.bend" if filename.startswith("karatsuba") else "PROOF.bend"
            result = check(directory, proof)
            assert result.returncode != 0 and "SOME PROOFS FAIL" in result.stdout, (name, result.stdout)
            # A parser or import failure would not demonstrate the law's strength.
            assert "- expected :" in result.stdout and "- observed :" in result.stdout, result.stdout
            print(f"PASS: verifier rejects '{name}'", flush=True)
    print("PASS: Bend/BendTT structural laws verified; arithmetic/check.py checks numerical equivalence", flush=True)


if __name__ == "__main__":
    main()
