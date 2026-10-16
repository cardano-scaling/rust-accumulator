#!/usr/bin/env python3
"""Build the experimental native adapter with the pinned Bend compiler."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--algorithm", choices=["verified", "karatsuba"], default="verified",
        help="karatsuba selects the product tree, proved equivalent for canonical inputs of length at most 256")
    args = parser.parse_args()
    if args.output is None:
        args.output = ROOT / "target"
        if args.algorithm == "karatsuba":
            args.output /= "karatsuba"
    env = {**os.environ, "BEND_NO_TELEMETRY": "1"}
    version = subprocess.check_output(["bend", "version"], text=True, env=env).strip()
    if version != "bend 2.0.37":
        raise SystemExit(f"adapter requires bend 2.0.37, got {version}")
    subprocess.run(["python3", str(ROOT / "arithmetic" / "check.py")], check=True, env=env)
    args.output.mkdir(parents=True, exist_ok=True)
    generated = args.output.resolve() / "bend_generated.c"
    source = "library.bend" if args.algorithm == "verified" else "karatsuba_library.bend"
    subprocess.run(["bend", str(ROOT / source), "-o", str(generated)],
                   check=True, env=env)
    subprocess.run([
        "clang", "-std=c11", "-O2", "-fPIC", "-fvisibility=hidden", "-shared",
        "-pthread", "-I", str(args.output.resolve()), str(ROOT / "adapter.c"),
        "-lm", "-o", str(args.output / "libbend_accumulator.so"),
    ], check=True, env=env)
    (args.output / "build.json").write_text(json.dumps({
        "compiler": version,
        "algorithm": args.algorithm,
        "full_recurrence_equivalence_proved": True,
        "recurrence_proof_scope": "canonical inputs, at most 256 scalars",
        "modular_arithmetic_correctness_proved": True,
        "arithmetic_proof_checker": "Lean 4.34.1",
        "arithmetic_trusted_boundary": "Bend-to-Lean scalar/list translation and Base primitive correspondence",
        "native_trusted_boundary": "Bend compiler, C adapter including byte-copy fast paths, Clang and Bend runtime",
        "c_flags": "-std=c11 -O2 -fPIC -fvisibility=hidden -shared -pthread",
        "source_sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in ["scalar.bend", "polynomial.bend", "karatsuba.bend", "library.bend",
                         "karatsuba_library.bend", "adapter.c", "adapter.h"]},
    }, indent=2) + "\n")
    print(args.output / "libbend_accumulator.so")


if __name__ == "__main__":
    main()
