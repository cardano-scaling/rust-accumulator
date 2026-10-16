#!/usr/bin/env python3
"""Check arithmetic and polynomial laws against fresh translations of the actual Bend sources."""
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from translate import ROOT, Translator
from polynomial_translate import generate

HERE = Path(__file__).resolve().parent
MODULES = ('ScalarLaws', 'Montgomery', 'Reduction', 'Field',
    'PolynomialModel', 'ListOperations', 'OriginalPolynomial', 'Convolution',
    'MultiplyPolynomial', 'Representation', 'MontgomeryLeaves', 'MonicProduct', 'ProductTree', 'Validation', 'LAWS')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def check(sources, lean, directory):
    # Only the pinned external dependencies may be inherited. Generated definitions
    # always live in this fresh directory, before dependencies on the search path.
    dependency_path = os.environ.get('LEAN_PATH', '')
    env = {**os.environ, 'LEAN_PATH': os.pathsep.join(filter(None, [str(directory), dependency_path]))}
    (directory / 'ScalarImpl.lean').write_text(Translator().translate(sources['scalar'], sources['karatsuba']))
    generate(directory, sources['polynomial'], sources['karatsuba'])
    for module in MODULES:
        shutil.copyfile(HERE / f'{module}.lean', directory / f'{module}.lean')
    outputs = []
    for module in ('ScalarImpl', 'PolynomialImpl', 'KaratsubaImpl', *MODULES):
        result = subprocess.run([lean, '-o', f'{module}.olean', f'{module}.lean'],
            cwd=directory, env=env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, timeout=180)
        outputs.append(result.stdout)
        if result.returncode:
            return False, ''.join(outputs)
    declarations = []
    for module in MODULES:
        declarations.extend(f'{module}.{name}' for name in
            re.findall(r'^(?:@\[[^\]]+\]\s*)?theorem (\w+)', (HERE / f'{module}.lean').read_text(), re.M))
    audit = '\n'.join([f'import {m}' for m in MODULES] +
        [f'#print axioms {name}' for name in declarations]) + '\n'
    (directory / 'Audit.lean').write_text(audit)
    result = subprocess.run([lean, 'Audit.lean'], cwd=directory, env=env,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if result.returncode:
        return False, result.stdout
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    if {name for name, _ in reports} != set(declarations):
        raise RuntimeError(f'Incomplete axiom audit:\n{result.stdout}')
    for name, dependencies in reports:
        extra = {s.strip() for s in dependencies.split(',') if s.strip()} - ALLOWED_AXIOMS
        if extra:
            raise RuntimeError(f'{name} uses forbidden axioms: {sorted(extra)}')
    return True, f'{len(declarations)} arithmetic and polynomial theorems checked; axiom audit passed.'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default=shutil.which('lean'))
    parser.add_argument('--mutations', action='store_true')
    args = parser.parse_args()
    if not args.lean:
        raise SystemExit('Lean is required; run inside nix develop.')
    lean = str(Path(args.lean).resolve())
    version = subprocess.check_output([lean, '--version'], text=True)
    if 'version 4.34.1' not in version:
        raise SystemExit(f'Expected pinned Lean 4.34.1, got {version.strip()}')
    sources = {name: (ROOT / f'{name}.bend').read_text()
        for name in ('scalar', 'polynomial', 'karatsuba')}
    with tempfile.TemporaryDirectory(prefix='bend-arithmetic-') as tmp:
        ok, output = check(sources, lean, Path(tmp))
        print(output, flush=True)
        if not ok:
            raise SystemExit(1)
    if args.mutations:
        mutants = (
            ('scalar', 'carry', 'U32.is_lt(t, s)', 'U32.is_lt(t, t)'),
            ('scalar', 'borrow', 'U32.is_lt(s, borrow)', 'U32.is_lt(s, s)'),
            ('scalar', 'modulus', 'Fr{1, 4294967295', 'Fr{2, 4294967295'),
            ('scalar', 'validation', 'borrowed(sub_raw(a, modulus()))', 'borrowed(sub_raw(modulus(), a))'),
            ('scalar', 'reduction', 'select(a, value(r), borrowed(r))', 'select(value(r), a, borrowed(r))'),
            ('scalar', 'repacking', 'U32.shln(d11, 29n)', 'U32.shln(d11, 30n)'),
            ('scalar', 'Montgomery digit', 'product(8388096, m)', 'product(8388097, m)'),
            ('scalar', 'conversion constant', 'Fr{3924570556,', 'Fr{3924570557,'),
            ('karatsuba', 'leading one', 'F.Fr{4292651767,', 'F.Fr{4292651766,'),
            ('karatsuba', 'leaf coefficient', 'F.add(lo2, F.sub(F.sub(mid0, lo0), hi0))', 'F.sub(F.sub(mid0, lo0), hi0)'),
            ('karatsuba', 'empty leaf length', 'case Nil{} Nil{}:\n      zeros(7n)',
                'case Nil{} Nil{}:\n      zeros(6n)'),
            ('karatsuba', 'Montgomery leaf seed', 'case Nil{}:\n      [montgomery_one()]',
                'case Nil{}:\n      [F.one()]'),
            ('karatsuba', 'Montgomery leaf factor',
                'P.extend_four(montgomery_coefficients(tail), r, s, t, u)',
                'P.extend_pair(montgomery_coefficients(tail), r, s)'),
            ('karatsuba', 'cross subtraction', 'F.sub(F.sub(a, b), c), cross(as, bs, cs)',
                'F.add(F.sub(a, b), c), cross(as, bs, cs)'),
            ('karatsuba', 'recursive shift', 'shift_add(half, z0, shift_add(half, cross(z1, z0, z2), z2))',
                'shift_add(1n+half, z0, shift_add(half, cross(z1, z0, z2), z2))'),
            ('karatsuba', 'truncation', 'Nat.sub(Nat.add(P.length(xs), P.length(ys)), 1n)',
                'Nat.sub(Nat.add(P.length(xs), P.length(ys)), 2n)'),
            ('karatsuba', 'tree partition', 'drop(xs, half))', 'take(xs, half))'),
            ('karatsuba', 'output conversion', 'from_montgomery(tree(1n+p, P.length(xs), xs))',
                'tree(1n+p, P.length(xs), xs)'),
            ('polynomial', 'factor sign', 'Con{F.add(F.multiply(r, h), previous), extend_tail_prepared(t, r, h)}',
                'Con{F.sub(F.multiply(r, h), previous), extend_tail_prepared(t, r, h)}'),
            ('polynomial', 'basis length', 'Nat.is_eq(basis_size, 1n+length(xs))',
                'Nat.is_eq(basis_size, length(xs))'),
        )
        for module, name, before, after in mutants:
            if sources[module].count(before) != 1:
                raise RuntimeError(f'Mutation {name} no longer matches uniquely')
            mutant = {**sources, module: sources[module].replace(before, after)}
            with tempfile.TemporaryDirectory(prefix='bend-proof-mutant-') as tmp:
                ok, output = check(mutant, lean, Path(tmp))
                if ok or 'error:' not in output:
                    raise RuntimeError(f'Mutation {name} did not fail a proof:\n{output}')
                print(f'Rejected proof mutation: {name}', flush=True)


if __name__ == '__main__':
    main()
