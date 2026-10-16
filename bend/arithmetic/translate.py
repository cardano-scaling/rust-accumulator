#!/usr/bin/env python3
"""Translate the straight-line scalar.bend subset to Lean, failing on unknown syntax.

The translator and the U32/Base correspondence are part of the trusted boundary.
No theorem is assumed by this translation. Every scalar definition is translated;
proofs are checked against fresh output, never a separately maintained model.
"""
import argparse
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PRIMITIVES = {
    'U32.add': 'W.add', 'U32.sub': 'W.sub', 'U32.or': 'W.bor',
    'U32.and': 'W.band', 'U32.is_lt': 'W.lt', 'U32.is_eq': 'W.eq',
    'U32.shln': 'W.shl', 'U32.shrn': 'W.shr',
    'U32.to_nat': 'W.toNat', 'U32.from_nat': 'W.ofNat',
    'Nat.add': 'Nat.add', 'Nat.mul': 'Nat.mul', 'Nat.mod': 'Nat.mod',
    'Nat.div': 'Nat.div',
}
PRELUDE = '''-- Generated from scalar.bend by translate.py. Do not edit.
import Std
set_option linter.unusedVariables false
namespace ScalarImpl
abbrev U32 := BitVec 32
namespace W
def add (a b : U32) : U32 := a + b
def sub (a b : U32) : U32 := a - b
def bor (a b : U32) : U32 := a ||| b
def band (a b : U32) : U32 := a &&& b
def lt (a b : U32) : Bool := decide (a.toNat < b.toNat)
def eq (a b : U32) : Bool := a == b
def shl (a : U32) (n : Nat) : U32 := a <<< n
def shr (a : U32) (n : Nat) : U32 := a >>> n
def toNat (a : U32) : Nat := a.toNat
def ofNat (a : Nat) : U32 := BitVec.ofNat 32 a
end W
'''


class Translator:
    def __init__(self):
        self.names = set(PRIMITIVES) | {'U32', 'Nat', 'Bool'}
        self.constructors = {'True': 'true', 'False': 'false'}

    def expr(self, text, bound):
        toks = re.findall(r'[A-Za-z_][A-Za-z_0-9.]*|[0-9]+n?|[(){},]', text)
        if ''.join(toks) != re.sub(r'\s+', '', text):
            raise ValueError(f'Unsupported expression: {text}')
        pos = 0

        def term():
            nonlocal pos
            name = toks[pos]
            pos += 1
            if re.fullmatch(r'[0-9]+n?', name):
                return name.removesuffix('n')
            if name in self.constructors:
                out = self.constructors[name]
            elif name in PRIMITIVES:
                out = PRIMITIVES[name]
            elif name in bound or name in self.names:
                out = name
            else:
                raise ValueError(f'Unknown name {name}')
            if pos < len(toks) and toks[pos] in ('(', '{'):
                close = ')' if toks[pos] == '(' else '}'
                pos += 1
                args = []
                if toks[pos] != close:
                    args.append(term())
                    while toks[pos] == ',':
                        pos += 1
                        args.append(term())
                if toks[pos] != close:
                    raise ValueError('Unbalanced expression')
                pos += 1
                return '(' + ' '.join([out] + args) + ')' if args else out
            return out

        out = term()
        if pos != len(toks):
            raise ValueError(f'Trailing tokens in {text}')
        return out

    def block(self, lines, bound, level=2):
        out = []
        pad = ' ' * level
        for indent, line in lines:
            # Source indentation carries all block nesting; generated bodies gain two spaces.
            pad = ' ' * indent
            if line.startswith('match '):
                names = line[6:-1].split()
                if not all(n in bound for n in names):
                    raise ValueError('Unknown match variable')
                out.append(pad + 'match ' + ', '.join(names) + ' with')
            elif line.startswith('case '):
                patterns = re.findall(r'([A-Za-z_][A-Za-z_0-9]*)\{([^{}]*)\}', line[5:-1])
                if re.sub(r'\s+', '', line[5:-1]) != ''.join(n + '{' + re.sub(r'\s+', '', a) + '}' for n, a in patterns):
                    raise ValueError('Unsupported pattern')
                pats = []
                for name, fields in patterns:
                    names = [s.strip().lstrip('+') for s in fields.split(',') if s.strip()]
                    if not all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', n) for n in names):
                        raise ValueError('Unsupported pattern field')
                    bound.update(names)
                    pats.append(' '.join([self.constructors[name]] + names))
                out.append(pad + '| ' + ', '.join(pats) + ' =>')
            elif '=' in line:
                name, rhs = line.split('=', 1)
                name = name.strip().lstrip('+')
                if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', name):
                    raise ValueError('Unsupported binding')
                out.append(pad + f'let {name} := {self.expr(rhs, bound)}')
                bound.add(name)
            else:
                out.append(pad + self.expr(line, bound))
        return '\n'.join(out)

    def translate(self, source, karatsuba=None):
        # Join continuation lines only inside balanced argument/constructor lists.
        lines, current, depth, indent = [], '', 0, 0
        for raw in source.splitlines():
            raw = raw.split('#', 1)[0].rstrip()
            if not raw.strip():
                continue
            if not current:
                indent = len(raw) - len(raw.lstrip())
            current += ' ' + raw.strip()
            depth += sum(raw.count(c) for c in '({') - sum(raw.count(c) for c in ')}')
            if depth < 0:
                raise ValueError('Unbalanced source')
            if depth == 0:
                lines.append((indent, current.strip()))
                current = ''
        if current or depth:
            raise ValueError('Incomplete source')
        out, i = [PRELUDE], 0
        while i < len(lines):
            indent, line = lines[i]
            if indent:
                raise ValueError('Unexpected top-level indentation')
            i += 1
            if line == 'import Base':
                continue
            match_type = re.fullmatch(r'type (\w+) is Data:', line)
            if match_type:
                typ = match_type[1]
                constructor = re.fullmatch(r'(\w+)\{(.*)\}', lines[i][1])
                if constructor is None:
                    raise ValueError('Unsupported data declaration')
                name, fields = constructor.groups()
                i += 1
                self.names.add(typ)
                self.constructors[name] = f'{typ}.{name}'
                out.append(f'structure {typ} where\n  {name} ::')
                for field in fields.split(','):
                    n, ty = map(str.strip, field.split(':'))
                    if ty not in self.names:
                        raise ValueError(f'Unknown type {ty}')
                    out.append(f'  {n} : {ty}')
                out.append('  deriving DecidableEq, Repr\n')
                continue
            header = re.fullmatch(r'def (\w+)\((.*)\) -> (\w+):', line)
            if header is None:
                raise ValueError(f'Unsupported declaration: {line}')
            name, params, ret = header.groups()
            self.names.add(name)
            bound, args = set(), []
            for param in params.split(',') if params else []:
                n, ty = map(str.strip, param.split(':'))
                n = n.lstrip('+')
                if ty not in self.names:
                    raise ValueError(f'Unknown type {ty}')
                bound.add(n)
                args.append(f'({n} : {ty})')
            body = []
            while i < len(lines) and lines[i][0] > 0:
                body.append(lines[i])
                i += 1
            out.append(f'def {name} {" ".join(args)} : {ret} :=\n' + self.block(body, bound) + '\n')
        if karatsuba is not None:
            identity = re.search(r'^def montgomery_one\(\) -> F\.Scalar:\n((?:[ \t]+[^\n]*\n)+)', karatsuba, re.M)
            if identity is None:
                raise ValueError('Unsupported Montgomery identity declaration')
            self.constructors['F.Fr'] = 'Scalar.Fr'
            out.append('def montgomery_one : Scalar := ' + self.expr(identity[1], set()) + '\n')
        out.append('end ScalarImpl\n')
        return '\n'.join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=ROOT / 'scalar.bend')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--karatsuba', type=Path, default=ROOT / 'karatsuba.bend')
    args = parser.parse_args()
    args.output.write_text(Translator().translate(args.source.read_text(), args.karatsuba.read_text()))


if __name__ == '__main__':
    main()
