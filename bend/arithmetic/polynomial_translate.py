#!/usr/bin/env python3
"""Fail-closed translation of the list/Nat subset used by the two coefficient kernels."""
from pathlib import Path
import re

from translate import ROOT

TOKEN = re.compile(r'[A-Za-z_][A-Za-z_0-9.]*|[0-9]+n?|&2|\+\+|[+(){}\[\],]')


def tokens(text):
    result = TOKEN.findall(text)
    if ''.join(result) != re.sub(r'\s+', '', text):
        raise ValueError(f'Unsupported syntax: {text}')
    return result


def logical_lines(source):
    lines, current, depth, indent = [], '', 0, 0
    for raw in source.splitlines():
        raw = raw.split('#', 1)[0].rstrip()
        if not raw.strip():
            continue
        if not current:
            indent = len(raw) - len(raw.lstrip())
        current += ' ' + raw.strip()
        depth += sum(raw.count(c) for c in '({[') - sum(raw.count(c) for c in ')}]')
        if depth < 0:
            raise ValueError('Unbalanced source')
        if depth == 0:
            lines.append((indent, current.strip()))
            current = ''
    if current or depth:
        raise ValueError('Incomplete source')
    return lines


class Translator:
    def __init__(self, namespace, polynomial_names=()):
        self.namespace = namespace
        self.names = set()
        self.polynomial_names = set(polynomial_names)
        self.constructors = {'Nil': 'List.nil', 'Con': 'List.cons', 'None': 'Option.none',
            'Some': 'Option.some', 'True': 'true', 'False': 'false',
            'F.Prepared': 'ScalarImpl.Multiplier.Prepared', 'F.Fr': 'ScalarImpl.Scalar.Fr'}
        self.types = {'F.Scalar': 'ScalarImpl.Scalar', 'F.Multiplier': 'ScalarImpl.Multiplier',
            'P.Scalars': 'PolynomialImpl.Scalars', 'Nat': 'Nat', 'Bool': 'Bool'}
        self.scalar_names = set(re.findall(r'^def (\w+)\(', (ROOT / 'scalar.bend').read_text(), re.M))

    def ty(self, source):
        if source in self.types:
            return self.types[source]
        m = re.fullmatch(r'Maybe<&2, (.*)>', source)
        if m:
            return '(Option ' + self.ty(m[1]) + ')'
        raise ValueError(f'Unsupported type {source}')

    def call(self, name, args):
        def application(fn, xs):
            return '(' + ' '.join([fn] + xs) + ')' if xs else fn
        if name in ('List.append', 'List.take', 'List.drop', 'List.length', 'List.get'):
            if args[:2] != ['&2', 'ScalarImpl.Scalar']:
                raise ValueError('Unexpected list representation or element type')
            xs = args[2:]
            if name in ('List.take', 'List.drop'):
                xs = xs[::-1]
            if name == 'List.get':
                return f'({xs[0]}[{xs[1]}]?)'
            return application(name, xs)
        if name == 'List.replicate':
            if args[0] != 'ScalarImpl.Scalar':
                raise ValueError('Unexpected replicated type')
            return application(name, args[1:])
        if name == 'Bool.pick':
            if args[0] not in self.types.values() or len(args) != 4:
                raise ValueError('Unsupported choice')
            return f'(if {args[1]} then {args[2]} else {args[3]})'
        binary = {'Nat.add': '+', 'Nat.sub': '-', 'Nat.div': '/', 'Nat.max': 'max',
            'Bool.and': '&&'}
        if name in binary:
            if len(args) != 2:
                raise ValueError('Wrong primitive arity')
            if name == 'Nat.max':
                return application('max', args)
            return f'({args[0]} {binary[name]} {args[1]})'
        if name in ('Nat.is_lt', 'Nat.is_eq'):
            if len(args) != 2:
                raise ValueError('Wrong comparison arity')
            return f'(decide ({args[0]} {"<" if name == "Nat.is_lt" else "="} {args[1]}))'
        if name == 'Nat.double':
            if len(args) != 1:
                raise ValueError('Wrong double arity')
            return f'(2 * {args[0]})'
        if name.startswith('F.') and name[2:] in self.scalar_names:
            return application('ScalarImpl.' + name[2:], args)
        if name.startswith('P.') and name[2:] in self.polynomial_names:
            return application('PolynomialImpl.' + name[2:], args)
        if name in self.names:
            return application('«' + name + '»', args)
        if name in self.constructors:
            return application(self.constructors[name], args)
        raise ValueError(f'Unsupported call {name}')

    def term(self, toks, bound, pattern=False):
        pos = 0
        def parse():
            nonlocal pos
            name = toks[pos]
            pos += 1
            if name == '+':
                if not pattern:
                    raise ValueError('Unexpected duplicate annotation')
                name = toks[pos]
                pos += 1
            if name == '[':
                args = []
                if toks[pos] != ']':
                    args.append(parse())
                    while toks[pos] == ',':
                        pos += 1
                        args.append(parse())
                if toks[pos] != ']':
                    raise ValueError('Unbalanced list')
                pos += 1
                out = '[' + ', '.join(args) + ']'
            elif re.fullmatch(r'[0-9]+n?', name):
                out = name.removesuffix('n')
            elif name == '&2':
                out = name
            elif pos < len(toks) and toks[pos] in ('(', '{'):
                close = ')' if toks[pos] == '(' else '}'
                pos += 1
                args = []
                if toks[pos] != close:
                    args.append(parse())
                    while toks[pos] == ',':
                        pos += 1
                        args.append(parse())
                if toks[pos] != close:
                    raise ValueError('Unbalanced application')
                pos += 1
                out = self.call(name, args)
            elif name in self.types and not pattern:
                out = self.types[name]
            elif pattern or name in bound:
                bound.add(name)
                out = '«' + name + '»'
            else:
                raise ValueError(f'Unbound name {name}')
            if pos < len(toks) and toks[pos] in ('+', '++'):
                pos += 1
                right = parse()
                if pattern:
                    if out != '1':
                        raise ValueError('Unsupported Nat pattern')
                    out = f'(Nat.succ {right})'
                else:
                    out = f'({out} + {right})'
            return out
        result = parse()
        return result, pos

    def expr(self, source, bound):
        toks = tokens(source)
        result, pos = self.term(toks, bound)
        if pos != len(toks):
            raise ValueError(f'Trailing tokens: {source}')
        return result

    def translate(self, source):
        lines = logical_lines(source)
        imports = ['import ScalarImpl']
        if self.polynomial_names:
            imports.append('import PolynomialImpl')
        out = ['-- Generated from the actual Bend coefficient kernel; do not edit.', *imports,
               'set_option linter.unusedVariables false', f'namespace {self.namespace}']
        i = 0
        while i < len(lines):
            indent, line = lines[i]
            i += 1
            if indent:
                raise ValueError('Unexpected top-level indentation')
            if line in ('import Base', 'import ./scalar.bend as F', 'import ./polynomial.bend as P'):
                continue
            if line == 'def Scalars() -> Data:':
                if lines[i] != (2, 'List<&2, F.Scalar>'):
                    raise ValueError('Unsupported scalar list type')
                i += 1
                self.types['Scalars'] = 'Scalars'
                out.append('abbrev Scalars := List ScalarImpl.Scalar')
                continue
            type_match = re.fullmatch(r'type (\w+) is Data:', line)
            if type_match:
                typ = type_match[1]
                match = re.fullmatch(r'(\w+)\{(.*)\}', lines[i][1])
                if match is None:
                    raise ValueError('Unsupported data declaration')
                i += 1
                name, fields = match.groups()
                self.types[typ] = typ
                self.constructors[name] = f'{typ}.{name}'
                out.append(f'structure {typ} where\n  {name} ::')
                for field in fields.split(','):
                    n, ty = map(str.strip, field.split(':'))
                    out.append(f'  {n} : {self.ty(ty)}')
                out.append('  deriving DecidableEq, Repr')
                continue
            header = re.fullmatch(r'def (\w+)\((.*)\) -> (.*):', line)
            if not header:
                raise ValueError(f'Unsupported declaration {line}')
            name, params, ret = header.groups()
            self.names.add(name)
            args, bound = [], set()
            for arg in params.split(',') if params else []:
                n, ty = map(str.strip, arg.split(':'))
                n = n.lstrip('+')
                bound.add(n)
                args.append(f'(«{n}» : {self.ty(ty)})')
            out.append(f'def «{name}» {" ".join(args)} : {self.ty(ret)} :=')
            while i < len(lines) and lines[i][0]:
                indent, line = lines[i]
                i += 1
                pad = ' ' * indent
                if line.startswith('match '):
                    scrutinees = line[6:-1].split()
                    if not all(n in bound for n in scrutinees):
                        raise ValueError('Unbound match variable')
                    out.append(pad + 'match ' + ', '.join('«' + n + '»' for n in scrutinees) + ' with')
                elif line.startswith('case '):
                    toks, patterns = tokens(line[5:-1]), []
                    while toks:
                        pattern, used = self.term(toks, bound, pattern=True)
                        patterns.append(pattern)
                        toks = toks[used:]
                    out.append(pad + '| ' + ', '.join(patterns) + ' =>')
                elif '=' in line:
                    binding, rhs = map(str.strip, line.split('=', 1))
                    parts = binding.lstrip('+').split(':')
                    n = parts[0].strip()
                    if not re.fullmatch(r'\w+', n) or len(parts) > 2:
                        raise ValueError('Unsupported binding')
                    annotation = ' : ' + self.ty(parts[1].strip()) if len(parts) == 2 else ''
                    expr = self.expr(rhs, bound)
                    bound.add(n)
                    out.append(pad + f'let «{n}»{annotation} := {expr}')
                else:
                    out.append(pad + self.expr(line, bound))
            out.append('')
        out.append(f'end {self.namespace}\n')
        return '\n'.join(out)


def generate(directory, polynomial_source=None, karatsuba_source=None):
    polynomial = Translator('PolynomialImpl')
    (directory / 'PolynomialImpl.lean').write_text(polynomial.translate(polynomial_source if polynomial_source is not None else (ROOT / 'polynomial.bend').read_text()))
    karatsuba = Translator('KaratsubaImpl', polynomial.names)
    (directory / 'KaratsubaImpl.lean').write_text(karatsuba.translate(karatsuba_source if karatsuba_source is not None else (ROOT / 'karatsuba.bend').read_text()))


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    generate(args.output)
