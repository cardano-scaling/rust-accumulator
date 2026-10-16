# List identities for the actual Karatsuba implementation. No field axioms.
import Base
import ../scalar.bend as F
import ../polynomial.bend as P
import ../karatsuba.bend as K
import ./specification.bend as Spec
import ./leaves.bend as Leaves

# Take exactly n coefficients, padding a short prefix with zeros.
def prefix(n: Nat, xs: P.Scalars) -> P.Scalars:
  match n:
    case 0n:
      []
    case 1n+p:
      match xs:
        case Nil{}:
          Con{F.zero(), prefix(p, [])}
        case Con{h, t}:
          Con{h, prefix(p, t)}

# A specification with explicit prefix construction rather than fused traversal.
def shifted_sum(+n: Nat, +xs: P.Scalars, ys: P.Scalars) -> P.Scalars:
  K.append(prefix(n, xs), K.add(K.drop(xs, n), ys))

def shifted_sum_agrees(n: Nat, xs: P.Scalars, -ys: P.Scalars)
  -> {K.shift_add(n, xs, ys) == shifted_sum(n, xs, ys) : P.Scalars}:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{h, t}:
          {==}
    case 1n+p:
      match xs:
        case Nil{}:
          Equal.cong(P.Scalars, P.Scalars, tail => Con{F.zero(), tail},
            K.shift_add(p, [], ys), shifted_sum(p, [], ys), shifted_sum_agrees(p, [], ys))
        case Con{h, t}:
          Equal.cong(P.Scalars, P.Scalars, tail => Con{h, tail},
            K.shift_add(p, t, ys), shifted_sum(p, t, ys), shifted_sum_agrees(p, t, ys))

def sub_empty(xs: P.Scalars) -> {K.sub(xs, []) == xs : P.Scalars}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def zero_sub(xs: P.Scalars) -> {K.sub([], xs) == K.negate(xs) : P.Scalars}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# Fused subtraction preserves the order of BOTH scalar subtractions.
def cross_agrees(xs: P.Scalars, ys: P.Scalars, zs: P.Scalars)
  -> {K.cross(xs, ys, zs) == K.sub(K.sub(xs, ys), zs) : P.Scalars}:
  match xs ys zs:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{c, cs}:
      {==}
    case Nil{} Con{b, bs} Nil{}:
      {==}
    case Nil{} Con{b, +bs} Con{c, cs}:
      %zero_sub(bs) : {Con{F.sub(F.sub(F.zero(), b), c), K.cross([], bs, cs)} == Con{F.sub(F.sub(F.zero(), b), c), K.sub(_, cs)} : P.Scalars}
      Equal.cong(P.Scalars, P.Scalars, tail => Con{F.sub(F.sub(F.zero(), b), c), tail},
        K.cross([], bs, cs), K.sub(K.sub([], bs), cs), cross_agrees([], bs, cs))
    case Con{a, as} Nil{} Nil{}:
      {==}
    case Con{a, as} Nil{} Con{c, cs}:
      {==}
    case Con{a, as} Con{b, bs} Nil{}:
      Equal.sym(P.Scalars, K.sub(Con{F.sub(a, b), K.sub(as, bs)}, []),
        Con{F.sub(a, b), K.sub(as, bs)}, sub_empty(Con{F.sub(a, b), K.sub(as, bs)}))
    case Con{a, as} Con{b, bs} Con{c, cs}:
      Equal.cong(P.Scalars, P.Scalars, tail => Con{F.sub(F.sub(a, b), c), tail},
        K.cross(as, bs, cs), K.sub(K.sub(as, bs), cs), cross_agrees(as, bs, cs))

# Splitting cannot omit, reorder or duplicate an input.
def split_agrees(xs: P.Scalars, n: Nat)
  -> {K.append(K.take(xs, n), K.drop(xs, n)) == xs : P.Scalars}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      Equal.cong(P.Scalars, P.Scalars, tail => Con{h, tail},
        K.append(K.take(t, p), K.drop(t, p)), t, split_agrees(t, p))

# Explicit two-level Karatsuba assembly; numerical equality is checked in Lean.
def reference_leaf(left: K.Four, right: K.Four) -> P.Scalars:
  Spec.nine(left, right)

def reference_leaf_agrees(left: K.Four, right: K.Four)
  -> {K.leaf(left, right) == reference_leaf(left, right) : P.Scalars}:
  match left right:
    case K.Four{a, b, c, d} K.Four{e, f, g, h}:
      {==}

def reference_leaf_lists(xs: P.Scalars, ys: P.Scalars) -> P.Scalars:
  match xs ys:
    case Nil{} Nil{}:
      K.zeros(7n)
    case Nil{} Con{b, bs}:
      K.zeros(7n)
    case Con{a, as} Nil{}:
      K.zeros(7n)
    case Con{a, as} Con{b, bs}:
      reference_leaf(K.four(Con{a, as}), K.four(Con{b, bs}))

def leaf_lists_agrees(xs: P.Scalars, ys: P.Scalars)
  -> {K.leaf_lists(xs, ys) == reference_leaf_lists(xs, ys) : P.Scalars}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bs}:
      {==}
    case Con{a, as} Nil{}:
      {==}
    case Con{a, as} Con{b, bs}:
      reference_leaf_agrees(K.four(Con{a, as}), K.four(Con{b, bs}))

def recombine(+half: Nat, +low: P.Scalars, middle: P.Scalars, +high: P.Scalars) -> P.Scalars:
  shifted_sum(half, low, shifted_sum(half, K.sub(K.sub(middle, low), high), high))

def recombine_agrees(+half: Nat, +low: P.Scalars, +middle: P.Scalars, +high: P.Scalars)
  -> {K.shift_add(half, low, K.shift_add(half, K.cross(middle, low, high), high)) == recombine(half, low, middle, high) : P.Scalars}:
  %cross_agrees(middle, low, high) : {K.shift_add(half, low, K.shift_add(half, K.cross(middle, low, high), high)) == shifted_sum(half, low, shifted_sum(half, _, high)) : P.Scalars}
  %shifted_sum_agrees(half, K.cross(middle, low, high), high) : {K.shift_add(half, low, K.shift_add(half, K.cross(middle, low, high), high)) == shifted_sum(half, low, _) : P.Scalars}
  shifted_sum_agrees(half, low, K.shift_add(half, K.cross(middle, low, high), high))

# This is the three-product recurrence; ../arithmetic/Convolution.lean proves its polynomial meaning.
# Canonical numerical convolution equality is checked by the Lean build gate.
def recurrence(depth: Nat, +width: Nat, +xs: P.Scalars, +ys: P.Scalars) -> P.Scalars:
  match depth:
    case 0n:
      reference_leaf_lists(xs, ys)
    case 1n++p:
      +half = Nat.div(width, 2n)
      +a0 = K.take(xs, half)
      +a1 = K.drop(xs, half)
      +b0 = K.take(ys, half)
      +b1 = K.drop(ys, half)
      recombine(half, recurrence(p, half, a0, b0),
        recurrence(p, half, K.add(a0, a1), K.add(b0, b1)), recurrence(p, half, a1, b1))

def recurrence_agrees(depth: Nat, +width: Nat, +xs: P.Scalars, +ys: P.Scalars)
  -> {K.convolution(depth, width, xs, ys) == recurrence(depth, width, xs, ys) : P.Scalars}:
  match depth:
    case 0n:
      leaf_lists_agrees(xs, ys)
    case 1n++p:
      +half = Nat.div(width, 2n)
      +a0 = K.take(xs, half)
      +a1 = K.drop(xs, half)
      +b0 = K.take(ys, half)
      +b1 = K.drop(ys, half)
      %recurrence_agrees(p, half, a0, b0) : {K.convolution(1n+p, width, xs, ys) == recombine(half, _, recurrence(p, half, K.add(a0, a1), K.add(b0, b1)), recurrence(p, half, a1, b1)) : P.Scalars}
      %recurrence_agrees(p, half, K.add(a0, a1), K.add(b0, b1)) : {K.convolution(1n+p, width, xs, ys) == recombine(half, K.convolution(p, half, a0, b0), _, recurrence(p, half, a1, b1)) : P.Scalars}
      %recurrence_agrees(p, half, a1, b1) : {K.convolution(1n+p, width, xs, ys) == recombine(half, K.convolution(p, half, a0, b0), K.convolution(p, half, K.add(a0, a1), K.add(b0, b1)), _) : P.Scalars}
      recombine_agrees(half, K.convolution(p, half, a0, b0),
        K.convolution(p, half, K.add(a0, a1), K.add(b0, b1)), K.convolution(p, half, a1, b1))

# Straightforward assembly around the explicit recurrence. These definitions
# intentionally allocate intermediate lists that the native kernel avoids.
def reference_multiply_sized(size: K.Dimensions, +xs: P.Scalars, +ys: P.Scalars) -> P.Scalars:
  match size:
    case K.Size{depth, +width}:
      K.take(recurrence(depth, width, xs, ys),
        Nat.sub(Nat.add(P.length(xs), P.length(ys)), 1n))

def multiply_sized_agrees(size: K.Dimensions, +xs: P.Scalars, +ys: P.Scalars)
  -> {K.multiply_sized(size, xs, ys) == reference_multiply_sized(size, xs, ys) : P.Scalars}:
  match size:
    case K.Size{depth, +width}:
      Equal.cong(P.Scalars, P.Scalars, result => K.take(result, Nat.sub(Nat.add(P.length(xs), P.length(ys)), 1n)),
        K.convolution(depth, width, xs, ys),
        recurrence(depth, width, xs, ys),
        recurrence_agrees(depth, width, xs, ys))

def reference_multiply(xs: P.Scalars, ys: P.Scalars) -> P.Scalars:
  match xs ys:
    case Nil{} Nil{}:
      []
    case Nil{} Con{b, bs}:
      []
    case Con{a, as} Nil{}:
      []
    case Con{a, +as} Con{b, +bs}:
      reference_multiply_sized(K.dimensions(6n, Nat.max(1n+P.length(as), 1n+P.length(bs))), Con{a, as}, Con{b, bs})

def multiply_agrees(xs: P.Scalars, ys: P.Scalars)
  -> {K.multiply(xs, ys) == reference_multiply(xs, ys) : P.Scalars}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bs}:
      {==}
    case Con{a, as} Nil{}:
      {==}
    case Con{a, +as} Con{b, +bs}:
      multiply_sized_agrees(K.dimensions(6n, Nat.max(1n+P.length(as), 1n+P.length(bs))), Con{a, as}, Con{b, bs})

def reference_monic(+m: Nat, +n: Nat, left: P.Scalars, right: P.Scalars) -> P.Scalars:
  +a = K.take(left, m)
  +b = K.take(right, n)
  K.append(shifted_sum(m, shifted_sum(n, reference_multiply(a, b), a), b), [K.montgomery_one()])

def monic_agrees(+m: Nat, +n: Nat, +left: P.Scalars, +right: P.Scalars)
  -> {K.monic_product(m, n, left, right) == reference_monic(m, n, left, right) : P.Scalars}:
  +a = K.take(left, m)
  +b = K.take(right, n)
  %multiply_agrees(a, b) : {K.monic_product(m, n, left, right) == K.append(shifted_sum(m, shifted_sum(n, _, a), b), [K.montgomery_one()]) : P.Scalars}
  %shifted_sum_agrees(n, K.multiply(a, b), a) : {K.monic_product(m, n, left, right) == K.append(shifted_sum(m, _, b), [K.montgomery_one()]) : P.Scalars}
  Equal.cong(P.Scalars, P.Scalars, result => K.append(result, [K.montgomery_one()]),
    K.shift_add(m, K.shift_add(n, K.multiply(a, b), a), b),
    shifted_sum(m, K.shift_add(n, K.multiply(a, b), a), b),
    shifted_sum_agrees(m, K.shift_add(n, K.multiply(a, b), a), b))

def reference_tree(depth: Nat, +count: Nat, +xs: P.Scalars) -> P.Scalars:
  match depth:
    case 0n:
      Leaves.reference(xs)
    case 1n++p:
      +half = Nat.div(count, 2n)
      reference_monic(half, Nat.sub(count, half), reference_tree(p, half, K.take(xs, half)),
        reference_tree(p, Nat.sub(count, half), K.drop(xs, half)))

def tree_agrees(depth: Nat, +count: Nat, +xs: P.Scalars)
  -> {K.tree(depth, count, xs) == reference_tree(depth, count, xs) : P.Scalars}:
  match depth:
    case 0n:
      Leaves.coefficients_agree(xs)
    case 1n++p:
      +half = Nat.div(count, 2n)
      %tree_agrees(p, half, K.take(xs, half)) : {K.tree(1n+p, count, xs) == reference_monic(half, Nat.sub(count, half), _, reference_tree(p, Nat.sub(count, half), K.drop(xs, half))) : P.Scalars}
      %tree_agrees(p, Nat.sub(count, half), K.drop(xs, half)) : {K.tree(1n+p, count, xs) == reference_monic(half, Nat.sub(count, half), K.tree(p, half, K.take(xs, half)), _) : P.Scalars}
      monic_agrees(half, Nat.sub(count, half), K.tree(p, half, K.take(xs, half)), K.tree(p, Nat.sub(count, half), K.drop(xs, half)))

def reference_sized(size: K.Dimensions, +xs: P.Scalars) -> P.Scalars:
  match size:
    case K.Size{0n, width}:
      P.coefficients(xs)
    case K.Size{1n+p, width}:
      K.from_montgomery(reference_tree(1n+p, P.length(xs), xs))

def sized_agrees(size: K.Dimensions, +xs: P.Scalars)
  -> {K.coefficients_sized(size, xs) == reference_sized(size, xs) : P.Scalars}:
  match size:
    case K.Size{0n, width}:
      {==}
    case K.Size{1n+p, width}:
      Equal.cong(P.Scalars, P.Scalars, result => K.from_montgomery(result),
        K.tree(1n+p, P.length(xs), xs), reference_tree(1n+p, P.length(xs), xs), tree_agrees(1n+p, P.length(xs), xs))

def reference_coefficients(+xs: P.Scalars) -> P.Scalars:
  reference_sized(K.tree_dimensions(3n, P.length(xs)), xs)

def coefficients_agree(+xs: P.Scalars)
  -> {K.coefficients(xs) == reference_coefficients(xs) : P.Scalars}:
  sized_agrees(K.tree_dimensions(3n, P.length(xs)), xs)
