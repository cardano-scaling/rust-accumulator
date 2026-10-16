# Length semantics, independent of scalar values and arithmetic identities.
import Base
import ../scalar.bend as F
import ../polynomial.bend as P
import ../karatsuba.bend as K
import ../LAWS.bend as Original
import ../PROOF.bend as OriginalProof
import ./leaves.bend as Leaves

def append_length(xs: P.Scalars, -ys: P.Scalars)
  -> {P.length(K.append(xs, ys)) == Nat.add(P.length(xs), P.length(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n, P.length(K.append(t, ys)),
        Nat.add(P.length(t), P.length(ys)), append_length(t, ys))

def take_length(xs: P.Scalars, n: Nat)
  -> {P.length(K.take(xs, n)) == Nat.min(P.length(xs), n) : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.take(t, p)),
        Nat.min(P.length(t), p), take_length(t, p))

def drop_length(xs: P.Scalars, n: Nat)
  -> {P.length(K.drop(xs, n)) == Nat.sub(P.length(xs), n) : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      drop_length(t, p)

def zeros_length(n: Nat) -> {P.length(K.zeros(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.zeros(p)), p, zeros_length(p))

def add_length(xs: P.Scalars, ys: P.Scalars)
  -> {P.length(K.add(xs, ys)) == Nat.max(P.length(xs), P.length(ys)) : Nat}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bs}:
      {==}
    case Con{a, as} Nil{}:
      {==}
    case Con{a, as} Con{b, bs}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.add(as, bs)),
        Nat.max(P.length(as), P.length(bs)), add_length(as, bs))

def negate_length(xs: P.Scalars) -> {P.length(K.negate(xs)) == P.length(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.negate(t)), P.length(t), negate_length(t))

def sub_length(xs: P.Scalars, ys: P.Scalars)
  -> {P.length(K.sub(xs, ys)) == Nat.max(P.length(xs), P.length(ys)) : Nat}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bs}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.negate(bs)), P.length(bs), negate_length(bs))
    case Con{a, as} Nil{}:
      {==}
    case Con{a, as} Con{b, bs}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.sub(as, bs)),
        Nat.max(P.length(as), P.length(bs)), sub_length(as, bs))

def cross_size(a: Nat, b: Nat, c: Nat) -> Nat:
  Nat.max(a, Nat.max(b, c))

def cross_length(xs: P.Scalars, ys: P.Scalars, zs: P.Scalars)
  -> {P.length(K.cross(xs, ys, zs)) == cross_size(P.length(xs), P.length(ys), P.length(zs)) : Nat}:
  match xs ys zs:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{c, cs}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.negate(cs)), P.length(cs), negate_length(cs))
    case Nil{} Con{b, bs} Nil{}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.negate(bs)), P.length(bs), negate_length(bs))
    case Nil{} Con{b, bs} Con{c, cs}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.cross([], bs, cs)),
        cross_size(0n, P.length(bs), P.length(cs)), cross_length([], bs, cs))
    case Con{a, as} Nil{} Nil{}:
      {==}
    case Con{a, as} Nil{} Con{c, cs}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.sub(as, cs)),
        Nat.max(P.length(as), P.length(cs)), sub_length(as, cs))
    case Con{a, as} Con{b, bs} Nil{}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.sub(as, bs)),
        Nat.max(P.length(as), P.length(bs)), sub_length(as, bs))
    case Con{a, as} Con{b, bs} Con{c, cs}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.cross(as, bs, cs)),
        cross_size(P.length(as), P.length(bs), P.length(cs)), cross_length(as, bs, cs))

def shift_size(n: Nat, xs: Nat, ys: Nat) -> Nat:
  match n:
    case 0n:
      Nat.max(xs, ys)
    case 1n+p:
      match xs:
        case 0n:
          1n+shift_size(p, 0n, ys)
        case 1n+k:
          1n+shift_size(p, k, ys)

def shift_length(n: Nat, xs: P.Scalars, ys: P.Scalars)
  -> {P.length(K.shift_add(n, xs, ys)) == shift_size(n, P.length(xs), P.length(ys)) : Nat}:
  match n:
    case 0n:
      add_length(xs, ys)
    case 1n+p:
      match xs:
        case Nil{}:
          Equal.cong(Nat, Nat, k => 1n+k, P.length(K.shift_add(p, [], ys)),
            shift_size(p, 0n, P.length(ys)), shift_length(p, [], ys))
        case Con{h, t}:
          Equal.cong(Nat, Nat, k => 1n+k, P.length(K.shift_add(p, t, ys)),
            shift_size(p, P.length(t), P.length(ys)), shift_length(p, t, ys))

def leaf_length(xs: K.Four, ys: K.Four) -> {P.length(K.leaf(xs, ys)) == 7n : Nat}:
  match xs ys:
    case K.Four{a, b, c, d} K.Four{e, f, g, h}:
      {==}

def leaf_lists_length(xs: P.Scalars, ys: P.Scalars)
  -> {P.length(K.leaf_lists(xs, ys)) == 7n : Nat}:
  match xs ys:
    case Nil{} Nil{}:
      zeros_length(7n)
    case Nil{} Con{b, bs}:
      zeros_length(7n)
    case Con{a, as} Nil{}:
      zeros_length(7n)
    case Con{a, as} Con{b, bs}:
      leaf_length(K.four(Con{a, as}), K.four(Con{b, bs}))

def pad_size(+xs: Nat, width: Nat) -> Nat:
  Nat.add(xs, Nat.sub(width, xs))

def pad_length(+xs: P.Scalars, +width: Nat)
  -> {P.length(K.pad(xs, width)) == pad_size(P.length(xs), width) : Nat}:
  %zeros_length(Nat.sub(width, P.length(xs))) : {P.length(K.pad(xs, width)) == Nat.add(P.length(xs), _) : Nat}
  append_length(xs, K.zeros(Nat.sub(width, P.length(xs))))

def recombine_size(+half: Nat, +lo: Nat, mid: Nat, +hi: Nat) -> Nat:
  shift_size(half, lo, shift_size(half, cross_size(mid, lo, hi), hi))

def recombine_length(+half: Nat, +lo: P.Scalars, +mid: P.Scalars, +hi: P.Scalars)
  -> {P.length(K.shift_add(half, lo, K.shift_add(half, K.cross(mid, lo, hi), hi))) == recombine_size(half, P.length(lo), P.length(mid), P.length(hi)) : Nat}:
  %cross_length(mid, lo, hi) : {P.length(K.shift_add(half, lo, K.shift_add(half, K.cross(mid, lo, hi), hi))) == shift_size(half, P.length(lo), shift_size(half, _, P.length(hi))) : Nat}
  %shift_length(half, K.cross(mid, lo, hi), hi) : {P.length(K.shift_add(half, lo, K.shift_add(half, K.cross(mid, lo, hi), hi))) == shift_size(half, P.length(lo), _) : Nat}
  shift_length(half, lo, K.shift_add(half, K.cross(mid, lo, hi), hi))

# An interpreter for lengths only; no scalar computation can affect its result.
def convolution_size(depth: Nat, width: Nat) -> Nat:
  match depth:
    case 0n:
      7n
    case 1n+p:
      +half = Nat.div(width, 2n)
      +child = convolution_size(p, half)
      recombine_size(half, child, child, child)

def convolution_length(depth: Nat, +width: Nat, +xs: P.Scalars, +ys: P.Scalars)
  -> {P.length(K.convolution(depth, width, xs, ys)) == convolution_size(depth, width) : Nat}:
  match depth:
    case 0n:
      leaf_lists_length(xs, ys)
    case 1n++p:
      +half = Nat.div(width, 2n)
      +a0 = K.take(xs, half)
      +a1 = K.drop(xs, half)
      +b0 = K.take(ys, half)
      +b1 = K.drop(ys, half)
      %convolution_length(p, half, a0, b0) : {P.length(K.convolution(1n+p, width, xs, ys)) == recombine_size(half, _, convolution_size(p, half), convolution_size(p, half)) : Nat}
      %convolution_length(p, half, K.add(a0, a1), K.add(b0, b1)) : {P.length(K.convolution(1n+p, width, xs, ys)) == recombine_size(half, P.length(K.convolution(p, half, a0, b0)), _, convolution_size(p, half)) : Nat}
      %convolution_length(p, half, a1, b1) : {P.length(K.convolution(1n+p, width, xs, ys)) == recombine_size(half, P.length(K.convolution(p, half, a0, b0)), P.length(K.convolution(p, half, K.add(a0, a1), K.add(b0, b1))), _) : Nat}
      recombine_length(half, K.convolution(p, half, a0, b0),
        K.convolution(p, half, K.add(a0, a1), K.add(b0, b1)), K.convolution(p, half, a1, b1))

def multiply_sized_size(size: K.Dimensions, +xs: Nat, +ys: Nat) -> Nat:
  match size:
    case K.Size{depth, +width}:
      Nat.min(convolution_size(depth, width),
        Nat.sub(Nat.add(xs, ys), 1n))

def multiply_sized_length(size: K.Dimensions, +xs: P.Scalars, +ys: P.Scalars)
  -> {P.length(K.multiply_sized(size, xs, ys)) == multiply_sized_size(size, P.length(xs), P.length(ys)) : Nat}:
  match size:
    case K.Size{+depth, +width}:
      %convolution_length(depth, width, xs, ys) : {P.length(K.multiply_sized(K.Size{depth, width}, xs, ys)) == Nat.min(_, Nat.sub(Nat.add(P.length(xs), P.length(ys)), 1n)) : Nat}
      take_length(K.convolution(depth, width, xs, ys), Nat.sub(Nat.add(P.length(xs), P.length(ys)), 1n))

def multiply_size(xs: Nat, ys: Nat) -> Nat:
  match xs ys:
    case 0n 0n:
      0n
    case 0n 1n+b:
      0n
    case 1n+a 0n:
      0n
    case 1n++a 1n++b:
      multiply_sized_size(K.dimensions(6n, Nat.max(1n+a, 1n+b)), 1n+a, 1n+b)

def multiply_length(xs: P.Scalars, ys: P.Scalars)
  -> {P.length(K.multiply(xs, ys)) == multiply_size(P.length(xs), P.length(ys)) : Nat}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bs}:
      {==}
    case Con{a, as} Nil{}:
      {==}
    case Con{a, +as} Con{b, +bs}:
      multiply_sized_length(K.dimensions(6n, Nat.max(1n+P.length(as), 1n+P.length(bs))), Con{a, as}, Con{b, bs})

def into_length(xs: P.Scalars)
  -> {P.length(K.into_montgomery(xs)) == P.length(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.into_montgomery(t)), P.length(t), into_length(t))

def from_length(xs: P.Scalars)
  -> {P.length(K.from_montgomery(xs)) == P.length(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, k => 1n+k, P.length(K.from_montgomery(t)), P.length(t), from_length(t))

def monic_size(+m: Nat, +n: Nat, left: Nat, right: Nat) -> Nat:
  +a = Nat.min(left, m)
  +b = Nat.min(right, n)
  Nat.add(shift_size(m, shift_size(n, multiply_size(a, b), a), b), 1n)

def monic_length(+m: Nat, +n: Nat, +left: P.Scalars, +right: P.Scalars)
  -> {P.length(K.monic_product(m, n, left, right)) == monic_size(m, n, P.length(left), P.length(right)) : Nat}:
  +a = K.take(left, m)
  +b = K.take(right, n)
  %take_length(left, m) : {P.length(K.monic_product(m, n, left, right)) == Nat.add(shift_size(m, shift_size(n, multiply_size(_, Nat.min(P.length(right), n)), _), Nat.min(P.length(right), n)), 1n) : Nat}
  %take_length(right, n) : {P.length(K.monic_product(m, n, left, right)) == Nat.add(shift_size(m, shift_size(n, multiply_size(P.length(a), _), P.length(a)), _), 1n) : Nat}
  %multiply_length(a, b) : {P.length(K.monic_product(m, n, left, right)) == Nat.add(shift_size(m, shift_size(n, _, P.length(a)), P.length(b)), 1n) : Nat}
  %shift_length(n, K.multiply(a, b), a) : {P.length(K.monic_product(m, n, left, right)) == Nat.add(shift_size(m, _, P.length(b)), 1n) : Nat}
  %shift_length(m, K.shift_add(n, K.multiply(a, b), a), b) : {P.length(K.monic_product(m, n, left, right)) == Nat.add(_, 1n) : Nat}
  append_length(K.shift_add(m, K.shift_add(n, K.multiply(a, b), a), b), [K.montgomery_one()])

def tree_size(depth: Nat, +count: Nat, +xs: Nat) -> Nat:
  match depth:
    case 0n:
      1n+xs
    case 1n++p:
      +half = Nat.div(count, 2n)
      monic_size(half, Nat.sub(count, half), tree_size(p, half, Nat.min(xs, half)),
        tree_size(p, Nat.sub(count, half), Nat.sub(xs, half)))

def tree_length(depth: Nat, +count: Nat, +xs: P.Scalars)
  -> {P.length(K.tree(depth, count, xs)) == tree_size(depth, count, P.length(xs)) : Nat}:
  match depth:
    case 0n:
      Leaves.coefficients_length(xs)
    case 1n++p:
      +half = Nat.div(count, 2n)
      %take_length(xs, half) : {P.length(K.tree(1n+p, count, xs)) == monic_size(half, Nat.sub(count, half), tree_size(p, half, _), tree_size(p, Nat.sub(count, half), Nat.sub(P.length(xs), half))) : Nat}
      %drop_length(xs, half) : {P.length(K.tree(1n+p, count, xs)) == monic_size(half, Nat.sub(count, half), tree_size(p, half, P.length(K.take(xs, half))), tree_size(p, Nat.sub(count, half), _)) : Nat}
      %tree_length(p, half, K.take(xs, half)) : {P.length(K.tree(1n+p, count, xs)) == monic_size(half, Nat.sub(count, half), _, tree_size(p, Nat.sub(count, half), P.length(K.drop(xs, half)))) : Nat}
      %tree_length(p, Nat.sub(count, half), K.drop(xs, half)) : {P.length(K.tree(1n+p, count, xs)) == monic_size(half, Nat.sub(count, half), P.length(K.tree(p, half, K.take(xs, half))), _) : Nat}
      monic_length(half, Nat.sub(count, half), K.tree(p, half, K.take(xs, half)), K.tree(p, Nat.sub(count, half), K.drop(xs, half)))

def coefficients_sized_size(size: K.Dimensions, +xs: Nat) -> Nat:
  match size:
    case K.Size{0n, width}:
      1n+xs
    case K.Size{1n+p, width}:
      tree_size(1n+p, xs, xs)

def coefficients_sized_length(size: K.Dimensions, +xs: P.Scalars)
  -> {P.length(K.coefficients_sized(size, xs)) == coefficients_sized_size(size, P.length(xs)) : Nat}:
  match size:
    case K.Size{0n, width}:
      Original.no_input_is_dropped(xs)
    case K.Size{1n++p, width}:
      %tree_length(1n+p, P.length(xs), xs) : {P.length(K.from_montgomery(K.tree(1n+p, P.length(xs), xs))) == _ : Nat}
      from_length(K.tree(1n+p, P.length(xs), xs))

def coefficients_size(+count: Nat) -> Nat:
  coefficients_sized_size(K.tree_dimensions(3n, count), count)

def coefficients_length(+xs: P.Scalars)
  -> {P.length(K.coefficients(xs)) == coefficients_size(P.length(xs)) : Nat}:
  coefficients_sized_length(K.tree_dimensions(3n, P.length(xs)), xs)
