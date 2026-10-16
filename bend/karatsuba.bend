# Balanced product tree with Karatsuba convolution over BLS12-381 scalars.
# Full canonical equivalence through 256 inputs: arithmetic/LAWS.lean.
# Internal convolutions use Montgomery form; the public boundary is canonical.
import Base
import ./scalar.bend as F
import ./polynomial.bend as P

def append(xs: P.Scalars, ys: P.Scalars) -> P.Scalars:
  List.append(&2, F.Scalar, xs, ys)

def take(xs: P.Scalars, n: Nat) -> P.Scalars:
  List.take(&2, F.Scalar, xs, n)

def drop(xs: P.Scalars, n: Nat) -> P.Scalars:
  List.drop(&2, F.Scalar, xs, n)

def zeros(n: Nat) -> P.Scalars:
  List.replicate(F.Scalar, n, F.zero())

def add(xs: P.Scalars, ys: P.Scalars) -> P.Scalars:
  match xs ys:
    case Nil{} Nil{}:
      []
    case Nil{} Con{b, bs}:
      Con{b, bs}
    case Con{a, as} Nil{}:
      Con{a, as}
    case Con{a, as} Con{b, bs}:
      Con{F.add(a, b), add(as, bs)}

def negate(xs: P.Scalars) -> P.Scalars:
  match xs:
    case Nil{}:
      []
    case Con{a, as}:
      Con{F.sub(F.zero(), a), negate(as)}

def sub(xs: P.Scalars, ys: P.Scalars) -> P.Scalars:
  match xs ys:
    case Nil{} Nil{}:
      []
    case Nil{} Con{b, bs}:
      Con{F.sub(F.zero(), b), negate(bs)}
    case Con{a, as} Nil{}:
      Con{a, as}
    case Con{a, as} Con{b, bs}:
      Con{F.sub(a, b), sub(as, bs)}

type Four is Data:
  Four{a: F.Scalar, b: F.Scalar, c: F.Scalar, d: F.Scalar}

def unfour(xs: Four) -> P.Scalars:
  match xs:
    case Four{a, b, c, d}:
      [a, b, c, d]

def four(xs: P.Scalars) -> Four:
  match xs:
    case Nil{}:
      Four{F.zero(), F.zero(), F.zero(), F.zero()}
    case Con{a, rest}:
      match rest:
        case Nil{}:
          Four{a, F.zero(), F.zero(), F.zero()}
        case Con{b, rest2}:
          match rest2:
            case Nil{}:
              Four{a, b, F.zero(), F.zero()}
            case Con{c, rest3}:
              match rest3:
                case Nil{}:
                  Four{a, b, c, F.zero()}
                case Con{d, tail}:
                  Four{a, b, c, d}

# Two Karatsuba levels: nine Montgomery products produce seven coefficients.
def leaf(xs: Four, ys: Four) -> P.Scalars:
  match xs ys:
    case Four{+a0, +a1, +a2, +a3} Four{+b0, +b1, +b2, +b3}:
      +lo0 = F.montgomery(a0, b0)
      +lo2 = F.montgomery(a1, b1)
      +lo1 = F.sub(F.sub(F.montgomery(F.add(a0, a1), F.add(b0, b1)), lo0), lo2)
      +hi0 = F.montgomery(a2, b2)
      +hi2 = F.montgomery(a3, b3)
      +hi1 = F.sub(F.sub(F.montgomery(F.add(a2, a3), F.add(b2, b3)), hi0), hi2)
      +a02 = F.add(a0, a2)
      +a13 = F.add(a1, a3)
      +b02 = F.add(b0, b2)
      +b13 = F.add(b1, b3)
      +mid0 = F.montgomery(a02, b02)
      +mid2 = F.montgomery(a13, b13)
      mid1 = F.sub(F.sub(F.montgomery(F.add(a02, a13), F.add(b02, b13)), mid0), mid2)
      [lo0, lo1, F.add(lo2, F.sub(F.sub(mid0, lo0), hi0)),
       F.sub(F.sub(mid1, lo1), hi1), F.add(hi0, F.sub(F.sub(mid2, lo2), hi2)), hi1, hi2]

# Empty blocks have seven zero coefficients at the fixed convolution leaf.
def leaf_lists(xs: P.Scalars, ys: P.Scalars) -> P.Scalars:
  match xs ys:
    case Nil{} Nil{}:
      zeros(7n)
    case Nil{} Con{b, bs}:
      zeros(7n)
    case Con{a, as} Nil{}:
      zeros(7n)
    case Con{a, as} Con{b, bs}:
      leaf(four(Con{a, as}), four(Con{b, bs}))

# Add a shifted row without allocating or adding its zero prefix.
def shift_add(n: Nat, xs: P.Scalars, ys: P.Scalars) -> P.Scalars:
  match n:
    case 0n:
      add(xs, ys)
    case 1n+p:
      match xs:
        case Nil{}:
          Con{F.zero(), shift_add(p, [], ys)}
        case Con{a, as}:
          Con{a, shift_add(p, as, ys)}

def cross(xs: P.Scalars, ys: P.Scalars, zs: P.Scalars) -> P.Scalars:
  match xs ys zs:
    case Nil{} Nil{} Nil{}:
      []
    case Nil{} Nil{} Con{c, cs}:
      Con{F.sub(F.zero(), c), negate(cs)}
    case Nil{} Con{b, bs} Nil{}:
      Con{F.sub(F.zero(), b), negate(bs)}
    case Nil{} Con{b, bs} Con{c, cs}:
      Con{F.sub(F.sub(F.zero(), b), c), cross([], bs, cs)}
    case Con{a, as} Nil{} Nil{}:
      Con{a, as}
    case Con{a, as} Nil{} Con{c, cs}:
      Con{F.sub(a, c), sub(as, cs)}
    case Con{a, as} Con{b, bs} Nil{}:
      Con{F.sub(a, b), sub(as, bs)}
    case Con{a, as} Con{b, bs} Con{c, cs}:
      Con{F.sub(F.sub(a, b), c), cross(as, bs, cs)}

type Dimensions is Data:
  Size{depth: Nat, width: Nat}

def grow(size: Dimensions, needed: Nat) -> Dimensions:
  match size:
    case Size{+depth, +width}:
      Bool.pick(Dimensions, Nat.is_lt(width, needed),
        Size{1n+depth, Nat.double(width)}, Size{depth, width})

# At most 256 coefficients enter a convolution at the native API boundary.
def dimensions(fuel: Nat, +needed: Nat) -> Dimensions:
  match fuel:
    case 0n:
      Size{0n, 4n}
    case 1n+p:
      grow(dimensions(p, needed), needed)

def tree_dimensions(fuel: Nat, +needed: Nat) -> Dimensions:
  match fuel:
    case 0n:
      Size{0n, 32n}
    case 1n+p:
      grow(tree_dimensions(p, needed), needed)

def pad(+xs: P.Scalars, n: Nat) -> P.Scalars:
  append(xs, zeros(Nat.sub(n, P.length(xs))))

# Three half-sized products replace four. z1 is the cross term after subtraction.
def convolution(depth: Nat, +width: Nat, +xs: P.Scalars, +ys: P.Scalars) -> P.Scalars:
  match depth:
    case 0n:
      leaf_lists(xs, ys)
    case 1n++p:
      +half = Nat.div(width, 2n)
      +a0 = take(xs, half)
      +a1 = drop(xs, half)
      +b0 = take(ys, half)
      +b1 = drop(ys, half)
      +z0 = convolution(p, half, a0, b0)
      +z2 = convolution(p, half, a1, b1)
      z1 = convolution(p, half, add(a0, a1), add(b0, b1))
      shift_add(half, z0, shift_add(half, cross(z1, z0, z2), z2))

def multiply_sized(size: Dimensions, +xs: P.Scalars, +ys: P.Scalars) -> P.Scalars:
  match size:
    case Size{depth, +width}:
      take(convolution(depth, width, xs, ys),
        Nat.sub(Nat.add(P.length(xs), P.length(ys)), 1n))

def multiply(+xs: P.Scalars, +ys: P.Scalars) -> P.Scalars:
  match xs ys:
    case Nil{} Nil{}:
      []
    case Nil{} Con{b, bs}:
      []
    case Con{a, as} Nil{}:
      []
    case Con{+a, +as} Con{+b, +bs}:
      multiply_sized(dimensions(6n, Nat.max(1n+P.length(as), 1n+P.length(bs))),
        Con{a, as}, Con{b, bs})

def into_montgomery(xs: P.Scalars) -> P.Scalars:
  match xs:
    case Nil{}:
      []
    case Con{a, tail}:
      Con{F.montgomery(F.r_squared(), a), into_montgomery(tail)}

def from_montgomery(xs: P.Scalars) -> P.Scalars:
  match xs:
    case Nil{}:
      []
    case Con{a, tail}:
      Con{F.montgomery(F.one(), a), from_montgomery(tail)}

# R modulo p, R=2^276; the multiplicative identity in Montgomery form.
def montgomery_one() -> F.Scalar:
  F.Fr{4292651767, 2315528, 4154857737, 2859941150, 1675309076, 1965255524, 503225995, 599249082}

# Start the streaming leaf with R, avoiding a conversion of every output.
def montgomery_coefficients(xs: P.Scalars) -> P.Scalars:
  match xs:
    case Nil{}:
      [montgomery_one()]
    case Con{r, rest}:
      match rest:
        case Nil{}:
          P.extend([montgomery_one()], r)
        case Con{s, rest2}:
          match rest2:
            case Nil{}:
              P.extend_pair([montgomery_one()], r, s)
            case Con{t, rest3}:
              match rest3:
                case Nil{}:
                  P.extend_pair(P.extend([montgomery_one()], t), r, s)
                case Con{u, tail}:
                  P.extend_four(montgomery_coefficients(tail), r, s, t, u)

# Omit the known leading ones from the expensive convolution:
# (x^m+a)(x^n+b) = ab + x^n a + x^m b + x^(m+n).
def monic_product(+left_degree: Nat, +right_degree: Nat, left: P.Scalars, right: P.Scalars) -> P.Scalars:
  +a = take(left, left_degree)
  +b = take(right, right_degree)
  append(shift_add(left_degree, shift_add(right_degree, multiply(a, b), a), b), [montgomery_one()])

# Leaves stream in Montgomery form; splits retain every input.
def tree(depth: Nat, +count: Nat, +xs: P.Scalars) -> P.Scalars:
  match depth:
    case 0n:
      montgomery_coefficients(xs)
    case 1n++p:
      +half = Nat.div(count, 2n)
      left = tree(p, half, take(xs, half))
      right = tree(p, Nat.sub(count, half), drop(xs, half))
      monic_product(half, Nat.sub(count, half), left, right)

def coefficients_sized(size: Dimensions, +xs: P.Scalars) -> P.Scalars:
  match size:
    case Size{0n, width}:
      P.coefficients(xs)
    case Size{1n+p, width}:
      from_montgomery(tree(1n+p, P.length(xs), xs))

def coefficients(+xs: P.Scalars) -> P.Scalars:
  coefficients_sized(tree_dimensions(3n, P.length(xs)), xs)

def gate(xs: P.Scalars, accepted: Bool) -> Maybe<&2, P.Scalars>:
  match accepted:
    case False{}:
      None{}
    case True{}:
      Some{coefficients(xs)}

def checked(+xs: P.Scalars, basis_size: Nat) -> Maybe<&2, P.Scalars>:
  gate(xs, P.accept(xs, basis_size))
