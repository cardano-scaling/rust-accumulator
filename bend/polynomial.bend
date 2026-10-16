# Ascending coefficients of product (x + input). Duplicates are retained.
import Base
import ./scalar.bend as F

def Scalars() -> Data:
  List<&2, F.Scalar>

def length(xs: Scalars) -> Nat:
  List.length(&2, F.Scalar, xs)

def at(xs: Scalars, k: Nat) -> Maybe<&2, F.Scalar>:
  List.get(&2, F.Scalar, xs, k)

# Keep the prepared multiplier shared across all coefficients of this factor.
def extend_tail_prepared(xs: Scalars, +r: F.Multiplier, previous: F.Scalar) -> Scalars:
  match xs:
    case Nil{}:
      [previous]
    case Con{+h, t}:
      Con{F.add(F.multiply(r, h), previous), extend_tail_prepared(t, r, h)}

def extend_prepared(xs: Scalars, +r: F.Multiplier) -> Scalars:
  match xs:
    case Nil{}:
      []
    case Con{+h, t}:
      Con{F.multiply(r, h), extend_tail_prepared(t, r, h)}

def extend_tail(xs: Scalars, r: F.Scalar, previous: F.Scalar) -> Scalars:
  extend_tail_prepared(xs, F.prepare(r), previous)

def extend(xs: Scalars, r: F.Scalar) -> Scalars:
  extend_prepared(xs, F.prepare(r))

# Fuse two recurrence steps without reassociating any field operations.
# Only the final polynomial is allocated; the intermediate row is streamed.
def pair_tail(xs: Scalars, +r: F.Multiplier, +s: F.Multiplier, +previous: F.Scalar, middle: F.Scalar) -> Scalars:
  match xs:
    case Nil{}:
      [F.add(F.multiply(r, previous), middle), previous]
    case Con{+h, t}:
      +next = F.add(F.multiply(s, h), previous)
      Con{F.add(F.multiply(r, next), middle), pair_tail(t, r, s, h, next)}

def pair_prepared(xs: Scalars, +r: F.Multiplier, +s: F.Multiplier) -> Scalars:
  match xs:
    case Nil{}:
      []
    case Con{+h, t}:
      +middle = F.multiply(s, h)
      Con{F.multiply(r, middle), pair_tail(t, r, s, h, middle)}

def extend_pair(xs: Scalars, r: F.Scalar, s: F.Scalar) -> Scalars:
  pair_prepared(xs, F.prepare(r), F.prepare(s))

# Four successive factors share one traversal. The three middle coefficients
# carry exactly the values produced by the original recurrence, in its order.
def four_tail(xs: Scalars, +r: F.Multiplier, +s: F.Multiplier, +t: F.Multiplier, +u: F.Multiplier, previous: F.Scalar, middle1: F.Scalar, middle2: F.Scalar, middle3: F.Scalar) -> Scalars:
  match xs:
    case Nil{}:
      pair_tail(extend_tail_prepared([previous], t, middle1), r, s, middle2, middle3)
    case Con{+h, tail}:
      +v1 = F.add(F.multiply(u, h), previous)
      +v2 = F.add(F.multiply(t, v1), middle1)
      +v3 = F.add(F.multiply(s, v2), middle2)
      Con{F.add(F.multiply(r, v3), middle3), four_tail(tail, r, s, t, u, h, v1, v2, v3)}

def four_prepared(xs: Scalars, +r: F.Multiplier, +s: F.Multiplier, +t: F.Multiplier, +u: F.Multiplier) -> Scalars:
  match xs:
    case Nil{}:
      []
    case Con{+h, tail}:
      +v1 = F.multiply(u, h)
      +v2 = F.multiply(t, v1)
      +v3 = F.multiply(s, v2)
      Con{F.multiply(r, v3), four_tail(tail, r, s, t, u, h, v1, v2, v3)}

def extend_four(xs: Scalars, r: F.Scalar, s: F.Scalar, t: F.Scalar, u: F.Scalar) -> Scalars:
  four_prepared(xs, F.prepare(r), F.prepare(s), F.prepare(t), F.prepare(u))

def coefficients(xs: Scalars) -> Scalars:
  match xs:
    case Nil{}:
      [F.one()]
    case Con{r, rest}:
      match rest:
        case Nil{}:
          extend([F.one()], r)
        case Con{s, rest2}:
          match rest2:
            case Nil{}:
              extend_pair([F.one()], r, s)
            case Con{t, rest3}:
              match rest3:
                case Nil{}:
                  extend_pair(extend([F.one()], t), r, s)
                case Con{u, tail}:
                  extend_four(coefficients(tail), r, s, t, u)

def all_valid(xs: Scalars) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(F.valid(h), all_valid(t))

def accept(+xs: Scalars, basis_size: Nat) -> Bool:
  Bool.and(all_valid(xs), Nat.is_eq(basis_size, 1n+length(xs)))

def gate(xs: Scalars, accepted: Bool) -> Maybe<&2, Scalars>:
  match accepted:
    case False{}:
      None{}
    case True{}:
      Some{coefficients(xs)}

# The adapter must use this entry point before handing coefficients to MSM.
def checked(+xs: Scalars, basis_size: Nat) -> Maybe<&2, Scalars>:
  gate(xs, accept(xs, basis_size))
