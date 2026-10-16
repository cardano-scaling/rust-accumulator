# Independent, one-coefficient-at-a-time specification of product (x + input).
# None denotes a degree outside the polynomial; zero is an actual coefficient.
import Base
import ./scalar.bend as F
import ./polynomial.bend as P

def constant(r: F.Scalar, c: Maybe<&2, F.Scalar>) -> Maybe<&2, F.Scalar>:
  match c:
    case None{}:
      None{}
    case Some{v}:
      Some{F.mul(r, v)}

# Coefficient k in (x+r)p is r*p[k] + p[k-1].
def next(r: F.Scalar, current: Maybe<&2, F.Scalar>, lower: Maybe<&2, F.Scalar>) -> Maybe<&2, F.Scalar>:
  match current lower:
    case None{} None{}:
      None{}
    case None{} Some{b}:
      Some{b}
    case Some{a} None{}:
      None{}
    case Some{a} Some{b}:
      Some{F.add(F.mul(r, a), b)}

def coefficient(xs: P.Scalars, k: Nat) -> Maybe<&2, F.Scalar>:
  match xs:
    case Nil{}:
      match k:
        case 0n:
          Some{F.one()}
        case 1n+j:
          None{}
    case Con{+r, +rest}:
      match k:
        case 0n:
          constant(r, coefficient(rest, 0n))
        case 1n++j:
          next(r, coefficient(rest, 1n+j), coefficient(rest, j))
