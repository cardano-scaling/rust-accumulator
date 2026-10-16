# A native library root. The C adapter calls dispatch with runtime inputs.
# Keeping IO out of the kernel allows the entire arithmetic call graph to check.
import Base
import ./scalar.bend as F
import ./polynomial.bend as P

type Request is Data:
  Coefficients{inputs: P.Scalars, basis_size: Nat}
  Add{left: F.Scalar, right: F.Scalar}
  Sub{left: F.Scalar, right: F.Scalar}
  Mul{left: F.Scalar, right: F.Scalar}

def dispatch(request: Request) -> Maybe<&2, P.Scalars>:
  match request:
    case Coefficients{xs, n}:
      P.checked(xs, n)
    case Add{a, b}:
      Some{[F.add(a, b)]}
    case Sub{a, b}:
      Some{[F.sub(a, b)]}
    case Mul{a, b}:
      Some{[F.mul(a, b)]}

def main() -> List<Maybe<&2, P.Scalars>>:
  [dispatch(Coefficients{[], 1n}), dispatch(Add{F.zero(), F.one()})]
