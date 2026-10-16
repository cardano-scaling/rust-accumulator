# Experimental entry point. The original library and its laws remain separate.
import Base
import ./scalar.bend as F
import ./polynomial.bend as P
import ./karatsuba.bend as K
import ./library.bend as API

def dispatch(request: API.Request) -> Maybe<&2, P.Scalars>:
  match request:
    case API.Coefficients{xs, n}:
      K.checked(xs, n)
    case API.Add{a, b}:
      Some{[F.add(a, b)]}
    case API.Sub{a, b}:
      Some{[F.sub(a, b)]}
    case API.Mul{a, b}:
      Some{[F.mul(a, b)]}

def main() -> List<Maybe<&2, P.Scalars>>:
  [dispatch(API.Coefficients{[], 1n}), dispatch(API.Add{F.zero(), F.one()})]
