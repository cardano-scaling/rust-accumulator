# Explicit nine-product assembly, independent of the fused scalar bindings.
# Its numerical convolution meaning is proved in arithmetic/Convolution.lean.
import Base
import ../scalar.bend as F
import ../polynomial.bend as P
import ../karatsuba.bend as K

type Three is Data:
  Three{a: F.Scalar, b: F.Scalar, c: F.Scalar}

def two(+a: F.Scalar, +b: F.Scalar, +c: F.Scalar, +d: F.Scalar) -> Three:
  +low = F.montgomery(a, c)
  +high = F.montgomery(b, d)
  Three{low, F.sub(F.sub(F.montgomery(F.add(a, b), F.add(c, d)), low), high), high}

def assemble(low: Three, middle: Three, high: Three) -> P.Scalars:
  match low middle high:
    case Three{+a, +b, +c} Three{d, e, f} Three{+g, +h, +i}:
      [a, b, F.add(c, F.sub(F.sub(d, a), g)),
       F.sub(F.sub(e, b), h), F.add(g, F.sub(F.sub(f, c), i)), h, i]

def nine(left: K.Four, right: K.Four) -> P.Scalars:
  match left right:
    case K.Four{+a, +b, +c, +d} K.Four{+e, +f, +g, +h}:
      assemble(two(a, b, e, f),
        two(F.add(a, c), F.add(b, d), F.add(e, g), F.add(f, h)), two(c, d, g, h))
