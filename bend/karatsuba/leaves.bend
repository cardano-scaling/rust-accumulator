# Streaming Montgomery leaves preserve the original one-factor operation order.
import Base
import ../scalar.bend as F
import ../polynomial.bend as P
import ../karatsuba.bend as K
import ../PROOF.bend as Original

def step_agrees(xs: P.Scalars, -r: F.Scalar)
  -> {P.extend(K.montgomery_coefficients(xs), r) == K.montgomery_coefficients(Con{r, xs}) : P.Scalars}:
  match xs:
    case Nil{}:
      {==}
    case Con{s, +rest}:
      match rest:
        case Nil{}:
          Original.pair_agrees([K.montgomery_one()], r, s)
        case Con{t, rest2}:
          match rest2:
            case Nil{}:
              Original.pair_agrees(P.extend([K.montgomery_one()], t), r, s)
            case Con{u, tail}:
              %step_agrees(rest, s) : {P.extend(_, r) == P.extend_four(K.montgomery_coefficients(tail), r, s, t, u) : P.Scalars}
              %step_agrees(rest2, t) : {P.extend(P.extend(_, s), r) == P.extend_four(K.montgomery_coefficients(tail), r, s, t, u) : P.Scalars}
              %step_agrees(tail, u) : {P.extend(P.extend(P.extend(_, t), s), r) == P.extend_four(K.montgomery_coefficients(tail), r, s, t, u) : P.Scalars}
              Original.four_agrees(K.montgomery_coefficients(tail), r, s, t, u)

def reference(xs: P.Scalars) -> P.Scalars:
  match xs:
    case Nil{}:
      [K.montgomery_one()]
    case Con{a, tail}:
      P.extend(reference(tail), a)

def coefficients_agree(xs: P.Scalars)
  -> {K.montgomery_coefficients(xs) == reference(xs) : P.Scalars}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, +tail}:
      Equal.trans(P.Scalars, K.montgomery_coefficients(Con{a, tail}),
        P.extend(K.montgomery_coefficients(tail), a), P.extend(reference(tail), a),
        Equal.sym(P.Scalars, P.extend(K.montgomery_coefficients(tail), a),
          K.montgomery_coefficients(Con{a, tail}), step_agrees(tail, a)),
        Equal.cong(P.Scalars, P.Scalars, cs => P.extend(cs, a),
          K.montgomery_coefficients(tail), reference(tail), coefficients_agree(tail)))

def coefficients_length(xs: P.Scalars)
  -> {P.length(K.montgomery_coefficients(xs)) == 1n+P.length(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %step_agrees(t, h) : {P.length(_) == 2n+P.length(t) : Nat}
      %coefficients_length(t) : {P.length(P.extend(K.montgomery_coefficients(t), h)) == Original.extended_size(_) : Nat}
      Original.extend_length(K.montgomery_coefficients(t), h)
