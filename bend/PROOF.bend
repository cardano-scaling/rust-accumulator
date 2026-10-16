import Base
import ./scalar.bend as F
import ./polynomial.bend as P
import ./specification.bend as Spec
import ./LAWS.bend as Laws

def Laws.empty():
  {==}

def pair_tail_agrees(xs: P.Scalars, -r: F.Scalar, -s: F.Scalar, -previous: F.Scalar, -middle: F.Scalar)
  -> {P.extend_tail(P.extend_tail(xs, s, previous), r, middle) == P.pair_tail(xs, F.prepare(r), F.prepare(s), previous, middle) : P.Scalars}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(P.Scalars, P.Scalars,
        tail => Con{F.add(F.mul(r, F.add(F.mul(s, h), previous)), middle), tail},
        P.extend_tail(P.extend_tail(t, s, h), r, F.add(F.mul(s, h), previous)),
        P.pair_tail(t, F.prepare(r), F.prepare(s), h, F.add(F.mul(s, h), previous)),
        pair_tail_agrees(t, r, s, h, F.add(F.mul(s, h), previous)))

def pair_agrees(xs: P.Scalars, -r: F.Scalar, -s: F.Scalar)
  -> {P.extend(P.extend(xs, s), r) == P.extend_pair(xs, r, s) : P.Scalars}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(P.Scalars, P.Scalars, tail => Con{F.mul(r, F.mul(s, h)), tail},
        P.extend_tail(P.extend_tail(t, s, h), r, F.mul(s, h)),
        P.pair_tail(t, F.prepare(r), F.prepare(s), h, F.mul(s, h)),
        pair_tail_agrees(t, r, s, h, F.mul(s, h)))

def four_tail_agrees(xs: P.Scalars, -r: F.Scalar, -s: F.Scalar, -t: F.Scalar, -u: F.Scalar, -previous: F.Scalar, -m1: F.Scalar, -m2: F.Scalar, -m3: F.Scalar)
  -> {P.extend_tail(P.extend_tail(P.extend_tail(P.extend_tail(xs, u, previous), t, m1), s, m2), r, m3) == P.four_tail(xs, F.prepare(r), F.prepare(s), F.prepare(t), F.prepare(u), previous, m1, m2, m3) : P.Scalars}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, tail}:
      -v1 = F.add(F.mul(u, h), previous)
      -v2 = F.add(F.mul(t, v1), m1)
      -v3 = F.add(F.mul(s, v2), m2)
      Equal.cong(P.Scalars, P.Scalars, rest => Con{F.add(F.mul(r, v3), m3), rest},
        P.extend_tail(P.extend_tail(P.extend_tail(P.extend_tail(tail, u, h), t, v1), s, v2), r, v3),
        P.four_tail(tail, F.prepare(r), F.prepare(s), F.prepare(t), F.prepare(u), h, v1, v2, v3),
        four_tail_agrees(tail, r, s, t, u, h, v1, v2, v3))

def four_agrees(xs: P.Scalars, -r: F.Scalar, -s: F.Scalar, -t: F.Scalar, -u: F.Scalar)
  -> {P.extend(P.extend(P.extend(P.extend(xs, u), t), s), r) == P.extend_four(xs, r, s, t, u) : P.Scalars}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, tail}:
      -v1 = F.mul(u, h)
      -v2 = F.mul(t, v1)
      -v3 = F.mul(s, v2)
      Equal.cong(P.Scalars, P.Scalars, rest => Con{F.mul(r, v3), rest},
        P.extend_tail(P.extend_tail(P.extend_tail(P.extend_tail(tail, u, h), t, v1), s, v2), r, v3),
        P.four_tail(tail, F.prepare(r), F.prepare(s), F.prepare(t), F.prepare(u), h, v1, v2, v3),
        four_tail_agrees(tail, r, s, t, u, h, v1, v2, v3))

# The optimized implementation obeys exactly the original one-factor recurrence.
def coefficients_step(xs: P.Scalars, -r: F.Scalar)
  -> {P.extend(P.coefficients(xs), r) == P.coefficients(Con{r, xs}) : P.Scalars}:
  match xs:
    case Nil{}:
      {==}
    case Con{s, +rest}:
      match rest:
        case Nil{}:
          pair_agrees([F.one()], r, s)
        case Con{t, rest2}:
          match rest2:
            case Nil{}:
              pair_agrees(P.extend([F.one()], t), r, s)
            case Con{u, tail}:
              %coefficients_step(rest, s) : {P.extend(_, r) == P.extend_four(P.coefficients(tail), r, s, t, u) : P.Scalars}
              %coefficients_step(rest2, t) : {P.extend(P.extend(_, s), r) == P.extend_four(P.coefficients(tail), r, s, t, u) : P.Scalars}
              %coefficients_step(tail, u) : {P.extend(P.extend(P.extend(_, t), s), r) == P.extend_four(P.coefficients(tail), r, s, t, u) : P.Scalars}
              four_agrees(P.coefficients(tail), r, s, t, u)

def tail_length(xs: P.Scalars, -r: F.Scalar, -previous: F.Scalar)
  -> {P.length(P.extend_tail(xs, r, previous)) == 1n+P.length(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %tail_length(t, r, h) : {1n+P.length(P.extend_tail(t, r, h)) == 1n+_ : Nat}
      {==}

def extended_size(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      2n+p

def extend_length(xs: P.Scalars, -r: F.Scalar)
  -> {P.length(P.extend(xs, r)) == extended_size(P.length(xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %tail_length(t, r, h) : {1n+P.length(P.extend_tail(t, r, h)) == 1n+_ : Nat}
      {==}

def Laws.no_input_is_dropped(inputs):
  match inputs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %coefficients_step(t, h) : {P.length(_) == 2n+P.length(t) : Nat}
      %Laws.no_input_is_dropped(t) : {P.length(P.extend(P.coefficients(t), h)) == extended_size(_) : Nat}
      extend_length(P.coefficients(t), h)

def tail_at(xs: P.Scalars, -r: F.Scalar, -previous: F.Scalar, k: Nat)
  -> {P.at(P.extend_tail(xs, r, previous), k) == Spec.next(r, P.at(xs, k), P.at(Con{previous, xs}, k)) : Maybe<&2, F.Scalar>}:
  match xs:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case Con{h, t}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          tail_at(t, r, h, j)

def extend_at_zero(xs: P.Scalars, -r: F.Scalar)
  -> {P.at(P.extend(xs, r), 0n) == Spec.constant(r, P.at(xs, 0n)) : Maybe<&2, F.Scalar>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def extend_at_next(xs: P.Scalars, -r: F.Scalar, k: Nat)
  -> {P.at(P.extend(xs, r), 1n+k) == Spec.next(r, P.at(xs, 1n+k), P.at(xs, k)) : Maybe<&2, F.Scalar>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      tail_at(t, r, h, k)

def Laws.every_coefficient_is_correct(inputs, degree):
  match inputs:
    case Nil{}:
      match degree:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case Con{+r, +t}:
      match degree:
        case 0n:
          %coefficients_step(t, r) : {P.at(_, 0n) == Spec.constant(r, Spec.coefficient(t, 0n)) : Maybe<&2, F.Scalar>}
          %Laws.every_coefficient_is_correct(t, 0n) : {P.at(P.extend(P.coefficients(t), r), 0n) == Spec.constant(r, _) : Maybe<&2, F.Scalar>}
          extend_at_zero(P.coefficients(t), r)
        case 1n++k:
          %coefficients_step(t, r) : {P.at(_, 1n+k) == Spec.next(r, Spec.coefficient(t, 1n+k), Spec.coefficient(t, k)) : Maybe<&2, F.Scalar>}
          %Laws.every_coefficient_is_correct(t, 1n+k) : {P.at(P.extend(P.coefficients(t), r), 1n+k) == Spec.next(r, _, Spec.coefficient(t, k)) : Maybe<&2, F.Scalar>}
          %Laws.every_coefficient_is_correct(t, k) : {P.at(P.extend(P.coefficients(t), r), 1n+k) == Spec.next(r, P.at(P.coefficients(t), 1n+k), _) : Maybe<&2, F.Scalar>}
          extend_at_next(P.coefficients(t), r, k)

def last_tail(xs: P.Scalars, -r: F.Scalar, -previous: F.Scalar, -start: F.Scalar)
  -> {List.last.go(&2, F.Scalar, P.extend_tail(xs, r, previous), start) == List.last.go(&2, F.Scalar, xs, previous) : F.Scalar}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      last_tail(t, r, h, F.add(F.mul(r, h), previous))

def last_extend(xs: P.Scalars, -r: F.Scalar)
  -> {List.last(&2, F.Scalar, P.extend(xs, r)) == List.last(&2, F.Scalar, xs) : Maybe<&2, F.Scalar>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %last_tail(t, r, h, F.mul(r, h)) : {Some{List.last.go(&2, F.Scalar, P.extend_tail(t, r, h), F.mul(r, h))} == Some{_} : Maybe<&2, F.Scalar>}
      {==}

def Laws.monic(inputs):
  match inputs:
    case Nil{}:
      {==}
    case Con{r, +t}:
      %coefficients_step(t, r) : {List.last(&2, F.Scalar, _) == Some{F.one()} : Maybe<&2, F.Scalar>}
      %Laws.monic(t) : {List.last(&2, F.Scalar, P.extend(P.coefficients(t), r)) == _ : Maybe<&2, F.Scalar>}
      last_extend(P.coefficients(t), r)

def and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.reject_invalid_scalars(inputs, basis_size, invalid):
  Equal.cong(Bool, Maybe<&2, P.Scalars>,
    b => P.gate(inputs, Bool.and(b, Nat.is_eq(basis_size, 1n+P.length(inputs)))),
    P.all_valid(inputs), False{}, invalid)

def and_right_false(+a: Bool, -b: Bool, e: {b == False{} : Bool})
  -> {Bool.and(a, b) == False{} : Bool}:
  Equal.trans(Bool, Bool.and(a, b), Bool.and(a, False{}), False{},
    Equal.cong(Bool, Bool, x => Bool.and(a, x), b, False{}, e), and_false(a))

def Laws.reject_wrong_basis_size(inputs, basis_size, wrong):
  Equal.cong(Bool, Maybe<&2, P.Scalars>, b => P.gate(inputs, b),
    P.accept(inputs, basis_size), False{},
    and_right_false(P.all_valid(inputs), Nat.is_eq(basis_size, 1n+P.length(inputs)), wrong))

def Laws.accepted_result(inputs, basis_size, accepted):
  Equal.cong(Bool, Maybe<&2, P.Scalars>, b => P.gate(inputs, b),
    P.accept(inputs, basis_size), True{}, accepted)
