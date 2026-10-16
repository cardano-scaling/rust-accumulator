# The exact algebraic facts used in Karatsuba's cross-term identity.
# Facts are proof inputs, not axioms: no witness for scalar.bend is supplied here.
import Base

type Facts<-A: Data, -add: A -> A -> A, -sub: A -> A -> A, -mul: A -> A -> A,
           -a: A, -b: A, -c: A, -d: A> is Type:
  Facts{
    split: {mul(add(a, b), add(c, d)) == add(mul(a, add(c, d)), mul(b, add(c, d))) : A},
    left: {mul(a, add(c, d)) == add(mul(a, c), mul(a, d)) : A},
    right: {mul(b, add(c, d)) == add(mul(b, c), mul(b, d)) : A},
    outer: {add(add(mul(a, c), mul(a, d)), add(mul(b, c), mul(b, d))) == add(mul(a, c), add(mul(a, d), add(mul(b, c), mul(b, d)))) : A},
    inner: {add(mul(a, d), add(mul(b, c), mul(b, d))) == add(add(mul(a, d), mul(b, c)), mul(b, d)) : A},
    cancel_low: {sub(add(mul(a, c), add(add(mul(a, d), mul(b, c)), mul(b, d))), mul(a, c)) == add(add(mul(a, d), mul(b, c)), mul(b, d)) : A},
    cancel_high: {sub(add(add(mul(a, d), mul(b, c)), mul(b, d)), mul(b, d)) == add(mul(a, d), mul(b, c)) : A}}

def cross_identity(-A: Data, -add: A -> A -> A, -sub: A -> A -> A, -mul: A -> A -> A,
                   -a: A, -b: A, -c: A, -d: A, facts: Facts<A, add, sub, mul, a, b, c, d>)
  -> {sub(sub(mul(add(a, b), add(c, d)), mul(a, c)), mul(b, d)) == add(mul(a, d), mul(b, c)) : A}:
  match facts:
    case Facts{split, left, right, outer, inner, cancel_low, cancel_high}:
      expanded_left = Equal.cong(A, A, x => add(x, mul(b, add(c, d))),
        mul(a, add(c, d)), add(mul(a, c), mul(a, d)), left)
      expanded_right = Equal.cong(A, A, x => add(add(mul(a, c), mul(a, d)), x),
        mul(b, add(c, d)), add(mul(b, c), mul(b, d)), right)
      reassociated = Equal.cong(A, A, x => add(mul(a, c), x),
        add(mul(a, d), add(mul(b, c), mul(b, d))),
        add(add(mul(a, d), mul(b, c)), mul(b, d)), inner)
      expanded = Equal.trans(A, mul(add(a, b), add(c, d)),
        add(mul(a, add(c, d)), mul(b, add(c, d))),
        add(add(mul(a, c), mul(a, d)), mul(b, add(c, d))), split, expanded_left)
      distributed = Equal.trans(A, mul(add(a, b), add(c, d)),
        add(add(mul(a, c), mul(a, d)), mul(b, add(c, d))),
        add(add(mul(a, c), mul(a, d)), add(mul(b, c), mul(b, d))), expanded, expanded_right)
      grouped = Equal.trans(A, mul(add(a, b), add(c, d)),
        add(add(mul(a, c), mul(a, d)), add(mul(b, c), mul(b, d))),
        add(mul(a, c), add(mul(a, d), add(mul(b, c), mul(b, d)))), distributed, outer)
      ordered = Equal.trans(A, mul(add(a, b), add(c, d)),
        add(mul(a, c), add(mul(a, d), add(mul(b, c), mul(b, d)))),
        add(mul(a, c), add(add(mul(a, d), mul(b, c)), mul(b, d))), grouped, reassociated)
      removed_low = Equal.trans(A, sub(mul(add(a, b), add(c, d)), mul(a, c)),
        sub(add(mul(a, c), add(add(mul(a, d), mul(b, c)), mul(b, d))), mul(a, c)),
        add(add(mul(a, d), mul(b, c)), mul(b, d)),
        Equal.cong(A, A, x => sub(x, mul(a, c)), mul(add(a, b), add(c, d)),
          add(mul(a, c), add(add(mul(a, d), mul(b, c)), mul(b, d))), ordered), cancel_low)
      Equal.trans(A, sub(sub(mul(add(a, b), add(c, d)), mul(a, c)), mul(b, d)),
        sub(add(add(mul(a, d), mul(b, c)), mul(b, d)), mul(b, d)),
        add(mul(a, d), mul(b, c)),
        Equal.cong(A, A, x => sub(x, mul(b, d)),
          sub(mul(add(a, b), add(c, d)), mul(a, c)),
          add(add(mul(a, d), mul(b, c)), mul(b, d)), removed_low), cancel_high)
