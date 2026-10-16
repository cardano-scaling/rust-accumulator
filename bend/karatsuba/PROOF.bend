import Base
import ../scalar.bend as F
import ../polynomial.bend as P
import ../karatsuba.bend as K
import ../PROOF.bend as Reference
import ./algebra.bend as Algebra
import ./structure.bend as Structure
import ./shape.bend as Shape
import ./bounds.bend as Bounds
import ./LAWS.bend as Laws

def Laws.empty():
  {==}

def Laws.no_input_is_dropped(inputs, supported):
  Equal.trans(Nat, P.length(K.coefficients(inputs)), Shape.coefficients_size(P.length(inputs)),
    1n+P.length(inputs), Shape.coefficients_length(inputs), Bounds.coefficient_count(P.length(inputs), supported))

def Laws.input_split_preserves_factors(inputs, position):
  Structure.split_agrees(inputs, position)

def Laws.recursive_assembly_is_exact(depth, width, left, right):
  Structure.recurrence_agrees(depth, width, left, right)

def Laws.product_tree_assembly_is_exact(inputs):
  Structure.coefficients_agree(inputs)

def Laws.reject_invalid_scalars(inputs, basis_size, invalid):
  Equal.cong(Bool, Maybe<&2, P.Scalars>,
    b => K.gate(inputs, Bool.and(b, Nat.is_eq(basis_size, 1n+P.length(inputs)))),
    P.all_valid(inputs), False{}, invalid)

def Laws.reject_wrong_basis_size(inputs, basis_size, wrong):
  Equal.cong(Bool, Maybe<&2, P.Scalars>, b => K.gate(inputs, b),
    P.accept(inputs, basis_size), False{},
    Reference.and_right_false(P.all_valid(inputs), Nat.is_eq(basis_size, 1n+P.length(inputs)), wrong))

def Laws.accepted_result(inputs, basis_size, accepted):
  Equal.cong(Bool, Maybe<&2, P.Scalars>, b => K.gate(inputs, b),
    P.accept(inputs, basis_size), True{}, accepted)

def copy_equality(-A: Type, -a: A, -b: A, e: {a == b : A})
  -> {a == b : A} & {a == b : A}:
  %e : {a == _ : A} & {a == _ : A}
  ({==}, {==})

def small_step(-count: Nat, -size: K.Dimensions,
              previous: {Nat.is_lt(32n, count) == False{} : Bool} -> {size == K.Size{0n, 32n} : K.Dimensions},
              copies: {Nat.is_lt(32n, count) == False{} : Bool} & {Nat.is_lt(32n, count) == False{} : Bool})
  -> {K.grow(size, count) == K.Size{0n, 32n} : K.Dimensions}:
  match copies:
    case Tuple{again, now}:
      Equal.trans(K.Dimensions, K.grow(size, count),
        K.grow(K.Size{0n, 32n}, count), K.Size{0n, 32n},
        Equal.cong(K.Dimensions, K.Dimensions, s => K.grow(s, count),
          size, K.Size{0n, 32n}, previous(again)),
        Equal.cong(Bool, K.Dimensions,
          b => Bool.pick(K.Dimensions, b, K.Size{1n, 64n}, K.Size{0n, 32n}),
          Nat.is_lt(32n, count), False{}, now))

def small_dimensions(fuel: Nat, -count: Nat, small: {Nat.is_lt(32n, count) == False{} : Bool})
  -> {K.tree_dimensions(fuel, count) == K.Size{0n, 32n} : K.Dimensions}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      small_step(count, K.tree_dimensions(p, count),
        e => small_dimensions(p, count, e),
        copy_equality(Bool, Nat.is_lt(32n, count), False{}, small))

def Laws.small_inputs_preserve_proved_kernel(inputs, small):
  Equal.cong(K.Dimensions, P.Scalars, size => K.coefficients_sized(size, inputs),
    K.tree_dimensions(3n, P.length(inputs)), K.Size{0n, 32n},
    small_dimensions(3n, P.length(inputs), small))

def Laws.cross_term(A, add, sub, mul, a, b, c, d, facts):
  Algebra.cross_identity(A, add, sub, mul, a, b, c, d, facts)


def Laws.leaf_matches_nine_product_spec(left, right, degree):
  Equal.cong(P.Scalars, Maybe<&2, F.Scalar>, xs => P.at(xs, degree),
    K.leaf(left, right), Structure.reference_leaf(left, right),
    Structure.reference_leaf_agrees(left, right))
