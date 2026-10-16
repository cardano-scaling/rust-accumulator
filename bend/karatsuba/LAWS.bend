# Proven properties of the experimental entry point.
# Numerical equivalence for canonical inputs through 256: ../arithmetic/LAWS.lean.
import Base
import ../scalar.bend as F
import ../polynomial.bend as P
import ../karatsuba.bend as K
import ../karatsuba_library.bend as API
import ../library.bend as Request
import ./algebra.bend as Algebra
import ./specification.bend as Spec
import ./structure.bend as Structure

# The empty multiset still produces the constant polynomial one.
law empty:
  {K.coefficients([]) == [F.one()] : P.Scalars}

# Within the native limit, every input contributes one degree, including zeros.
law no_input_is_dropped:
  for +inputs: P.Scalars
  for supported: {Nat.is_lt(P.length(inputs), 257n) == True{} : Bool}
  {P.length(K.coefficients(inputs)) == 1n+P.length(inputs) : Nat}

# A split retains every factor in its original order, even at uneven boundaries.
law input_split_preserves_factors:
  for +inputs: P.Scalars
  for +position: Nat
  {K.append(K.take(inputs, position), K.drop(inputs, position)) == inputs : P.Scalars}

# Every recursive merge preserves the explicit three-product recurrence.
# Numerical convolution correctness is proved in ../arithmetic/Convolution.lean.
law recursive_assembly_is_exact:
  for +depth: Nat
  for +width: Nat
  for +left: P.Scalars
  for +right: P.Scalars
  {K.convolution(depth, width, left, right) == Structure.recurrence(depth, width, left, right) : P.Scalars}

# The full kernel preserves the explicit product-tree assembly and conversions.
# The reference here is still Karatsuba, not the original one-factor recurrence.
law product_tree_assembly_is_exact:
  for +inputs: P.Scalars
  {K.coefficients(inputs) == Structure.reference_coefficients(inputs) : P.Scalars}

# Reject noncanonical inputs before evaluating the product tree.
law reject_invalid_scalars:
  for +inputs: P.Scalars
  for basis_size: Nat
  for invalid: {P.all_valid(inputs) == False{} : Bool}
  {API.dispatch(Request.Coefficients{inputs, basis_size}) == None{} : Maybe<&2, P.Scalars>}

# Reject an SRS whose size could cause MSM to truncate the result.
law reject_wrong_basis_size:
  for +inputs: P.Scalars
  for +basis_size: Nat
  for wrong: {Nat.is_eq(basis_size, 1n+P.length(inputs)) == False{} : Bool}
  {API.dispatch(Request.Coefficients{inputs, basis_size}) == None{} : Maybe<&2, P.Scalars>}

# Validation cannot change the candidate polynomial delivered to the caller.
law accepted_result:
  for +inputs: P.Scalars
  for +basis_size: Nat
  for accepted: {P.accept(inputs, basis_size) == True{} : Bool}
  {API.dispatch(Request.Coefficients{inputs, basis_size}) == Some{K.coefficients(inputs)} : Maybe<&2, P.Scalars>}

# Through 32 inputs the candidate returns the already-proved recurrence.
law small_inputs_preserve_proved_kernel:
  for +inputs: P.Scalars
  for small: {Nat.is_lt(32n, P.length(inputs)) == False{} : Bool}
  {K.coefficients(inputs) == P.coefficients(inputs) : P.Scalars}

# Every leaf coefficient preserves the explicit nine-product assembly.
# Numerical convolution equality for canonical inputs: arithmetic/Convolution.lean.
law leaf_matches_nine_product_spec:
  for +left: K.Four
  for +right: K.Four
  for +degree: Nat
  {P.at(K.leaf(left, right), degree) == P.at(Spec.nine(left, right), degree) : Maybe<&2, F.Scalar>}

# Karatsuba's middle term is exact when the supplied ring facts hold.
law cross_term:
  for -A: Data
  for -add: A -> A -> A
  for -sub: A -> A -> A
  for -mul: A -> A -> A
  for -a: A
  for -b: A
  for -c: A
  for -d: A
  for facts: Algebra.Facts<A, add, sub, mul, a, b, c, d>
  {sub(sub(mul(add(a, b), add(c, d)), mul(a, c)), mul(b, d)) == add(mul(a, d), mul(b, c)) : A}
