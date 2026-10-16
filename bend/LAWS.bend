# Contract for the coefficient kernel used before G1/G2 MSM.
# Inputs are field elements, not byte strings. Their factors are (x + input).
# These laws do not assert cryptographic binding or verify the foreign MSM.
import Base
import ./scalar.bend as F
import ./polynomial.bend as P
import ./specification.bend as Spec
import ./library.bend as API

# The empty multiset commits to the constant polynomial one.
law empty:
  {P.coefficients([]) == [F.one()] : P.Scalars}

# Every input contributes one degree, including zero and repeated inputs.
law no_input_is_dropped:
  for +inputs: P.Scalars
  {P.length(P.coefficients(inputs)) == 1n+P.length(inputs) : Nat}

# Every coefficient is that of product (x + input), in ascending degree order.
law every_coefficient_is_correct:
  for +inputs: P.Scalars
  for +degree: Nat
  {P.at(P.coefficients(inputs), degree) == Spec.coefficient(inputs, degree) : Maybe<&2, F.Scalar>}

# The highest coefficient is one; the polynomial cannot collapse to zero.
law monic:
  for inputs: P.Scalars
  {List.last(&2, F.Scalar, P.coefficients(inputs)) == Some{F.one()} : Maybe<&2, F.Scalar>}

# Reject noncanonical scalars instead of silently reducing attacker input.
law reject_invalid_scalars:
  for +inputs: P.Scalars
  for basis_size: Nat
  for invalid: {P.all_valid(inputs) == False{} : Bool}
  {API.dispatch(API.Coefficients{inputs, basis_size}) == None{} : Maybe<&2, P.Scalars>}

# Require one basis point per coefficient; MSM must never truncate a polynomial.
law reject_wrong_basis_size:
  for +inputs: P.Scalars
  for +basis_size: Nat
  for wrong: {Nat.is_eq(basis_size, 1n+P.length(inputs)) == False{} : Bool}
  {API.dispatch(API.Coefficients{inputs, basis_size}) == None{} : Maybe<&2, P.Scalars>}

# Validation cannot change the polynomial that reaches MSM.
law accepted_result:
  for +inputs: P.Scalars
  for +basis_size: Nat
  for accepted: {P.accept(inputs, basis_size) == True{} : Bool}
  {API.dispatch(API.Coefficients{inputs, basis_size}) == Some{P.coefficients(inputs)} : Maybe<&2, P.Scalars>}
