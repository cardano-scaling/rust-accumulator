/- Arithmetic and coefficient laws for the actual Bend implementations.
   check.py regenerates scalar and both polynomial definitions before checking. The translation
   and its Base/U32 mapping are trusted; every theorem is checked by Lean's kernel.
   Canonical inputs are integers in [0, p). No primality or cryptographic assumption
   is needed for these ring laws. -/
import Validation
open ScalarImpl ScalarLaws Montgomery Reduction Field
open PolynomialModel
namespace LAWS
noncomputable section

/-- Validation accepts exactly canonical encodings. -/
theorem canonical_validation (a : Scalar) :
    valid a = decide (decode a < p) := valid_exact a

/-- Addition is ordinary addition modulo p. -/
theorem addition (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    decode (add a b) = (decode a + decode b) % p := add_exact a b ha hb

/-- Subtraction is ordinary subtraction modulo p. -/
theorem subtraction (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    decode (sub a b) = (decode a + p - decode b) % p := sub_exact a b ha hb

/-- Multiplication is ordinary multiplication modulo p. -/
theorem multiplication (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    decode (mul a b) = (decode a * decode b) % p := mul_exact a b ha hb

/-- Arithmetic preserves canonical encodings. -/
theorem canonical_results (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    decode (add a b) < p ∧ decode (sub a b) < p ∧ decode (mul a b) < p :=
  ⟨add_closed a b ha hb, sub_closed a b ha hb, mul_closed a b ha hb⟩

/-- Representation changes preserve public values. -/
theorem conversion_roundtrip (a : Scalar) (ha : decode a < p) :
    montgomery one (montgomery r_squared a) = a := montgomery_roundtrip a ha

/-- The product tree's literal leading coefficient acts as one. -/
theorem leading_one (a : Scalar) (ha : decode a < p) :
    montgomery montgomery_one a = a := montgomery_identity a ha

/-- Three Montgomery products recover the two cross terms exactly. -/
theorem karatsuba_cross_term (a b c d : Scalar)
    (ha : decode a < p) (hb : decode b < p) (hc : decode c < p) (hd : decode d < p) :
    sub (sub (montgomery (add a b) (add c d)) (montgomery a c)) (montgomery b d) =
      add (montgomery a d) (montgomery b c) := karatsuba_cross a b c d ha hb hc hd

/-- The fast kernel returns exactly the original coefficient encodings. -/
theorem exact_coefficients (xs : Scalars) (hx : Canon xs) (hn : xs.length ≤ 256) :
    KaratsubaImpl.coefficients xs = PolynomialImpl.coefficients xs :=
  ProductTree.coefficients_equal xs hx hn

/-- Empty input requires only the canonical encoding of one. -/
theorem empty_coefficients : KaratsubaImpl.coefficients [] = [one] := rfl

/-- A singleton requires only a validated input copy and the encoding of one. -/
theorem singleton_coefficients (a : Scalar) (ha : decode a < p) :
    KaratsubaImpl.coefficients [a] = [a, one] := by
  rw [exact_coefficients [a] (by simpa using ha) (by simp)]
  change [mul a one, one] = [a, one]
  have h : mul a one = a := by
    apply decode_injective
    rw [mul_exact a one ha PolynomialModel.one_valid]
    have ho : decode one = 1 := by decide +kernel
    rw [ho, Nat.mul_one, Nat.mod_eq_of_lt ha]
  rw [h]

/-- Every input contributes a factor, including zeros and duplicates. -/
theorem input_product (xs : Scalars) (hx : Canon xs) (hn : xs.length ≤ 256) :
    poly sr (KaratsubaImpl.coefficients xs) = OriginalPolynomial.factors xs :=
  (ProductTree.coefficients_spec xs hx hn).2.1

/-- Successful computation returns n+1 canonical coefficients. -/
theorem output_shape (xs : Scalars) (hx : Canon xs) (hn : xs.length ≤ 256) :
    Canon (KaratsubaImpl.coefficients xs) ∧
    (KaratsubaImpl.coefficients xs).length = xs.length+1 :=
  ⟨(ProductTree.coefficients_spec xs hx hn).1, (ProductTree.coefficients_spec xs hx hn).2.2⟩

/-- The result is monic. -/
theorem monic (xs : Scalars) (hx : Canon xs) (hn : xs.length ≤ 256) :
    (poly sr (KaratsubaImpl.coefficients xs)).coeff xs.length = 1 := by
  rw [input_product xs hx hn]
  exact (Representation.factors_top xs).1

/-- The checked entry point rejects exactly bad scalars or a wrong basis length. -/
theorem rejection (xs : Scalars) (basis : Nat) :
    KaratsubaImpl.checked xs basis = none ↔ ¬Canon xs ∨ basis ≠ xs.length+1 :=
  Validation.rejected xs basis

/-- Validation preserves the result of the original checked entry point. -/
theorem checked_equivalence (xs : Scalars) (basis : Nat) (hn : xs.length ≤ 256) :
    KaratsubaImpl.checked xs basis = PolynomialImpl.checked xs basis :=
  Validation.checked_equal xs basis hn

/-- Input order is unauthenticated: equal multisets yield equal coefficients. -/
theorem multiset_semantics (xs ys : Scalars) (h : xs.Perm ys)
    (hx : Canon xs) (hn : xs.length ≤ 256) :
    KaratsubaImpl.coefficients xs = KaratsubaImpl.coefficients ys :=
  ProductTree.permutation_invariant xs ys h hx hn

end
end LAWS
