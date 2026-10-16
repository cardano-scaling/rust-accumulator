import Representation
open ScalarImpl ScalarLaws Field Polynomial PolynomialModel OriginalPolynomial Representation
namespace MontgomeryLeaves
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Changing representation scales every coefficient by the same invertible residue. -/
theorem poly_montgomery (xs : Scalars) : poly mr xs = poly sr xs * C invR := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [poly_cons, mr, C_mul, ih]; ring

def reference : Scalars → Scalars
  | [] => [KaratsubaImpl.montgomery_one]
  | a :: xs => PolynomialImpl.extend (reference xs) a

/-- Fusing four factors preserves the streaming recurrence starting from R. -/
theorem assembly (xs : Scalars) : KaratsubaImpl.montgomery_coefficients xs = reference xs := by
  fun_induction KaratsubaImpl.montgomery_coefficients xs with
  | case1 => rfl
  | case2 r => rfl
  | case3 r s => simp only [reference, PolynomialImpl.extend_pair, PolynomialImpl.extend, ← pair_agrees]
  | case4 r s t => simp only [reference, PolynomialImpl.extend_pair, PolynomialImpl.extend, ← pair_agrees]
  | case5 r s t u tail ih =>
    simp only [reference, PolynomialImpl.extend_four, PolynomialImpl.extend, ← four_agrees, ih]

theorem tail_length (xs : Scalars) (r : Multiplier) (a : Scalar) :
    (PolynomialImpl.extend_tail_prepared xs r a).length = xs.length+1 := by
  induction xs generalizing a with
  | nil => rfl
  | cons y ys ih => simpa [PolynomialImpl.extend_tail_prepared] using ih y

theorem extend_length (xs : Scalars) (r : Scalar) (hn : 0 < xs.length) :
    (PolynomialImpl.extend xs r).length = xs.length+1 := by
  cases xs with
  | nil => simp at hn
  | cons a xs => simp [PolynomialImpl.extend, PolynomialImpl.extend_prepared, tail_length]

/-- Leaves produce the input product directly in Montgomery representation. -/
theorem coefficients_spec (xs : Scalars) (hx : Canon xs) :
    Canon (KaratsubaImpl.montgomery_coefficients xs) ∧
    poly mr (KaratsubaImpl.montgomery_coefficients xs) = factors xs ∧
    (KaratsubaImpl.montgomery_coefficients xs).length = xs.length+1 := by
  rw [assembly]
  induction xs with
  | nil => simp [reference, factors, montgomery_one_valid]
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
    obtain ⟨hc, hp, hl⟩ := ih hxs
    obtain ⟨hec, hep⟩ := OriginalPolynomial.extend_spec (reference xs) a hc ha
    refine ⟨hec, ?_, ?_⟩
    · change poly mr (PolynomialImpl.extend (reference xs) a) = (C (sr a)+X)*factors xs
      rw [poly_montgomery, hep, mul_assoc, ← poly_montgomery, hp]
    · change (PolynomialImpl.extend (reference xs) a).length = (a::xs).length+1
      rw [extend_length _ _ (by omega), hl]
      rfl

end
end MontgomeryLeaves
