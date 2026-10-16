import OriginalPolynomial
open ScalarImpl ScalarLaws Reduction Field Polynomial PolynomialModel OriginalPolynomial
namespace Representation
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

@[simp] theorem r_squared_valid : decode r_squared < p := by decide +kernel
@[simp] theorem montgomery_one_valid : decode KaratsubaImpl.montgomery_one < p := by decide +kernel

theorem conversion_ring : sr r_squared * invR * invR = 1 := by
  apply Fin.ext
  change ((decode r_squared % p * (inverseR % p)) % p * (inverseR % p)) % p = 1
  simpa only [Nat.mul_mod, Nat.mod_mod] using conversion_constant

@[simp] theorem montgomery_one_ring : mr KaratsubaImpl.montgomery_one = 1 := by
  apply Fin.ext
  change ((decode montgomery_one % p) * (inverseR % p)) % p = 1
  rw [← Nat.mul_mod]
  exact identity_constant

theorem into_scalar (a : Scalar) (ha : decode a < p) : mr (montgomery r_squared a) = sr a := by
  rw [mr, sr_montgomery _ _ r_squared_valid ha]
  calc
    sr r_squared * sr a * invR * invR = sr a * (sr r_squared * invR * invR) := by ring
    _ = sr a := by rw [conversion_ring, mul_one]

theorem from_scalar (a : Scalar) (ha : decode a < p) : sr (montgomery one a) = mr a := by
  rw [sr_montgomery _ _ one_valid ha, sr_one, one_mul]
  rfl

theorem into_spec (xs : Scalars) (hx : Canon xs) :
    Canon (KaratsubaImpl.into_montgomery xs) ∧
    poly mr (KaratsubaImpl.into_montgomery xs) = poly sr xs ∧
    (KaratsubaImpl.into_montgomery xs).length = xs.length := by
  induction xs with
  | nil => simp [KaratsubaImpl.into_montgomery]
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
    obtain ⟨hc, hp, hl⟩ := ih hxs
    simp only [KaratsubaImpl.into_montgomery, canon_cons, poly_cons, List.length_cons]
    exact ⟨⟨montgomery_closed _ _ r_squared_valid ha, hc⟩,
      by rw [into_scalar a ha, hp], by rw [hl]⟩

theorem from_spec (xs : Scalars) (hx : Canon xs) :
    Canon (KaratsubaImpl.from_montgomery xs) ∧
    poly sr (KaratsubaImpl.from_montgomery xs) = poly mr xs ∧
    (KaratsubaImpl.from_montgomery xs).length = xs.length := by
  induction xs with
  | nil => simp [KaratsubaImpl.from_montgomery]
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
    obtain ⟨hc, hp, hl⟩ := ih hxs
    simp only [KaratsubaImpl.from_montgomery, canon_cons, poly_cons, List.length_cons]
    exact ⟨⟨montgomery_closed _ _ one_valid ha, hc⟩,
      by rw [from_scalar a ha, hp], by rw [hl]⟩

/-- The public recurrence always returns degree plus one coefficients. -/
theorem original_length (xs : Scalars) : (PolynomialImpl.coefficients xs).length = xs.length + 1 := by
  have tail_length : ∀ (ys : Scalars) r a,
      (PolynomialImpl.extend_tail_prepared ys r a).length = ys.length + 1 := by
    intro ys r
    induction ys with
    | nil => intro a; rfl
    | cons y ys ih => intro a; simpa [PolynomialImpl.extend_tail_prepared] using ih y
  have extend_length : ∀ (ys : Scalars) r, 0 < ys.length →
      (PolynomialImpl.extend ys r).length = ys.length + 1 := by
    intro ys r hn
    cases ys with
    | nil => simp at hn
    | cons a ys => simp [PolynomialImpl.extend, PolynomialImpl.extend_prepared, tail_length]
  rw [original_agrees]
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [reference, List.length_cons]
    rw [extend_length _ _ (by omega), ih]

theorem factors_append (xs ys : Scalars) : factors (xs ++ ys) = factors xs * factors ys := by
  induction xs with
  | nil => simp [factors]
  | cons a xs ih => simp only [List.cons_append, factors, ih]; ring

/-- A product of monic linear factors has leading coefficient one. -/
theorem factors_top (xs : Scalars) :
    (factors xs).coeff xs.length = 1 ∧ ∀ k, xs.length < k → (factors xs).coeff k = 0 := by
  induction xs with
  | nil =>
    constructor
    · simp [factors]
    · intro k hk
      have h : k ≠ 0 := by simp only [List.length_nil] at hk; omega
      simp [factors, coeff_one, h]
  | cons a xs ih =>
    obtain ⟨ht, ho⟩ := ih
    constructor
    · simp only [List.length_cons, factors, add_mul, coeff_add, coeff_C_mul, coeff_X_mul]
      rw [ho (xs.length+1) (by omega), mul_zero, zero_add, ht]
    · intro k hk
      cases k with
      | zero => simp at hk
      | succ k =>
        simp only [factors, add_mul, coeff_add, coeff_C_mul, coeff_X_mul]
        rw [ho (k+1) (by simp only [List.length_cons] at hk; omega),
          ho k (by simp only [List.length_cons] at hk; omega)]
        simp

end
end Representation
