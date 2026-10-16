import ListOperations
open ScalarImpl ScalarLaws Field Polynomial PolynomialModel
namespace OriginalPolynomial
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- The streaming two-factor loop performs exactly two original recurrence steps. -/
theorem pair_tail (xs : Scalars) (r s : Multiplier) (previous middle : Scalar) :
    PolynomialImpl.extend_tail_prepared (PolynomialImpl.extend_tail_prepared xs s previous) r middle =
      PolynomialImpl.pair_tail xs r s previous middle := by
  induction xs generalizing previous middle with
  | nil => rfl
  | cons a xs ih =>
    simpa only [PolynomialImpl.extend_tail_prepared, PolynomialImpl.pair_tail] using
      congrArg (List.cons (add (multiply r (add (multiply s a) previous)) middle))
        (ih a (add (multiply s a) previous))

theorem pair_agrees (xs : Scalars) (r s : Multiplier) :
    PolynomialImpl.extend_prepared (PolynomialImpl.extend_prepared xs s) r =
      PolynomialImpl.pair_prepared xs r s := by
  cases xs with
  | nil => rfl
  | cons a xs => simp only [PolynomialImpl.extend_prepared, PolynomialImpl.pair_prepared, pair_tail]

theorem four_tail (xs : Scalars) (r s t u : Multiplier) (previous m1 m2 m3 : Scalar) :
    PolynomialImpl.extend_tail_prepared
      (PolynomialImpl.extend_tail_prepared
        (PolynomialImpl.extend_tail_prepared
          (PolynomialImpl.extend_tail_prepared xs u previous) t m1) s m2) r m3 =
      PolynomialImpl.four_tail xs r s t u previous m1 m2 m3 := by
  induction xs generalizing previous m1 m2 m3 with
  | nil => simp only [PolynomialImpl.four_tail, PolynomialImpl.extend_tail_prepared, PolynomialImpl.pair_tail]
  | cons a xs ih =>
    simp only [PolynomialImpl.extend_tail_prepared, PolynomialImpl.four_tail]
    congr 1
    exact ih a (add (multiply u a) previous) (add (multiply t (add (multiply u a) previous)) m1)
      (add (multiply s (add (multiply t (add (multiply u a) previous)) m1)) m2)

theorem four_agrees (xs : Scalars) (r s t u : Multiplier) :
    PolynomialImpl.extend_prepared
      (PolynomialImpl.extend_prepared
        (PolynomialImpl.extend_prepared (PolynomialImpl.extend_prepared xs u) t) s) r =
      PolynomialImpl.four_prepared xs r s t u := by
  cases xs with
  | nil => rfl
  | cons a xs => simp only [PolynomialImpl.extend_prepared, PolynomialImpl.four_prepared, four_tail]

/-- The unoptimized one-factor reference, independent of the blocked traversal. -/
def reference : Scalars → Scalars
  | [] => [one]
  | a :: xs => PolynomialImpl.extend (reference xs) a

theorem original_agrees (xs : Scalars) : PolynomialImpl.coefficients xs = reference xs := by
  fun_induction PolynomialImpl.coefficients xs with
  | case1 => rfl
  | case2 r => rfl
  | case3 r s =>
    simp only [reference, PolynomialImpl.extend_pair, PolynomialImpl.extend,
      ← pair_agrees]
  | case4 r s t =>
    simp only [reference, PolynomialImpl.extend_pair, PolynomialImpl.extend,
      ← pair_agrees]
  | case5 r s t u tail ih =>
    simp only [reference, PolynomialImpl.extend_four, PolynomialImpl.extend,
      ← four_agrees, ih]

/-- A tail recurrence adds the carried previous coefficient and one linear factor. -/
theorem extend_tail_spec (xs : Scalars) (r previous : Scalar)
    (hx : Canon xs) (hr : decode r < p) (hp : decode previous < p) :
    Canon (PolynomialImpl.extend_tail_prepared xs (prepare r) previous) ∧
    poly sr (PolynomialImpl.extend_tail_prepared xs (prepare r) previous) =
      C (sr previous) + (C (sr r) + X) * poly sr xs := by
  induction xs generalizing previous with
  | nil => simpa [PolynomialImpl.extend_tail_prepared] using hp
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
    obtain ⟨hc, hq⟩ := ih a hxs ha
    have hm : decode (multiply (prepare r) a) < p := mul_closed r a hr ha
    have he : sr (multiply (prepare r) a) = sr r * sr a := sr_mul r a hr ha
    constructor
    · exact (canon_cons _ _).mpr ⟨add_closed _ previous hm hp, hc⟩
    · simp only [PolynomialImpl.extend_tail_prepared, poly_cons, sr_add _ _ hm hp, he, C_add, C_mul, hq]
      ring

theorem extend_spec (xs : Scalars) (r : Scalar) (hx : Canon xs) (hr : decode r < p) :
    Canon (PolynomialImpl.extend xs r) ∧
    poly sr (PolynomialImpl.extend xs r) = (C (sr r) + X) * poly sr xs := by
  cases xs with
  | nil => simp [PolynomialImpl.extend, PolynomialImpl.extend_prepared]
  | cons a xs =>
    obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
    obtain ⟨hc, hq⟩ := extend_tail_spec xs r a hxs hr ha
    have hm : decode (multiply (prepare r) a) < p := mul_closed r a hr ha
    have he : sr (multiply (prepare r) a) = sr r * sr a := sr_mul r a hr ha
    constructor
    · exact (canon_cons _ _).mpr ⟨hm, hc⟩
    · simp only [PolynomialImpl.extend, PolynomialImpl.extend_prepared, poly_cons, he, C_mul, hq]
      ring

def factors : Scalars → Q
  | [] => 1
  | a :: xs => (C (sr a) + X) * factors xs

theorem coefficients_spec (xs : Scalars) (hx : Canon xs) :
    Canon (PolynomialImpl.coefficients xs) ∧ poly sr (PolynomialImpl.coefficients xs) = factors xs := by
  rw [original_agrees]
  induction xs with
  | nil => simp [reference, factors]
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
    obtain ⟨hc, hp⟩ := ih hxs
    obtain ⟨hcan, hpoly⟩ := extend_spec (reference xs) a hc ha
    simpa only [reference, factors, hp] using And.intro hcan hpoly

end
end OriginalPolynomial
