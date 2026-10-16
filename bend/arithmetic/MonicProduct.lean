import MultiplyPolynomial
import Representation
open ScalarImpl ScalarLaws Field Polynomial PolynomialModel ListOperations Convolution
  MultiplyPolynomial Representation OriginalPolynomial
namespace MonicProduct
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Removing a leading one subtracts exactly the highest power of X. -/
theorem monic_split (f : Scalar → R) (xs : Scalars) (n : Nat)
    (hl : xs.length = n+1) (ht : (poly f xs).coeff n = 1) :
    poly f xs = poly f (xs.take n) + X^n := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hl
    | cons a xs =>
      have hnil : xs = [] := by cases xs <;> simp_all
      subst xs
      simpa using congrArg C (by simpa using ht : f a = 1)
  | succ n ih =>
    cases xs with
    | nil => simp at hl
    | cons a xs =>
      have ht' : (poly f xs).coeff n = 1 := by simpa [coeff_X_mul] using ht
      have hs := ih xs (by simp only [List.length_cons] at hl; omega) ht'
      simp only [List.take_succ_cons, poly_cons, pow_succ]
      rw [hs]
      ring

/-- The optimized monic product restores both omitted leading coefficients exactly. -/
theorem monic_product_spec (m n : Nat) (xs ys : Scalars)
    (hx : Canon xs) (hy : Canon ys)
    (lx : xs.length = m+1) (ly : ys.length = n+1)
    (mx : 0 < m ∧ m ≤ 256) (ny : 0 < n ∧ n ≤ 256)
    (tx : (poly mr xs).coeff m = 1) (ty : (poly mr ys).coeff n = 1) :
    Canon (KaratsubaImpl.monic_product m n xs ys) ∧
    poly mr (KaratsubaImpl.monic_product m n xs ys) = poly mr xs * poly mr ys ∧
    (KaratsubaImpl.monic_product m n xs ys).length = m+n+1 := by
  have hxa := canon_take xs m hx
  have hya := canon_take ys n hy
  have lxa : (xs.take m).length = m := by simp [lx]
  have lya : (ys.take n).length = n := by simp [ly]
  obtain ⟨hc, hp⟩ := multiply_spec _ _ hxa hya (by omega) (by omega)
  have hl := multiply_length _ _ hxa hya (by omega) (by omega)
  obtain ⟨hic, hip⟩ := shift_add_spec n _ _ hc hxa
  obtain ⟨hoc, hop⟩ := shift_add_spec m _ _ hic hya
  have outer_length :
      (KaratsubaImpl.shift_add m (KaratsubaImpl.shift_add n
        (KaratsubaImpl.multiply (xs.take m) (ys.take n)) (xs.take m)) (ys.take n)).length = m+n := by
    rw [shift_add_length, shift_add_length, hl, lxa, lya]
    omega
  simp only [KaratsubaImpl.monic_product, KaratsubaImpl.take, KaratsubaImpl.append, List.append_eq]
  constructor
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hoc a ha
    · have he : a = KaratsubaImpl.montgomery_one := List.mem_singleton.mp ha
      subst a
      exact montgomery_one_valid
  constructor
  · rw [poly_append, outer_length, hop, hip, hp]
    simp only [poly_cons, poly_nil, montgomery_one_ring, C_1, mul_zero, add_zero, mul_one]
    rw [monic_split mr xs m lx tx, monic_split mr ys n ly ty, pow_add]
    ring
  · simp only [List.length_append, List.length_cons, List.length_nil, outer_length]

end
end MonicProduct
