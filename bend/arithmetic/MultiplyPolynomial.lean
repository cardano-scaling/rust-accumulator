import Convolution
open ScalarImpl ScalarLaws Field Polynomial PolynomialModel ListOperations Convolution
namespace MultiplyPolynomial
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem length_eq (xs : Scalars) : PolynomialImpl.length xs = xs.length := by
  induction xs <;> simp_all [PolynomialImpl.length, Nat.add_comm]

theorem pad_spec (xs : Scalars) (n : Nat) (hx : Canon xs) :
    Canon (KaratsubaImpl.pad xs n) ∧ poly mr (KaratsubaImpl.pad xs n) = poly mr xs ∧
    (KaratsubaImpl.pad xs n).length = max xs.length n := by
  obtain ⟨hc, hp, hl⟩ := zeros_spec (n - xs.length)
  simp only [KaratsubaImpl.pad, KaratsubaImpl.append, length_eq]
  change Canon (xs ++ KaratsubaImpl.zeros (n-xs.length)) ∧
    poly mr (xs ++ KaratsubaImpl.zeros (n-xs.length)) = poly mr xs ∧
    (xs ++ KaratsubaImpl.zeros (n-xs.length)).length = max xs.length n
  constructor
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hx a ha
    · exact hc a ha
  constructor
  · rw [poly_append, hp]; simp
  · rw [List.length_append, hl]; omega

theorem take_coeff (f : Scalar → R) (xs : Scalars) (n k : Nat) (hk : k < n) :
    (poly f (xs.take n)).coeff k = (poly f xs).coeff k := by
  induction xs generalizing n k with
  | nil => simp
  | cons a xs ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases k with
      | zero => simp
      | succ k => simpa [coeff_X_mul] using ih n k (by omega)

theorem take_preserves (f : Scalar → R) (xs : Scalars) (n : Nat)
    (h : ∀ k, n ≤ k → (poly f xs).coeff k = 0) : poly f (xs.take n) = poly f xs := by
  ext k
  by_cases hk : k < n
  · exact take_coeff f xs n k hk
  · rw [h k (by omega), coeff_outside f (xs.take n) k (by simp; omega)]

theorem product_outside (f : Scalar → R) (xs ys : Scalars) (k : Nat)
    (hk : xs.length + ys.length - 1 ≤ k) : (poly f xs * poly f ys).coeff k = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
  by_cases h : xs.length ≤ ij.1
  · rw [coeff_outside f xs ij.1 h, zero_mul]
  · rw [coeff_outside f ys ij.2 (by omega), mul_zero]

/-- The six growth steps cover every convolution admitted by the native API. -/
theorem dimensions_spec (n : Nat) (hn : n ≤ 256) :
    ∃ d, KaratsubaImpl.dimensions 6 n = KaratsubaImpl.Dimensions.Size d (4*2^d) ∧ n ≤ 4*2^d := by
  have certificate : ∀ n : Fin 257, ∃ d : Fin 7,
      KaratsubaImpl.dimensions 6 n.val = KaratsubaImpl.Dimensions.Size d.val (4*2^d.val) ∧
      n.val ≤ 4*2^d.val := by decide +kernel
  obtain ⟨d, hd⟩ := certificate ⟨n, by omega⟩
  exact ⟨d.val, hd⟩

theorem multiply_sized_spec (d : Nat) (xs ys : Scalars) (hx : Canon xs) (hy : Canon ys)
    (lx : xs.length ≤ 4*2^d) (ly : ys.length ≤ 4*2^d) :
    Canon (KaratsubaImpl.multiply_sized (.Size d (4*2^d)) xs ys) ∧
    poly mr (KaratsubaImpl.multiply_sized (.Size d (4*2^d)) xs ys) = poly mr xs * poly mr ys ∧
    (KaratsubaImpl.multiply_sized (.Size d (4*2^d)) xs ys).length = xs.length + ys.length - 1 := by
  obtain ⟨hc, hp, hl⟩ := convolution_spec d xs ys hx hy lx ly
  simp only [KaratsubaImpl.multiply_sized, KaratsubaImpl.take, length_eq]
  refine ⟨canon_take _ _ hc, ?_, ?_⟩
  · rw [take_preserves, hp]
    intro k hk
    rw [hp]
    exact product_outside mr xs ys k hk
  · rw [List.length_take, hl, Nat.min_eq_left (by omega)]

theorem multiply_spec (xs ys : Scalars) (hx : Canon xs) (hy : Canon ys)
    (lx : xs.length ≤ 256) (ly : ys.length ≤ 256) :
    Canon (KaratsubaImpl.multiply xs ys) ∧
    poly mr (KaratsubaImpl.multiply xs ys) = poly mr xs * poly mr ys := by
  cases xs with
  | nil => cases ys <;> simp [KaratsubaImpl.multiply]
  | cons a xs =>
    cases ys with
    | nil => simp [KaratsubaImpl.multiply]
    | cons b ys =>
      obtain ⟨d, hd, hn⟩ := dimensions_spec (max (a::xs).length (b::ys).length) (by omega)
      simp only [KaratsubaImpl.multiply, length_eq]
      rw [show max (1+xs.length) (1+ys.length) = max (a::xs).length (b::ys).length by simp; omega, hd]
      exact ⟨(multiply_sized_spec d _ _ hx hy (by omega) (by omega)).1,
        (multiply_sized_spec d _ _ hx hy (by omega) (by omega)).2.1⟩

theorem multiply_length (xs ys : Scalars) (hx : Canon xs) (hy : Canon ys)
    (lx : 0 < xs.length ∧ xs.length ≤ 256) (ly : 0 < ys.length ∧ ys.length ≤ 256) :
    (KaratsubaImpl.multiply xs ys).length = xs.length + ys.length - 1 := by
  cases xs with
  | nil => simp at lx
  | cons a xs =>
    cases ys with
    | nil => simp at ly
    | cons b ys =>
      obtain ⟨d, hd, hn⟩ := dimensions_spec (max (a::xs).length (b::ys).length) (by omega)
      simp only [KaratsubaImpl.multiply, length_eq]
      rw [show max (1+xs.length) (1+ys.length) = max (a::xs).length (b::ys).length by simp; omega, hd]
      exact (multiply_sized_spec d _ _ hx hy (by omega) (by omega)).2.2

end
end MultiplyPolynomial
