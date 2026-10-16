import MonicProduct
import MontgomeryLeaves
open ScalarImpl ScalarLaws Field Polynomial PolynomialModel ListOperations Convolution
  MultiplyPolynomial Representation OriginalPolynomial MonicProduct
namespace ProductTree
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every supported tree is the product of all its input factors, with no loss or duplication. -/
theorem tree_spec (depth : Nat) (xs : Scalars) (hx : Canon xs)
    (hd : 2^depth ≤ xs.length) (hn : xs.length ≤ 256) :
    Canon (KaratsubaImpl.tree depth xs.length xs) ∧
    poly mr (KaratsubaImpl.tree depth xs.length xs) = factors xs ∧
    (KaratsubaImpl.tree depth xs.length xs).length = xs.length+1 := by
  induction depth generalizing xs with
  | zero => exact MontgomeryLeaves.coefficients_spec xs hx
  | succ depth ih =>
    let m := xs.length / 2
    let n := xs.length - m
    have dp : 0 < 2^depth := by positivity
    have power : 2^(depth+1) = 2*2^depth := by rw [pow_succ]; omega
    have lm : (xs.take m).length = m := by simp [m, Nat.div_le_self]
    have ln : (xs.drop m).length = n := by simp [n]
    have hm : 2^depth ≤ m := by dsimp [m]; omega
    have hn' : 2^depth ≤ n := by dsimp [n, m]; omega
    obtain ⟨hlc, hlp, hll⟩ := ih (xs.take m) (canon_take xs m hx) (by omega) (by omega)
    obtain ⟨hrc, hrp, hrl⟩ := ih (xs.drop m) (canon_drop xs m hx) (by omega) (by omega)
    rw [lm] at hlc hlp hll
    rw [ln] at hrc hrp hrl
    have hlt : (poly mr (KaratsubaImpl.tree depth m (xs.take m))).coeff m = 1 := by
      rw [hlp]
      have h := (factors_top (xs.take m)).1
      rw [lm] at h
      exact h
    have hrt : (poly mr (KaratsubaImpl.tree depth n (xs.drop m))).coeff n = 1 := by
      rw [hrp]
      have h := (factors_top (xs.drop m)).1
      rw [ln] at h
      exact h
    obtain ⟨hc, hp, hl⟩ := monic_product_spec m n _ _ hlc hrc hll hrl
      (by dsimp [m]; omega) (by dsimp [n, m]; omega) hlt hrt
    simp only [KaratsubaImpl.tree, KaratsubaImpl.take, KaratsubaImpl.drop]
    refine ⟨hc, ?_, ?_⟩
    · rw [hp, hlp, hrp, ← factors_append, List.take_append_drop]
    · rw [hl]
      dsimp [n, m]
      omega

theorem tree_dimensions_spec (n : Nat) (hn : n ≤ 256) :
    ∃ d, KaratsubaImpl.tree_dimensions 3 n = KaratsubaImpl.Dimensions.Size d (32*2^d) ∧
      (d = 0 ∨ 2^d ≤ n) := by
  have certificate : ∀ n : Fin 257, ∃ d : Fin 4,
      KaratsubaImpl.tree_dimensions 3 n.val = KaratsubaImpl.Dimensions.Size d.val (32*2^d.val) ∧
      (d.val = 0 ∨ 2^d.val ≤ n.val) := by decide +kernel
  obtain ⟨d, hd⟩ := certificate ⟨n, by omega⟩
  exact ⟨d.val, hd⟩

/-- The complete public kernel returns canonical coefficients for the input product. -/
theorem coefficients_spec (xs : Scalars) (hx : Canon xs) (hn : xs.length ≤ 256) :
    Canon (KaratsubaImpl.coefficients xs) ∧
    poly sr (KaratsubaImpl.coefficients xs) = factors xs ∧
    (KaratsubaImpl.coefficients xs).length = xs.length+1 := by
  obtain ⟨d, hd, hdepth⟩ := tree_dimensions_spec xs.length hn
  simp only [KaratsubaImpl.coefficients, length_eq, hd]
  cases d with
  | zero =>
    exact ⟨(OriginalPolynomial.coefficients_spec xs hx).1,
      (OriginalPolynomial.coefficients_spec xs hx).2, original_length xs⟩
  | succ d =>
    have hpower : 2^(d+1) ≤ xs.length := by rcases hdepth with h | h; omega; exact h
    obtain ⟨hc, hp, hl⟩ := tree_spec (d+1) xs hx hpower hn
    obtain ⟨hfc, hfp, hfl⟩ := from_spec _ hc
    simpa only [KaratsubaImpl.coefficients_sized, length_eq, Nat.add_comm] using
      And.intro hfc (And.intro (hfp.trans hp) (hfl.trans hl))

/-- Karatsuba returns exactly the original coefficient bytes for every supported canonical input. -/
theorem coefficients_equal (xs : Scalars) (hx : Canon xs) (hn : xs.length ≤ 256) :
    KaratsubaImpl.coefficients xs = PolynomialImpl.coefficients xs := by
  obtain ⟨hc, hp, hl⟩ := coefficients_spec xs hx hn
  obtain ⟨ho, hq⟩ := OriginalPolynomial.coefficients_spec xs hx
  exact poly_injective _ _ hc ho (hl.trans (original_length xs).symm) (hp.trans hq.symm)

/-- Reordering factors does not change their product. -/
theorem factors_permutation (xs ys : Scalars) (h : xs.Perm ys) : factors xs = factors ys := by
  induction h <;> simp_all [factors, mul_assoc, mul_left_comm]

/-- Coefficients commit to the multiset, preserving multiplicity but not order. -/
theorem permutation_invariant (xs ys : Scalars) (h : xs.Perm ys)
    (hx : Canon xs) (hn : xs.length ≤ 256) :
    KaratsubaImpl.coefficients xs = KaratsubaImpl.coefficients ys := by
  have hy : Canon ys := fun a ha => hx a (h.mem_iff.mpr ha)
  obtain ⟨hxc, hxp, hxl⟩ := coefficients_spec xs hx hn
  obtain ⟨hyc, hyp, hyl⟩ := coefficients_spec ys hy (by rw [← h.length_eq]; exact hn)
  apply poly_injective _ _ hxc hyc
  · rw [hxl, hyl, h.length_eq]
  · rw [hxp, hyp, factors_permutation xs ys h]

end
end ProductTree
