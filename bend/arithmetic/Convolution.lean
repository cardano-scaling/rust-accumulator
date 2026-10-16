import OriginalPolynomial
open ScalarImpl ScalarLaws Field Polynomial PolynomialModel ListOperations
namespace Convolution
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

syntax "scalar_bound" : tactic
macro_rules
  | `(tactic| scalar_bound) => `(tactic|
      with_reducible first
      | assumption
      | (apply And.intro <;> scalar_bound)
      | exact zero_valid
      | exact one_valid
      | (apply add_closed <;> scalar_bound)
      | (apply sub_closed <;> scalar_bound)
      | (apply montgomery_closed <;> scalar_bound))

theorem prepared_digits (a b : Scalar) :
    multiply (Multiplier.Prepared (digits a)) b = montgomery a b := rfl

theorem leaf_spec (x y : KaratsubaImpl.Four)
    (hx : Canon (KaratsubaImpl.unfour x)) (hy : Canon (KaratsubaImpl.unfour y)) :
    Canon (KaratsubaImpl.leaf x y) ∧
    poly mr (KaratsubaImpl.leaf x y) = poly mr (KaratsubaImpl.unfour x) * poly mr (KaratsubaImpl.unfour y) := by
  cases x; cases y
  rename_i a0 a1 a2 a3 b0 b1 b2 b3
  simp only [KaratsubaImpl.unfour, canon_cons, canon_nil, and_true] at hx hy
  obtain ⟨ha0, ha1, ha2, ha3⟩ := hx
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hy
  constructor
  · simp only [KaratsubaImpl.leaf, prepared_digits, canon_cons, canon_nil, and_true]
    scalar_bound
  · simp only [KaratsubaImpl.leaf, KaratsubaImpl.unfour, prepared_digits, poly_cons, poly_nil]
    simp (disch := scalar_bound) only [mr_add, mr_sub, mr_mul, C_add, C_sub, C_mul]
    ring

theorem four_spec (xs : Scalars) (hx : Canon xs) (hn : xs.length ≤ 4) :
    Canon (KaratsubaImpl.unfour (KaratsubaImpl.four xs)) ∧
    poly mr (KaratsubaImpl.unfour (KaratsubaImpl.four xs)) = poly mr xs := by
  rcases xs with _ | ⟨a, xs⟩
  · simp [KaratsubaImpl.four, KaratsubaImpl.unfour, poly]
  rcases xs with _ | ⟨b, xs⟩
  · simpa [KaratsubaImpl.four, KaratsubaImpl.unfour, poly] using hx
  rcases xs with _ | ⟨c, xs⟩
  · simpa [KaratsubaImpl.four, KaratsubaImpl.unfour, poly] using hx
  rcases xs with _ | ⟨d, xs⟩
  · simpa [KaratsubaImpl.four, KaratsubaImpl.unfour, poly] using hx
  have ht : xs = [] := by
    cases xs with
    | nil => rfl
    | cons e rest => simp only [List.length_cons] at hn; omega
  subst xs
  simpa [KaratsubaImpl.four, KaratsubaImpl.unfour] using hx

theorem zeros_spec (n : Nat) : Canon (KaratsubaImpl.zeros n) ∧ poly mr (KaratsubaImpl.zeros n) = 0 ∧
    (KaratsubaImpl.zeros n).length = n := by
  induction n with
  | zero => simp [KaratsubaImpl.zeros]
  | succ n ih => simpa [KaratsubaImpl.zeros, List.replicate_succ, poly] using ih

/-- Empty blocks skip arithmetic; missing coefficients still mean zero. -/
theorem leaf_lists_spec (xs ys : Scalars) (hx : Canon xs) (hy : Canon ys)
    (lx : xs.length ≤ 4) (ly : ys.length ≤ 4) :
    Canon (KaratsubaImpl.leaf_lists xs ys) ∧
    poly mr (KaratsubaImpl.leaf_lists xs ys) = poly mr xs * poly mr ys ∧
    (KaratsubaImpl.leaf_lists xs ys).length = 7 := by
  cases xs with
  | nil => cases ys <;> simpa [KaratsubaImpl.leaf_lists] using zeros_spec 7
  | cons a xs =>
    cases ys with
    | nil => simpa [KaratsubaImpl.leaf_lists] using zeros_spec 7
    | cons b ys =>
      obtain ⟨hxc, hxp⟩ := four_spec (a::xs) hx lx
      obtain ⟨hyc, hyp⟩ := four_spec (b::ys) hy ly
      obtain ⟨hc, hp⟩ := leaf_spec _ _ hxc hyc
      simp only [KaratsubaImpl.leaf_lists]
      refine ⟨hc, ?_, ?_⟩
      · rw [hp, hxp, hyp]
      · cases KaratsubaImpl.four (a::xs); cases KaratsubaImpl.four (b::ys); rfl

theorem add_length (xs ys : Scalars) :
    (KaratsubaImpl.add xs ys).length = max xs.length ys.length := by
  fun_induction KaratsubaImpl.add xs ys <;> simp_all [KaratsubaImpl.add, Nat.succ_max_succ]

theorem negate_length (xs : Scalars) : (KaratsubaImpl.negate xs).length = xs.length := by
  induction xs <;> simp_all [KaratsubaImpl.negate]

theorem sub_length (xs ys : Scalars) :
    (KaratsubaImpl.sub xs ys).length = max xs.length ys.length := by
  fun_induction KaratsubaImpl.sub xs ys <;> simp_all [KaratsubaImpl.sub, negate_length, Nat.succ_max_succ]

theorem cross_length (xs ys zs : Scalars) :
    (KaratsubaImpl.cross xs ys zs).length = max xs.length (max ys.length zs.length) := by
  fun_induction KaratsubaImpl.cross xs ys zs <;>
    simp_all [KaratsubaImpl.cross, negate_length, sub_length, Nat.succ_max_succ]

theorem shift_add_length (n : Nat) (xs ys : Scalars) :
    (KaratsubaImpl.shift_add n xs ys).length = max xs.length (n + ys.length) := by
  induction n generalizing xs with
  | zero => simp [KaratsubaImpl.shift_add, add_length]
  | succ n ih => cases xs <;> simp_all [KaratsubaImpl.shift_add, Nat.succ_max_succ, Nat.succ_add]

/-- Every recursion level is an ordinary polynomial product in Montgomery representation. -/
theorem convolution_spec (depth : Nat) (xs ys : Scalars)
    (hx : Canon xs) (hy : Canon ys)
    (lx : xs.length ≤ 4*2^depth) (ly : ys.length ≤ 4*2^depth) :
    Canon (KaratsubaImpl.convolution depth (4*2^depth) xs ys) ∧
    poly mr (KaratsubaImpl.convolution depth (4*2^depth) xs ys) = poly mr xs * poly mr ys ∧
    (KaratsubaImpl.convolution depth (4*2^depth) xs ys).length = 2*(4*2^depth)-1 := by
  induction depth generalizing xs ys with
  | zero =>
    simpa only [KaratsubaImpl.convolution, pow_zero, Nat.mul_one] using
      leaf_lists_spec xs ys hx hy (by simpa using lx) (by simpa using ly)
  | succ depth ih =>
    let w := 4*2^depth
    have wpos : 0 < w := by dsimp [w]; positivity
    have width : 4*2^(depth+1) = 2*w := by dsimp [w]; rw [pow_succ]; omega
    have half : (2*w)/2 = w := by omega
    have ax := canon_take xs w hx
    have ay := canon_take ys w hy
    have bx := canon_drop xs w hx
    have bys := canon_drop ys w hy
    have la : (xs.take w).length ≤ w := by simp
    have lb : (ys.take w).length ≤ w := by simp
    have lc : (xs.drop w).length ≤ w := by simp only [List.length_drop]; omega
    have ld : (ys.drop w).length ≤ w := by simp only [List.length_drop]; omega
    obtain ⟨h0, p0, l0⟩ := ih (xs.take w) (ys.take w) ax ay la lb
    obtain ⟨h2, p2, l2⟩ := ih (xs.drop w) (ys.drop w) bx bys lc ld
    obtain ⟨hax, pax⟩ := add_spec _ _ ax bx
    obtain ⟨hay, pay⟩ := add_spec _ _ ay bys
    obtain ⟨h1, p1, l1⟩ := ih (KaratsubaImpl.add (xs.take w) (xs.drop w))
      (KaratsubaImpl.add (ys.take w) (ys.drop w)) hax hay
      (by rw [add_length]; omega) (by rw [add_length]; omega)
    obtain ⟨hcross, pcross⟩ := cross_spec _ _ _ h1 h0 h2
    obtain ⟨hinner, pinner⟩ := shift_add_spec w _ _ hcross h2
    obtain ⟨houter, pouter⟩ := shift_add_spec w _ _ h0 hinner
    rw [width]
    simp only [KaratsubaImpl.convolution, half, KaratsubaImpl.take, KaratsubaImpl.drop]
    refine ⟨houter, ?_, ?_⟩
    · rw [pouter, pinner, pcross, p0, p1, p2, pax, pay]
      have split_x : poly mr xs = poly mr (xs.take w) + X^w * poly mr (xs.drop w) := by
        by_cases h : w ≤ xs.length
        · exact poly_split mr xs w h
        · simp [List.take_of_length_le (by omega : xs.length ≤ w), List.drop_eq_nil_of_le (by omega : xs.length ≤ w)]
      have split_y : poly mr ys = poly mr (ys.take w) + X^w * poly mr (ys.drop w) := by
        by_cases h : w ≤ ys.length
        · exact poly_split mr ys w h
        · simp [List.take_of_length_le (by omega : ys.length ≤ w), List.drop_eq_nil_of_le (by omega : ys.length ≤ w)]
      rw [split_x, split_y]
      ring
    · rw [shift_add_length, shift_add_length, cross_length, l0, l1, l2]
      omega

end
end Convolution
