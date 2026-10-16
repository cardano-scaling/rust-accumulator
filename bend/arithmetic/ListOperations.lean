import PolynomialModel
open ScalarImpl ScalarLaws Field Polynomial PolynomialModel
namespace ListOperations
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- Fused coefficient addition implements polynomial addition and stays canonical. -/
theorem add_spec (xs ys : Scalars) (hx : Canon xs) (hy : Canon ys) :
    Canon (KaratsubaImpl.add xs ys) ∧
    poly mr (KaratsubaImpl.add xs ys) = poly mr xs + poly mr ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [KaratsubaImpl.add]
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
    cases ys with
    | nil => simp_all [KaratsubaImpl.add]
    | cons b ys =>
      obtain ⟨hb, hys⟩ := (canon_cons b ys).mp hy
      obtain ⟨hc, hp⟩ := ih ys hxs hys
      constructor
      · exact (canon_cons _ _).mpr ⟨add_closed a b ha hb, hc⟩
      · simp only [KaratsubaImpl.add, poly_cons, mr_add a b ha hb, C_add, hp]
        ring

theorem negate_spec (xs : Scalars) (hx : Canon xs) :
    Canon (KaratsubaImpl.negate xs) ∧ poly mr (KaratsubaImpl.negate xs) = -poly mr xs := by
  induction xs with
  | nil => simp [KaratsubaImpl.negate]
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
    obtain ⟨hc, hp⟩ := ih hxs
    constructor
    · exact (canon_cons _ _).mpr ⟨sub_closed zero a zero_valid ha, hc⟩
    · simp only [KaratsubaImpl.negate, poly_cons, mr_sub zero a zero_valid ha, mr_zero, zero_sub, C_neg, hp]
      ring

theorem sub_spec (xs ys : Scalars) (hx : Canon xs) (hy : Canon ys) :
    Canon (KaratsubaImpl.sub xs ys) ∧
    poly mr (KaratsubaImpl.sub xs ys) = poly mr xs - poly mr ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [KaratsubaImpl.sub]
    | cons b ys =>
      simpa [KaratsubaImpl.sub, KaratsubaImpl.negate] using negate_spec (b::ys) hy
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
    cases ys with
    | nil => simp_all [KaratsubaImpl.sub]
    | cons b ys =>
      obtain ⟨hb, hys⟩ := (canon_cons b ys).mp hy
      obtain ⟨hc, hp⟩ := ih ys hxs hys
      constructor
      · exact (canon_cons _ _).mpr ⟨sub_closed a b ha hb, hc⟩
      · simp only [KaratsubaImpl.sub, poly_cons, mr_sub a b ha hb, C_sub, hp]
        ring

theorem cross_spec (xs ys zs : Scalars) (hx : Canon xs) (hy : Canon ys) (hz : Canon zs) :
    Canon (KaratsubaImpl.cross xs ys zs) ∧
    poly mr (KaratsubaImpl.cross xs ys zs) = poly mr xs - poly mr ys - poly mr zs := by
  induction xs generalizing ys zs with
  | nil =>
    induction ys generalizing zs with
    | nil =>
      cases zs with
      | nil => simp [KaratsubaImpl.cross]
      | cons c zs => simpa [KaratsubaImpl.cross, KaratsubaImpl.negate] using negate_spec (c::zs) hz
    | cons b ys ih =>
      obtain ⟨hb, hys⟩ := (canon_cons b ys).mp hy
      cases zs with
      | nil => simpa [KaratsubaImpl.cross, KaratsubaImpl.negate] using negate_spec (b::ys) hy
      | cons c zs =>
        obtain ⟨hc, hzs⟩ := (canon_cons c zs).mp hz
        obtain ⟨hr, hp⟩ := ih zs hys hzs
        have hnb := sub_closed zero b zero_valid hb
        constructor
        · exact (canon_cons _ _).mpr ⟨sub_closed _ c hnb hc, hr⟩
        · simp only [KaratsubaImpl.cross, poly_cons, poly_nil, mr_sub _ c hnb hc,
            mr_sub zero b zero_valid hb, mr_zero, C_sub, C_0, hp]
          ring
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
    cases ys with
    | nil =>
      cases zs with
      | nil => simp_all [KaratsubaImpl.cross]
      | cons c zs => simpa [KaratsubaImpl.cross, KaratsubaImpl.sub] using sub_spec (a::xs) (c::zs) hx hz
    | cons b ys =>
      obtain ⟨hb, hys⟩ := (canon_cons b ys).mp hy
      cases zs with
      | nil => simpa [KaratsubaImpl.cross, KaratsubaImpl.sub] using sub_spec (a::xs) (b::ys) hx hy
      | cons c zs =>
        obtain ⟨hc, hzs⟩ := (canon_cons c zs).mp hz
        obtain ⟨hr, hp⟩ := ih ys zs hxs hys hzs
        have hab := sub_closed a b ha hb
        constructor
        · exact (canon_cons _ _).mpr ⟨sub_closed _ c hab hc, hr⟩
        · simp only [KaratsubaImpl.cross, poly_cons, mr_sub _ c hab hc,
            mr_sub a b ha hb, C_sub, hp]
          ring

theorem shift_add_spec (n : Nat) (xs ys : Scalars) (hx : Canon xs) (hy : Canon ys) :
    Canon (KaratsubaImpl.shift_add n xs ys) ∧
    poly mr (KaratsubaImpl.shift_add n xs ys) = poly mr xs + X^n * poly mr ys := by
  induction n generalizing xs with
  | zero => simpa [KaratsubaImpl.shift_add] using add_spec xs ys hx hy
  | succ n ih =>
    cases xs with
    | nil =>
      obtain ⟨hc, hp⟩ := ih [] canon_nil
      constructor
      · exact (canon_cons _ _).mpr ⟨zero_valid, hc⟩
      · simp only [KaratsubaImpl.shift_add, poly_cons, mr_zero, C_0, zero_add, hp, poly_nil, pow_succ]
        ring
    | cons a xs =>
      obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
      obtain ⟨hc, hp⟩ := ih xs hxs
      constructor
      · exact (canon_cons _ _).mpr ⟨ha, hc⟩
      · simp only [KaratsubaImpl.shift_add, poly_cons, hp, pow_succ]
        ring

end
end ListOperations
