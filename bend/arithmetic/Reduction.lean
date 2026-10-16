import Montgomery
open ScalarImpl ScalarLaws Montgomery
namespace Reduction
set_option maxRecDepth 8192
set_option maxHeartbeats 200000

/-- The CIOS loop invariant: the accumulator stays below a+p. -/
theorem step_invariant (a t : Digits) (b : U32)
    (ha : bounded a) (ht : bounded t) (hb : b.toNat < radix)
    (han : decodeD a < p) (htn : decodeD t < decodeD a + p) :
    ∃ m : Nat,
      radix * decodeD (step a b t) = decodeD t + decodeD a * b.toNat + m*p ∧
      decodeD (step a b t) < decodeD a + p ∧ bounded (step a b t) := by
  let m := W.band (W.sub 0 (low (t.d0.toNat + product a.d0 b))) 8388607
  have h := step_exact a t b ha ht hb han
  change radix * decodeD (step a b t) = decodeD t + decodeD a * b.toNat + m.toNat*p ∧ _ at h
  have hm := (cancellation (t.d0.toNat + product a.d0 b)).1
  change m.toNat < radix at hm
  refine ⟨m.toNat, h.1, ?_, h.2⟩
  have hab : decodeD a * b.toNat ≤ decodeD a * (radix-1) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [radix, p] at *
  omega

/-- All twelve executable steps preserve the Montgomery relation and range. -/
theorem montgomery_digits_exact (a b : Digits)
    (ha : bounded a) (hb : bounded b) (han : decodeD a < p) :
    decodeD (montgomery_digits a b) < decodeD a + p ∧
    bounded (montgomery_digits a b) ∧
    ∃ k : Nat, decodeD (montgomery_digits a b) * 2^276 = decodeD a * decodeD b + k*p := by
  cases b
  rename_i b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
  simp only [bounded] at hb
  rcases hb with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11⟩
  let t0 := digits zero
  have ht0 : bounded t0 := (digits_exact zero).2
  have hn0 : decodeD t0 < decodeD a + p := by
    have hz : decodeD t0 = 0 := by decide +kernel
    have hp : 0 < p := by decide +kernel
    omega
  let t1 := step a b0 t0
  obtain ⟨m0, e0, hn1, ht1⟩ := step_invariant a t0 b0 ha ht0 hb0 han hn0
  change radix * decodeD t1 = decodeD t0 + decodeD a * b0.toNat + m0*p at e0
  let t2 := step a b1 t1
  obtain ⟨m1, e1, hn2, ht2⟩ := step_invariant a t1 b1 ha ht1 hb1 han hn1
  change radix * decodeD t2 = decodeD t1 + decodeD a * b1.toNat + m1*p at e1
  let t3 := step a b2 t2
  obtain ⟨m2, e2, hn3, ht3⟩ := step_invariant a t2 b2 ha ht2 hb2 han hn2
  change radix * decodeD t3 = decodeD t2 + decodeD a * b2.toNat + m2*p at e2
  let t4 := step a b3 t3
  obtain ⟨m3, e3, hn4, ht4⟩ := step_invariant a t3 b3 ha ht3 hb3 han hn3
  change radix * decodeD t4 = decodeD t3 + decodeD a * b3.toNat + m3*p at e3
  let t5 := step a b4 t4
  obtain ⟨m4, e4, hn5, ht5⟩ := step_invariant a t4 b4 ha ht4 hb4 han hn4
  change radix * decodeD t5 = decodeD t4 + decodeD a * b4.toNat + m4*p at e4
  let t6 := step a b5 t5
  obtain ⟨m5, e5, hn6, ht6⟩ := step_invariant a t5 b5 ha ht5 hb5 han hn5
  change radix * decodeD t6 = decodeD t5 + decodeD a * b5.toNat + m5*p at e5
  let t7 := step a b6 t6
  obtain ⟨m6, e6, hn7, ht7⟩ := step_invariant a t6 b6 ha ht6 hb6 han hn6
  change radix * decodeD t7 = decodeD t6 + decodeD a * b6.toNat + m6*p at e6
  let t8 := step a b7 t7
  obtain ⟨m7, e7, hn8, ht8⟩ := step_invariant a t7 b7 ha ht7 hb7 han hn7
  change radix * decodeD t8 = decodeD t7 + decodeD a * b7.toNat + m7*p at e7
  let t9 := step a b8 t8
  obtain ⟨m8, e8, hn9, ht9⟩ := step_invariant a t8 b8 ha ht8 hb8 han hn8
  change radix * decodeD t9 = decodeD t8 + decodeD a * b8.toNat + m8*p at e8
  let t10 := step a b9 t9
  obtain ⟨m9, e9, hn10, ht10⟩ := step_invariant a t9 b9 ha ht9 hb9 han hn9
  change radix * decodeD t10 = decodeD t9 + decodeD a * b9.toNat + m9*p at e9
  let t11 := step a b10 t10
  obtain ⟨m10, e10, hn11, ht11⟩ := step_invariant a t10 b10 ha ht10 hb10 han hn10
  change radix * decodeD t11 = decodeD t10 + decodeD a * b10.toNat + m10*p at e10
  let t12 := step a b11 t11
  obtain ⟨m11, e11, hn12, ht12⟩ := step_invariant a t11 b11 ha ht11 hb11 han hn11
  change radix * decodeD t12 = decodeD t11 + decodeD a * b11.toNat + m11*p at e11
  change decodeD t12 < decodeD a + p ∧ bounded t12 ∧ ∃ k, decodeD t12 * 2^276 = _
  refine ⟨hn12, ht12, m0 + 2^23*m1 + 2^46*m2 + 2^69*m3 + 2^92*m4 + 2^115*m5 + 2^138*m6 + 2^161*m7 + 2^184*m8 + 2^207*m9 + 2^230*m10 + 2^253*m11, ?_⟩
  change decodeD t12 * 2^276 = decodeD a * (b0.toNat + 2^23*b1.toNat + 2^46*b2.toNat + 2^69*b3.toNat + 2^92*b4.toNat + 2^115*b5.toNat + 2^138*b6.toNat + 2^161*b7.toNat + 2^184*b8.toNat + 2^207*b9.toNat + 2^230*b10.toNat + 2^253*b11.toNat) + (m0 + 2^23*m1 + 2^46*m2 + 2^69*m3 + 2^92*m4 + 2^115*m5 + 2^138*m6 + 2^161*m7 + 2^184*m8 + 2^207*m9 + 2^230*m10 + 2^253*m11)*p
  simp only [Nat.mul_add]
  rw [Nat.mul_left_comm (decodeD a) (2^23) b1.toNat]
  rw [Nat.mul_left_comm (decodeD a) (2^46) b2.toNat]
  rw [Nat.mul_left_comm (decodeD a) (2^69) b3.toNat]
  rw [Nat.mul_left_comm (decodeD a) (2^92) b4.toNat]
  rw [Nat.mul_left_comm (decodeD a) (2^115) b5.toNat]
  rw [Nat.mul_left_comm (decodeD a) (2^138) b6.toNat]
  rw [Nat.mul_left_comm (decodeD a) (2^161) b7.toNat]
  rw [Nat.mul_left_comm (decodeD a) (2^184) b8.toNat]
  rw [Nat.mul_left_comm (decodeD a) (2^207) b9.toNat]
  rw [Nat.mul_left_comm (decodeD a) (2^230) b10.toNat]
  rw [Nat.mul_left_comm (decodeD a) (2^253) b11.toNat]
  have hz : decodeD t0 = 0 := by decide +kernel
  rw [hz] at e0
  clear ha han ht0 ht1 ht2 ht3 ht4 ht5 ht6 ht7 ht8 ht9 ht10 ht11 ht12 hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7 hn8 hn9 hn10 hn11 hn12 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11
  simp only [radix, p, Nat.add_mul, Nat.mul_assoc] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ⊢
  omega

def inverseR : Nat := 33588544069962898116296588901410757386977461076994467378710251184785742012392

theorem cancel_radix (t u k : Nat) (h : t * 2^276 = u + k*p) :
    t % p = (u * inverseR) % p := by
  have hi : (2^276 * inverseR) % p = 1 := by
    have certificate : 2^276 * inverseR = 77775258210554975085791442866881447937389542642247331934156930172538362453135720447 * p + 1 := by decide +kernel
    rw [certificate, Nat.add_mod, Nat.mul_mod_left]
    simp only [Nat.zero_add]
    exact Nat.mod_eq_of_lt (by decide +kernel)
  calc
    t % p = (t * (2^276 * inverseR)) % p := by rw [Nat.mul_mod, hi, Nat.mul_one, Nat.mod_mod]
    _ = ((t * 2^276) * inverseR) % p := by rw [Nat.mul_assoc]
    _ = ((u + k*p) * inverseR) % p := by rw [h]
    _ = (u * inverseR) % p := by
      rw [Nat.add_mul, Nat.add_mod]
      have hz : (k*p*inverseR) % p = 0 := by
        rw [Nat.mul_right_comm k p inverseR, Nat.mul_mod_left]
      rw [hz, Nat.add_zero, Nat.mod_mod]

/-- Montgomery multiplication returns the canonical residue a*b/R modulo p. -/
theorem montgomery_exact (a b : Scalar) (ha : decode a < p) (_hb : decode b < p) :
    decode (montgomery a b) = (decode a * decode b * inverseR) % p := by
  have da := digits_exact a
  have db := digits_exact b
  obtain ⟨bound, digitsBound, k, relation⟩ := montgomery_digits_exact (digits a) (digits b)
    da.2 db.2 (by simpa only [da.1] using ha)
  rw [da.1, db.1] at relation
  rw [da.1] at bound
  have hp : 2*p < 2^256 := by decide +kernel
  have repack := from_digits_exact (montgomery_digits (digits a) (digits b)) digitsBound (by omega)
  unfold montgomery
  rw [reduce_exact _ (by omega), repack]
  exact cancel_radix _ _ k relation

end Reduction
