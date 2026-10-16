import ScalarLaws
open ScalarImpl ScalarLaws
namespace Montgomery
set_option maxRecDepth 8192
set_option maxHeartbeats 200000

/-- The radix used by the executable Bend arithmetic. -/
def radix : Nat := 8388608

theorem join_nat (a b : U32) (k : Nat) (hk : k ≤ 32) (ha : a.toNat < 2^k) :
    (a ||| (b <<< k)).toNat = a.toNat + (b.toNat % 2^(32-k)) * 2^k := by
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have he : 2^32 = 2^(32-k) * 2^k := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [he, Nat.mul_mod_mul_right, Nat.or_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq]
  omega

theorem mask_nat (a : U32) : (a &&& 8388607).toNat = a.toNat % radix := by
  change a.toNat &&& (2^23-1) = a.toNat % 2^23
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem digit_nat (a : U32) : digit a = a.toNat % radix := mask_nat a

theorem low_nat (a : Nat) : (low a).toNat = a % radix := by
  change (a % 8388608) % 2^32 = _
  unfold radix
  omega

theorem high_nat (n : Nat) : high n = n / radix := rfl

def decodeD (x : Digits) : Nat :=
  x.d0.toNat + 2^23*x.d1.toNat + 2^46*x.d2.toNat + 2^69*x.d3.toNat +
  2^92*x.d4.toNat + 2^115*x.d5.toNat + 2^138*x.d6.toNat + 2^161*x.d7.toNat +
  2^184*x.d8.toNat + 2^207*x.d9.toNat + 2^230*x.d10.toNat + 2^253*x.d11.toNat

def bounded (x : Digits) : Prop :=
  x.d0.toNat < radix ∧ x.d1.toNat < radix ∧ x.d2.toNat < radix ∧
  x.d3.toNat < radix ∧ x.d4.toNat < radix ∧ x.d5.toNat < radix ∧
  x.d6.toNat < radix ∧ x.d7.toNat < radix ∧ x.d8.toNat < radix ∧
  x.d9.toNat < radix ∧ x.d10.toNat < radix ∧ x.d11.toNat < radix

theorem digits_exact (x : Scalar) : decodeD (digits x) = decode x ∧ bounded (digits x) := by
  cases x
  rename_i a b c d e f g h
  have := a.isLt; have := b.isLt; have := c.isLt; have := d.isLt
  have := e.isLt; have := f.isLt; have := g.isLt; have := h.isLt
  simp only [decodeD, decode, bounded, digits, W.band, W.bor, W.shl, W.shr]
  have j0 := join_nat (a >>> 23) b 9 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j1 := join_nat (b >>> 14) c 18 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j2 := join_nat (c >>> 28) d 4 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j3 := join_nat (d >>> 19) e 13 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j4 := join_nat (e >>> 10) f 22 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j5 := join_nat (f >>> 24) g 8 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j6 := join_nat (g >>> 15) h 17 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  simp only [mask_nat, j0, j1, j2, j3, j4, j5, j6, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, radix]
  omega

/-- Repacking loses no information for bounded digits below 2^256. -/
theorem from_digits_exact (x : Digits) (hx : bounded x) (hn : decodeD x < 2^256) :
    decode (from_digits x) = decodeD x := by
  cases x
  rename_i d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11
  simp only [bounded, radix] at hx
  simp only [decodeD] at hn ⊢
  simp only [from_digits, decode, W.bor, W.shl, W.shr]
  have j0 := join_nat d0 d1 23 (by decide) (by omega)
  have j1 := join_nat (d1 >>> 9) d2 14 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j2 := join_nat (d2 >>> 18) d3 5 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j3 := join_nat (d2 >>> 18 ||| d3 <<< 5) d4 28 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, j2]; omega)
  have j4 := join_nat (d4 >>> 4) d5 19 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j5 := join_nat (d5 >>> 13) d6 10 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j6 := join_nat (d6 >>> 22) d7 1 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j7 := join_nat (d6 >>> 22 ||| d7 <<< 1) d8 24 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, j6]; omega)
  have j8 := join_nat (d8 >>> 8) d9 15 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j9 := join_nat (d9 >>> 17) d10 6 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega)
  have j10 := join_nat (d9 >>> 17 ||| d10 <<< 6) d11 29 (by decide) (by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, j9]; omega)
  simp only [j0, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- The cancellation digit annihilates the low radix digit because p[0] = 1. -/
theorem cancellation (s : Nat) :
    let m := W.band (W.sub 0 (low s)) 8388607
    m.toNat < radix ∧ (s + m.toNat) % radix = 0 := by
  simp only [W.band, W.sub, mask_nat, BitVec.toNat_sub, low_nat]
  have hz : (0 : U32).toNat = 0 := rfl
  rw [hz]
  simp only [radix]
  omega


theorem product_exact (a b : U32) (ha : a.toNat < radix) (hb : b.toNat < radix) :
    product a b = a.toNat * b.toNat := by
  simp only [product, digit_nat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rfl

theorem product_bound (a b : U32) (ha : a.toNat < radix) (hb : b.toNat < radix) :
    product a b ≤ (radix-1)*(radix-1) := by
  rw [product_exact a b ha hb]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- One CIOS step is exact division by the radix after adding a multiple of p. -/
theorem step_exact (a t : Digits) (b : U32)
    (ha : bounded a) (ht : bounded t) (hb : b.toNat < radix) (han : decodeD a < p) :
    let m := W.band (W.sub 0 (low (t.d0.toNat + product a.d0 b))) 8388607
    radix * decodeD (step a b t) = decodeD t + decodeD a * b.toNat + m.toNat * p ∧
    bounded (step a b t) := by
  cases a; cases t
  rename_i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11
  simp only [bounded] at ha ht
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11⟩
  rcases ht with ⟨ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11⟩
  have htop : a11.toNat ≤ 3 := by
    simp only [decodeD, p] at han
    omega
  let s0 := t0.toNat + product a0 b
  let m := W.band (W.sub 0 (low s0)) 8388607
  have hm := cancellation s0
  change m.toNat < radix ∧ (s0 + m.toNat) % radix = 0 at hm
  let c0 := high (s0 + m.toNat)
  let s1 := t1.toNat + product a1 b + product 8388096 m + c0
  let s2 := t2.toNat + product a2 b + product 8126463 m + high s1
  let s3 := t3.toNat + product a3 b + product 8385247 m + high s2
  let s4 := t4.toNat + product a4 b + product 5914671 m + high s3
  let s5 := t5.toNat + product a5 b + product 43639 m + high s4
  let s6 := t6.toNat + product a6 b + product 157814 m + high s5
  let s7 := t7.toNat + product a7 b + product 1895428 m + high s6
  let s8 := t8.toNat + product a8 b + product 8210483 m + high s7
  let s9 := t9.toNat + product a9 b + product 2511674 m + high s8
  let s10 := t10.toNat + product a10 b + product 5224093 m + high s9
  let s11 := t11.toNat + product a11 b + product 3 m + high s10
  have ab0 := product_bound a0 b ha0 hb
  have ab1 := product_bound a1 b ha1 hb
  have ab2 := product_bound a2 b ha2 hb
  have ab3 := product_bound a3 b ha3 hb
  have ab4 := product_bound a4 b ha4 hb
  have ab5 := product_bound a5 b ha5 hb
  have ab6 := product_bound a6 b ha6 hb
  have ab7 := product_bound a7 b ha7 hb
  have ab8 := product_bound a8 b ha8 hb
  have ab9 := product_bound a9 b ha9 hb
  have ab10 := product_bound a10 b ha10 hb
  have ab11 := product_bound a11 b ha11 hb
  have mp1 := product_exact 8388096 m (by decide) hm.1
  change product 8388096 m = 8388096 * m.toNat at mp1
  have mp2 := product_exact 8126463 m (by decide) hm.1
  change product 8126463 m = 8126463 * m.toNat at mp2
  have mp3 := product_exact 8385247 m (by decide) hm.1
  change product 8385247 m = 8385247 * m.toNat at mp3
  have mp4 := product_exact 5914671 m (by decide) hm.1
  change product 5914671 m = 5914671 * m.toNat at mp4
  have mp5 := product_exact 43639 m (by decide) hm.1
  change product 43639 m = 43639 * m.toNat at mp5
  have mp6 := product_exact 157814 m (by decide) hm.1
  change product 157814 m = 157814 * m.toNat at mp6
  have mp7 := product_exact 1895428 m (by decide) hm.1
  change product 1895428 m = 1895428 * m.toNat at mp7
  have mp8 := product_exact 8210483 m (by decide) hm.1
  change product 8210483 m = 8210483 * m.toNat at mp8
  have mp9 := product_exact 2511674 m (by decide) hm.1
  change product 2511674 m = 2511674 * m.toNat at mp9
  have mp10 := product_exact 5224093 m (by decide) hm.1
  change product 5224093 m = 5224093 * m.toNat at mp10
  have mp11 := product_exact 3 m (by decide) hm.1
  change product 3 m = 3 * m.toNat at mp11
  have atop : product a11 b ≤ 3 * (radix-1) := by
    rw [product_exact a11 b ha11 hb]
    exact Nat.mul_le_mul htop (by omega)
  have bound0 : s0 < 2^48 ∧ c0 < 2*radix := by
    dsimp only [s0, c0]
    simp only [high_nat, radix] at *
    omega
  have bound1 : s1 < 2^48 ∧ high s1 < 2*radix := by
    dsimp only [s1]
    rw [mp1]
    simp only [high_nat, radix] at *
    omega
  have bound2 : s2 < 2^48 ∧ high s2 < 2*radix := by
    dsimp only [s2]
    rw [mp2]
    simp only [high_nat, radix] at *
    omega
  have bound3 : s3 < 2^48 ∧ high s3 < 2*radix := by
    dsimp only [s3]
    rw [mp3]
    simp only [high_nat, radix] at *
    omega
  have bound4 : s4 < 2^48 ∧ high s4 < 2*radix := by
    dsimp only [s4]
    rw [mp4]
    simp only [high_nat, radix] at *
    omega
  have bound5 : s5 < 2^48 ∧ high s5 < 2*radix := by
    dsimp only [s5]
    rw [mp5]
    simp only [high_nat, radix] at *
    omega
  have bound6 : s6 < 2^48 ∧ high s6 < 2*radix := by
    dsimp only [s6]
    rw [mp6]
    simp only [high_nat, radix] at *
    omega
  have bound7 : s7 < 2^48 ∧ high s7 < 2*radix := by
    dsimp only [s7]
    rw [mp7]
    simp only [high_nat, radix] at *
    omega
  have bound8 : s8 < 2^48 ∧ high s8 < 2*radix := by
    dsimp only [s8]
    rw [mp8]
    simp only [high_nat, radix] at *
    omega
  have bound9 : s9 < 2^48 ∧ high s9 < 2*radix := by
    dsimp only [s9]
    rw [mp9]
    simp only [high_nat, radix] at *
    omega
  have bound10 : s10 < 2^48 ∧ high s10 < 2*radix := by
    dsimp only [s10]
    rw [mp10]
    simp only [high_nat, radix] at *
    omega
  have bound11 : s11 < 2^48 ∧ high s11 < radix := by
    dsimp only [s11]
    rw [mp11]
    simp only [high_nat, radix] at *
    omega
  change radix * decodeD (Digits.D (low s1) (low s2) (low s3) (low s4) (low s5) (low s6) (low s7) (low s8) (low s9) (low s10) (low s11) (W.ofNat (high s11))) = decodeD (Digits.D t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11) + decodeD (Digits.D a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) * b.toNat + m.toNat * p ∧ bounded (Digits.D (low s1) (low s2) (low s3) (low s4) (low s5) (low s6) (low s7) (low s8) (low s9) (low s10) (low s11) (W.ofNat (high s11)))
  have top_exact : (W.ofNat (high s11)).toNat = high s11 := by
    change (high s11) % 2^32 = high s11
    apply Nat.mod_eq_of_lt
    simp only [radix] at bound11
    omega
  constructor
  · simp only [decodeD, low_nat, top_exact]
    have e0 : radix*c0 = t0.toNat + product a0 b + m.toNat := by
      dsimp only [c0, high_nat]
      simp only [radix] at hm ⊢
      change 8388608 * ((s0 + m.toNat) / 8388608) = s0 + m.toNat
      omega
    have e1 : s1 % radix + radix * high s1 = t1.toNat + product a1 b + 8388096 * m.toNat + c0 := by
      rw [← mp1]
      change s1 % radix + radix * (s1 / radix) = s1
      exact Nat.mod_add_div _ _
    have e2 : s2 % radix + radix * high s2 = t2.toNat + product a2 b + 8126463 * m.toNat + high s1 := by
      rw [← mp2]
      change s2 % radix + radix * (s2 / radix) = s2
      exact Nat.mod_add_div _ _
    have e3 : s3 % radix + radix * high s3 = t3.toNat + product a3 b + 8385247 * m.toNat + high s2 := by
      rw [← mp3]
      change s3 % radix + radix * (s3 / radix) = s3
      exact Nat.mod_add_div _ _
    have e4 : s4 % radix + radix * high s4 = t4.toNat + product a4 b + 5914671 * m.toNat + high s3 := by
      rw [← mp4]
      change s4 % radix + radix * (s4 / radix) = s4
      exact Nat.mod_add_div _ _
    have e5 : s5 % radix + radix * high s5 = t5.toNat + product a5 b + 43639 * m.toNat + high s4 := by
      rw [← mp5]
      change s5 % radix + radix * (s5 / radix) = s5
      exact Nat.mod_add_div _ _
    have e6 : s6 % radix + radix * high s6 = t6.toNat + product a6 b + 157814 * m.toNat + high s5 := by
      rw [← mp6]
      change s6 % radix + radix * (s6 / radix) = s6
      exact Nat.mod_add_div _ _
    have e7 : s7 % radix + radix * high s7 = t7.toNat + product a7 b + 1895428 * m.toNat + high s6 := by
      rw [← mp7]
      change s7 % radix + radix * (s7 / radix) = s7
      exact Nat.mod_add_div _ _
    have e8 : s8 % radix + radix * high s8 = t8.toNat + product a8 b + 8210483 * m.toNat + high s7 := by
      rw [← mp8]
      change s8 % radix + radix * (s8 / radix) = s8
      exact Nat.mod_add_div _ _
    have e9 : s9 % radix + radix * high s9 = t9.toNat + product a9 b + 2511674 * m.toNat + high s8 := by
      rw [← mp9]
      change s9 % radix + radix * (s9 / radix) = s9
      exact Nat.mod_add_div _ _
    have e10 : s10 % radix + radix * high s10 = t10.toNat + product a10 b + 5224093 * m.toNat + high s9 := by
      rw [← mp10]
      change s10 % radix + radix * (s10 / radix) = s10
      exact Nat.mod_add_div _ _
    have e11 : s11 % radix + radix * high s11 = t11.toNat + product a11 b + 3 * m.toNat + high s10 := by
      rw [← mp11]
      change s11 % radix + radix * (s11 / radix) = s11
      exact Nat.mod_add_div _ _
    rw [product_exact a0 b ha0 hb] at e0
    rw [product_exact a1 b ha1 hb] at e1
    rw [product_exact a2 b ha2 hb] at e2
    rw [product_exact a3 b ha3 hb] at e3
    rw [product_exact a4 b ha4 hb] at e4
    rw [product_exact a5 b ha5 hb] at e5
    rw [product_exact a6 b ha6 hb] at e6
    rw [product_exact a7 b ha7 hb] at e7
    rw [product_exact a8 b ha8 hb] at e8
    rw [product_exact a9 b ha9 hb] at e9
    rw [product_exact a10 b ha10 hb] at e10
    rw [product_exact a11 b ha11 hb] at e11
    clear han hb htop hm top_exact atop bound0 bound1 bound2 bound3 bound4 bound5 bound6 bound7 bound8 bound9 bound10 bound11 ab0 ab1 ab2 ab3 ab4 ab5 ab6 ab7 ab8 ab9 ab10 ab11 ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10 ha11 ht0 ht1 ht2 ht3 ht4 ht5 ht6 ht7 ht8 ht9 ht10 ht11 mp1 mp2 mp3 mp4 mp5 mp6 mp7 mp8 mp9 mp10 mp11
    simp only [Nat.add_mul, Nat.mul_assoc, p, radix, high_nat] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ⊢
    omega
  · change bounded (Digits.D (low s1) (low s2) (low s3) (low s4) (low s5) (low s6) (low s7) (low s8) (low s9) (low s10) (low s11) (W.ofNat (high s11)))
    simp only [bounded, low_nat, top_exact, radix] at *
    omega


end Montgomery
