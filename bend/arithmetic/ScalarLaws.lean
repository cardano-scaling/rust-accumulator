import ScalarImpl
open ScalarImpl
namespace ScalarLaws
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem adc_exact (a b c : U32) (hc : c.toNat ≤ 1) :
    (adc a b c).word.toNat + 4294967296 * (adc a b c).carry.toNat =
      a.toNat + b.toNat + c.toNat ∧ (adc a b c).carry.toNat ≤ 1 := by
  have ha := a.isLt
  have hb := b.isLt
  by_cases hs : (a + b).toNat < a.toNat <;>
    by_cases ht : (a + b + c).toNat < (a + b).toNat <;>
    simp only [adc, W.add, W.bor, W.lt, hs, ht, decide_true, decide_false, flag] <;> simp <;>
    simp only [BitVec.toNat_add] at * <;> omega

theorem sbb_exact (a b c : U32) (hc : c.toNat ≤ 1) :
    (sbb a b c).word.toNat + b.toNat + c.toNat =
      a.toNat + 4294967296 * (sbb a b c).carry.toNat ∧
      (sbb a b c).carry.toNat ≤ 1 := by
  have ha := a.isLt
  have hb := b.isLt
  by_cases hs : a.toNat < b.toNat <;>
    by_cases ht : (a - b).toNat < c.toNat <;>
    simp only [sbb, W.sub, W.bor, W.lt, hs, ht, decide_true, decide_false, flag] <;> simp <;>
    simp only [BitVec.toNat_sub] at * <;> omega

/-- The canonical integer represented by the eight little-endian limbs. -/
def decode (x : Scalar) : Nat :=
  x.a.toNat + 2^32 * x.b.toNat + 2^64 * x.c.toNat + 2^96 * x.d.toNat +
  2^128 * x.e.toNat + 2^160 * x.f.toNat + 2^192 * x.g.toNat + 2^224 * x.h.toNat

def p : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

theorem modulus_exact : decode modulus = p := by decide

theorem decode_lt (x : Scalar) : decode x < 2^256 := by
  have := x.a.isLt; have := x.b.isLt; have := x.c.isLt; have := x.d.isLt
  have := x.e.isLt; have := x.f.isLt; have := x.g.isLt; have := x.h.isLt
  simp only [decode]
  omega

theorem add_raw_exact (x y : Scalar) :
    decode (add_raw x y).value + 2^256 * (add_raw x y).carry.toNat = decode x + decode y ∧
    (add_raw x y).carry.toNat ≤ 1 := by
  cases x; cases y
  rename_i xa xb xc xd xe xf xg xh ya yb yc yd ye yf yg yh
  let r1 := adc xa ya (0)
  have h1 := adc_exact xa ya (0) (by decide)
  change r1.word.toNat + 4294967296 * r1.carry.toNat = xa.toNat + ya.toNat + (0 : U32).toNat ∧ r1.carry.toNat ≤ 1 at h1
  let r2 := adc xb yb (r1.carry)
  have h2 := adc_exact xb yb (r1.carry) (h1.2)
  change r2.word.toNat + 4294967296 * r2.carry.toNat = xb.toNat + yb.toNat + (r1.carry : U32).toNat ∧ r2.carry.toNat ≤ 1 at h2
  let r3 := adc xc yc (r2.carry)
  have h3 := adc_exact xc yc (r2.carry) (h2.2)
  change r3.word.toNat + 4294967296 * r3.carry.toNat = xc.toNat + yc.toNat + (r2.carry : U32).toNat ∧ r3.carry.toNat ≤ 1 at h3
  let r4 := adc xd yd (r3.carry)
  have h4 := adc_exact xd yd (r3.carry) (h3.2)
  change r4.word.toNat + 4294967296 * r4.carry.toNat = xd.toNat + yd.toNat + (r3.carry : U32).toNat ∧ r4.carry.toNat ≤ 1 at h4
  let r5 := adc xe ye (r4.carry)
  have h5 := adc_exact xe ye (r4.carry) (h4.2)
  change r5.word.toNat + 4294967296 * r5.carry.toNat = xe.toNat + ye.toNat + (r4.carry : U32).toNat ∧ r5.carry.toNat ≤ 1 at h5
  let r6 := adc xf yf (r5.carry)
  have h6 := adc_exact xf yf (r5.carry) (h5.2)
  change r6.word.toNat + 4294967296 * r6.carry.toNat = xf.toNat + yf.toNat + (r5.carry : U32).toNat ∧ r6.carry.toNat ≤ 1 at h6
  let r7 := adc xg yg (r6.carry)
  have h7 := adc_exact xg yg (r6.carry) (h6.2)
  change r7.word.toNat + 4294967296 * r7.carry.toNat = xg.toNat + yg.toNat + (r6.carry : U32).toNat ∧ r7.carry.toNat ≤ 1 at h7
  let r8 := adc xh yh (r7.carry)
  have h8 := adc_exact xh yh (r7.carry) (h7.2)
  change r8.word.toNat + 4294967296 * r8.carry.toNat = xh.toNat + yh.toNat + (r7.carry : U32).toNat ∧ r8.carry.toNat ≤ 1 at h8
  change r1.word.toNat + 4294967296 * r2.word.toNat + 18446744073709551616 * r3.word.toNat + 79228162514264337593543950336 * r4.word.toNat + 340282366920938463463374607431768211456 * r5.word.toNat + 1461501637330902918203684832716283019655932542976 * r6.word.toNat + 6277101735386680763835789423207666416102355444464034512896 * r7.word.toNat + 26959946667150639794667015087019630673637144422540572481103610249216 * r8.word.toNat + 2^256 * r8.carry.toNat = decode (Scalar.Fr xa xb xc xd xe xf xg xh) + decode (Scalar.Fr ya yb yc yd ye yf yg yh) ∧ r8.carry.toNat ≤ 1
  have hz : (0 : U32).toNat = 0 := rfl
  rw [hz] at h1
  simp only [decode] at *
  omega

theorem sub_raw_exact (x y : Scalar) :
    decode (sub_raw x y).value + decode y = decode x + 2^256 * (sub_raw x y).carry.toNat ∧
    (sub_raw x y).carry.toNat ≤ 1 := by
  cases x; cases y
  rename_i xa xb xc xd xe xf xg xh ya yb yc yd ye yf yg yh
  let r1 := sbb xa ya (0)
  have h1 := sbb_exact xa ya (0) (by decide)
  change r1.word.toNat + ya.toNat + (0 : U32).toNat = xa.toNat + 4294967296 * r1.carry.toNat ∧ r1.carry.toNat ≤ 1 at h1
  let r2 := sbb xb yb (r1.carry)
  have h2 := sbb_exact xb yb (r1.carry) (h1.2)
  change r2.word.toNat + yb.toNat + (r1.carry : U32).toNat = xb.toNat + 4294967296 * r2.carry.toNat ∧ r2.carry.toNat ≤ 1 at h2
  let r3 := sbb xc yc (r2.carry)
  have h3 := sbb_exact xc yc (r2.carry) (h2.2)
  change r3.word.toNat + yc.toNat + (r2.carry : U32).toNat = xc.toNat + 4294967296 * r3.carry.toNat ∧ r3.carry.toNat ≤ 1 at h3
  let r4 := sbb xd yd (r3.carry)
  have h4 := sbb_exact xd yd (r3.carry) (h3.2)
  change r4.word.toNat + yd.toNat + (r3.carry : U32).toNat = xd.toNat + 4294967296 * r4.carry.toNat ∧ r4.carry.toNat ≤ 1 at h4
  let r5 := sbb xe ye (r4.carry)
  have h5 := sbb_exact xe ye (r4.carry) (h4.2)
  change r5.word.toNat + ye.toNat + (r4.carry : U32).toNat = xe.toNat + 4294967296 * r5.carry.toNat ∧ r5.carry.toNat ≤ 1 at h5
  let r6 := sbb xf yf (r5.carry)
  have h6 := sbb_exact xf yf (r5.carry) (h5.2)
  change r6.word.toNat + yf.toNat + (r5.carry : U32).toNat = xf.toNat + 4294967296 * r6.carry.toNat ∧ r6.carry.toNat ≤ 1 at h6
  let r7 := sbb xg yg (r6.carry)
  have h7 := sbb_exact xg yg (r6.carry) (h6.2)
  change r7.word.toNat + yg.toNat + (r6.carry : U32).toNat = xg.toNat + 4294967296 * r7.carry.toNat ∧ r7.carry.toNat ≤ 1 at h7
  let r8 := sbb xh yh (r7.carry)
  have h8 := sbb_exact xh yh (r7.carry) (h7.2)
  change r8.word.toNat + yh.toNat + (r7.carry : U32).toNat = xh.toNat + 4294967296 * r8.carry.toNat ∧ r8.carry.toNat ≤ 1 at h8
  change r1.word.toNat + 4294967296 * r2.word.toNat + 18446744073709551616 * r3.word.toNat + 79228162514264337593543950336 * r4.word.toNat + 340282366920938463463374607431768211456 * r5.word.toNat + 1461501637330902918203684832716283019655932542976 * r6.word.toNat + 6277101735386680763835789423207666416102355444464034512896 * r7.word.toNat + 26959946667150639794667015087019630673637144422540572481103610249216 * r8.word.toNat + decode (Scalar.Fr ya yb yc yd ye yf yg yh) = decode (Scalar.Fr xa xb xc xd xe xf xg xh) + 2^256 * r8.carry.toNat ∧ r8.carry.toNat ≤ 1
  have hz : (0 : U32).toNat = 0 := rfl
  rw [hz] at h1
  simp only [decode] at *
  omega


/-- Borrow is exactly unsigned integer comparison, including noncanonical inputs. -/
theorem borrow_exact (x y : Scalar) :
    borrowed (sub_raw x y) = decide (decode x < decode y) := by
  have h := sub_raw_exact x y
  have hx := decode_lt x
  have hy := decode_lt y
  have hr := decode_lt (sub_raw x y).value
  have hb : borrowed (sub_raw x y) = decide ((sub_raw x y).carry.toNat = 1) := by
    generalize sub_raw x y = r
    cases r
    apply Bool.eq_iff_iff.mpr
    simp only [borrowed, W.eq, beq_iff_eq, decide_eq_true_eq]
    exact BitVec.toNat_inj.symm
  rw [hb]
  congr 1
  apply propext
  omega

/-- Validation accepts exactly the canonical field encodings. -/
theorem valid_exact (x : Scalar) : valid x = decide (decode x < p) := by
  simpa only [valid, modulus_exact] using borrow_exact x modulus

theorem value_projection (r : Raw) : value r = r.value := by cases r; rfl

/-- One conditional subtraction computes the canonical residue below 2p. -/
theorem reduce_exact (x : Scalar) (hx : decode x < 2*p) :
    decode (reduce x) = decode x % p := by
  have h := sub_raw_exact x modulus
  rw [modulus_exact] at h
  have hr := decode_lt (sub_raw x modulus).value
  have hb := borrow_exact x modulus
  rw [modulus_exact] at hb
  simp only [reduce]
  rw [hb]
  by_cases hlt : decode x < p
  · simp only [hlt, decide_true, select]
    exact (Nat.mod_eq_of_lt hlt).symm
  · simp only [hlt, decide_false, select, value_projection]
    have hp : 0 < p ∧ 2*p < 2^256 := by decide
    have hx' := decode_lt x
    have hc : (sub_raw x modulus).carry.toNat = 0 := by omega
    simp only [hc, Nat.mul_zero, Nat.add_zero] at h
    simp only [p] at *
    omega

/-- Addition cannot overflow the eight limbs for canonical operands. -/
theorem add_exact (x y : Scalar) (hx : decode x < p) (hy : decode y < p) :
    decode (add x y) = (decode x + decode y) % p := by
  have h := add_raw_exact x y
  have hr := decode_lt (add_raw x y).value
  have hp : 2*p < 2^256 := by decide
  have hc : (add_raw x y).carry.toNat = 0 := by omega
  have he : decode (add_raw x y).value = decode x + decode y := by omega
  unfold add
  rw [value_projection, reduce_exact _ (by omega), he]

/-- Subtraction restores p after borrow and returns the canonical difference. -/
theorem sub_exact (x y : Scalar) (hx : decode x < p) (hy : decode y < p) :
    decode (sub x y) = (decode x + p - decode y) % p := by
  have h := sub_raw_exact x y
  have hr := decode_lt (sub_raw x y).value
  have hp : 0 < p ∧ 2*p < 2^256 := by decide
  have ha := add_raw_exact (sub_raw x y).value modulus
  have har := decode_lt (add_raw (sub_raw x y).value modulus).value
  rw [modulus_exact] at ha
  have hb := borrow_exact x y
  simp only [sub]
  rw [hb]
  by_cases hlt : decode x < decode y
  · simp only [hlt, decide_true, select, value_projection]
    have hc : (sub_raw x y).carry.toNat = 1 := by omega
    have hac : (add_raw (sub_raw x y).value modulus).carry.toNat = 1 := by omega
    simp only [p] at *
    omega
  · simp only [hlt, decide_false, select, value_projection]
    have hc : (sub_raw x y).carry.toNat = 0 := by omega
    simp only [p] at *
    omega

end ScalarLaws
