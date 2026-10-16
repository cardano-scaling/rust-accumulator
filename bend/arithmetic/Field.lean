import Reduction
import Init.GrindInstances.Ring.Fin
open ScalarImpl ScalarLaws Montgomery Reduction
namespace Field
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

/-- Multiplication is two Montgomery products with the fixed R-squared conversion. -/
theorem mul_as_montgomery (a b : Scalar) :
    mul a b = montgomery (montgomery r_squared a) b := rfl

theorem conversion_constant : (decode r_squared * inverseR * inverseR) % p = 1 := by
  have certificate : decode r_squared * inverseR * inverseR = 385707664294953839722905273487578005866768475514755895851696506721872512186999070528116216275849305973262591238755669240067172752142948934888899780011775 * p + 1 := by decide +kernel
  rw [certificate, Nat.add_mod, Nat.mul_mod_left]
  simp only [Nat.zero_add]
  exact Nat.mod_eq_of_lt (by decide +kernel)

/-- The executable multiplication computes the ordinary canonical field product. -/
theorem mul_exact (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    decode (mul a b) = (decode a * decode b) % p := by
  have hp : 0 < p := by decide
  have hr : decode r_squared < p := by decide +kernel
  have first := montgomery_exact r_squared a hr ha
  have canonical : decode (montgomery r_squared a) < p := by
    rw [first]
    exact Nat.mod_lt _ hp
  rw [mul_as_montgomery, montgomery_exact _ _ canonical hb, first]
  rw [Nat.mul_assoc, Nat.mod_mul_mod]
  have rearrange : decode r_squared * decode a * inverseR * (decode b * inverseR) =
      (decode a * decode b) * (decode r_squared * inverseR * inverseR) := by ac_rfl
  rw [rearrange, Nat.mul_mod, conversion_constant, Nat.mul_one, Nat.mod_mod]


instance : NeZero p := ⟨by decide⟩

/-- Canonical residues form the concrete ring used by the coefficient code. -/
def residue (x : Scalar) : Fin p := Fin.ofNat p (decode x)

theorem add_closed (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    decode (add a b) < p := by
  rw [add_exact a b ha hb]
  exact Nat.mod_lt _ (by decide)

theorem sub_closed (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    decode (sub a b) < p := by
  rw [sub_exact a b ha hb]
  exact Nat.mod_lt _ (by decide)

theorem mul_closed (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    decode (mul a b) < p := by
  rw [mul_exact a b ha hb]
  exact Nat.mod_lt _ (by decide)

theorem montgomery_closed (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    decode (montgomery a b) < p := by
  rw [montgomery_exact a b ha hb]
  exact Nat.mod_lt _ (by decide)

theorem residue_add (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    residue (add a b) = residue a + residue b := by
  apply Fin.ext
  change decode (add a b) % p = ((decode a % p) + (decode b % p)) % p
  rw [add_exact a b ha hb, Nat.mod_mod, Nat.add_mod]

theorem residue_sub (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    residue (sub a b) = residue a - residue b := by
  apply Fin.ext
  change decode (sub a b) % p = (p - decode b % p + decode a % p) % p
  rw [sub_exact a b ha hb, Nat.mod_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  congr 1
  omega

theorem residue_mul (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    residue (mul a b) = residue a * residue b := by
  apply Fin.ext
  change decode (mul a b) % p = ((decode a % p) * (decode b % p)) % p
  rw [mul_exact a b ha hb, Nat.mod_mod, Nat.mul_mod]

theorem residue_montgomery (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    residue (montgomery a b) = residue a * residue b * Fin.ofNat p inverseR := by
  apply Fin.ext
  simp only [residue, Fin.val_ofNat, Fin.val_mul, montgomery_exact a b ha hb,
    Nat.mul_mod, Nat.mod_mod]

/-- Canonical encodings are unique, so equality of residues is scalar equality. -/
theorem decode_injective (a b : Scalar) (h : decode a = decode b) : a = b := by
  cases a; cases b
  congr 1 <;> apply BitVec.toNat_inj.mp <;>
    simp only [decode] at h <;> omega

theorem residue_injective (a b : Scalar) (ha : decode a < p) (hb : decode b < p)
    (h : residue a = residue b) : a = b := by
  apply decode_injective
  have hv := congrArg Fin.val h
  simpa only [residue, Fin.val_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv

/-- Karatsuba's cross term holds for the actual Montgomery scalar operations. -/
theorem karatsuba_cross (a b c d : Scalar)
    (ha : decode a < p) (hb : decode b < p) (hc : decode c < p) (hd : decode d < p) :
    sub (sub (montgomery (add a b) (add c d)) (montgomery a c)) (montgomery b d) =
      add (montgomery a d) (montgomery b c) := by
  have hab := add_closed a b ha hb
  have hcd := add_closed c d hc hd
  have habcd := montgomery_closed (add a b) (add c d) hab hcd
  have hac := montgomery_closed a c ha hc
  have hbd := montgomery_closed b d hb hd
  have had := montgomery_closed a d ha hd
  have hbc := montgomery_closed b c hb hc
  have hfirst := sub_closed _ _ habcd hac
  apply residue_injective _ _ (sub_closed _ _ hfirst hbd) (add_closed _ _ had hbc)
  rw [residue_sub _ _ hfirst hbd, residue_sub _ _ habcd hac,
    residue_add _ _ had hbc, residue_montgomery _ _ hab hcd,
    residue_montgomery _ _ ha hc, residue_montgomery _ _ hb hd,
    residue_montgomery _ _ ha hd, residue_montgomery _ _ hb hc,
    residue_add _ _ ha hb, residue_add _ _ hc hd]
  grind


/-- The product tree's literal identity really is R modulo p. -/
theorem montgomery_one_exact : decode montgomery_one = 2^276 % p := by
  have certificate : 2^276 = 2315529 * p + decode montgomery_one := by decide +kernel
  have canonical : decode montgomery_one < p := by decide +kernel
  rw [certificate, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt canonical]
  exact (Nat.mod_eq_of_lt canonical).symm

theorem identity_constant : (decode montgomery_one * inverseR) % p = 1 := by
  have certificate : decode montgomery_one * inverseR = 10348777855573461318664586698295879009172095409879199360956882618036923685079 * p + 1 := by decide +kernel
  rw [certificate, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add]
  exact Nat.mod_eq_of_lt (by decide +kernel)

theorem montgomery_identity (a : Scalar) (ha : decode a < p) :
    montgomery montgomery_one a = a := by
  apply decode_injective
  rw [montgomery_exact _ _ (by decide +kernel) ha]
  have rearrange : decode montgomery_one * decode a * inverseR =
      decode a * (decode montgomery_one * inverseR) := by ac_rfl
  rw [rearrange, Nat.mul_mod, identity_constant, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt ha]

theorem montgomery_comm (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    montgomery a b = montgomery b a := by
  apply decode_injective
  rw [montgomery_exact a b ha hb, montgomery_exact b a hb ha, Nat.mul_comm (decode a)]

/-- Entering and leaving Montgomery representation preserves the public scalar. -/
theorem montgomery_roundtrip (a : Scalar) (ha : decode a < p) :
    montgomery one (montgomery r_squared a) = a := by
  have h1 : decode one < p := by decide +kernel
  have hr : decode r_squared < p := by decide +kernel
  rw [montgomery_comm _ _ h1 (montgomery_closed _ _ hr ha), ← mul_as_montgomery]
  apply decode_injective
  rw [mul_exact _ _ ha h1]
  have one_exact : decode one = 1 := by decide +kernel
  rw [one_exact, Nat.mul_one, Nat.mod_eq_of_lt ha]

end Field
