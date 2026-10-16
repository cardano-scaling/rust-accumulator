import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Field
import KaratsubaImpl
open ScalarImpl ScalarLaws Reduction Field Polynomial
namespace PolynomialModel
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
abbrev R := ZMod p
abbrev Q := Polynomial R
abbrev Scalars := List Scalar

def Canon (xs : Scalars) : Prop := ∀ a ∈ xs, decode a < p
@[simp] theorem canon_nil : Canon [] := by simp [Canon]
@[simp] theorem canon_cons (a : Scalar) (xs : Scalars) :
    Canon (a :: xs) ↔ decode a < p ∧ Canon xs := by simp [Canon]
theorem canon_take (xs : Scalars) (n : Nat) (h : Canon xs) : Canon (xs.take n) :=
  fun a ha => h a (List.mem_of_mem_take ha)
theorem canon_drop (xs : Scalars) (n : Nat) (h : Canon xs) : Canon (xs.drop n) :=
  fun a ha => h a (List.mem_of_mem_drop ha)

@[simp] theorem zero_valid : decode zero < p := by decide +kernel
@[simp] theorem one_valid : decode one < p := by decide +kernel
@[simp] theorem residue_zero : (residue zero : R) = 0 := by decide +kernel
@[simp] theorem residue_one : (residue one : R) = 1 := by decide +kernel

def sr (a : Scalar) : R := residue a
@[simp] theorem sr_zero : sr zero = 0 := residue_zero
@[simp] theorem sr_one : sr one = 1 := residue_one
theorem sr_add (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    sr (add a b) = sr a + sr b := residue_add a b ha hb
theorem sr_sub (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    sr (sub a b) = sr a - sr b := residue_sub a b ha hb
theorem sr_mul (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    sr (mul a b) = sr a * sr b := residue_mul a b ha hb
def invR : R := Fin.ofNat p inverseR
theorem sr_montgomery (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    sr (montgomery a b) = sr a * sr b * invR := residue_montgomery a b ha hb

def mr (a : Scalar) : R := sr a * invR
@[simp] theorem mr_zero : mr zero = 0 := by simp [mr]
theorem mr_add (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    mr (add a b) = mr a + mr b := by rw [mr, sr_add a b ha hb]; simp [mr, add_mul]
theorem mr_sub (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    mr (sub a b) = mr a - mr b := by rw [mr, sr_sub a b ha hb]; simp [mr, sub_mul]
theorem mr_mul (a b : Scalar) (ha : decode a < p) (hb : decode b < p) :
    mr (montgomery a b) = mr a * mr b := by
  rw [mr, sr_montgomery a b ha hb]
  change (sr a * sr b * invR) * invR = (sr a * invR) * (sr b * invR)
  ring

def poly (f : Scalar → R) : Scalars → Q
  | [] => 0
  | a :: xs => C (f a) + X * poly f xs

@[simp] theorem poly_nil (f : Scalar → R) : poly f [] = 0 := rfl
@[simp] theorem poly_cons (f : Scalar → R) (a : Scalar) (xs : Scalars) :
    poly f (a :: xs) = C (f a) + X * poly f xs := rfl

/-- A coefficient list has no nonzero coefficients beyond its length. -/
theorem coeff_outside (f : Scalar → R) (xs : Scalars) (k : Nat) (hk : xs.length ≤ k) :
    (poly f xs).coeff k = 0 := by
  induction xs generalizing k with
  | nil => simp
  | cons a xs ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have h : xs.length ≤ k := by simpa using hk
      simp only [poly_cons, coeff_add, coeff_C, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ↓reduceIte, coeff_X_mul, zero_add]
      exact ih k h

/-- Appending coefficients shifts the second polynomial by the first list's length. -/
theorem poly_append (f : Scalar → R) (xs ys : Scalars) :
    poly f (xs ++ ys) = poly f xs + X^xs.length * poly f ys := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.cons_append, poly_cons, List.length_cons, ih, pow_succ]; ring

theorem poly_split (f : Scalar → R) (xs : Scalars) (n : Nat) (hn : n ≤ xs.length) :
    poly f xs = poly f (xs.take n) + X^n * poly f (xs.drop n) := by
  have h := poly_append f (xs.take n) (xs.drop n)
  simpa [List.take_append_drop, List.length_take, Nat.min_eq_left hn] using h

/-- Equal-length canonical lists with equal public polynomials have equal encodings. -/
theorem poly_injective (xs ys : Scalars) (hx : Canon xs) (hy : Canon ys)
    (hlen : xs.length = ys.length) (h : poly sr xs = poly sr ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => simpa using hlen.symm
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      obtain ⟨ha, hxs⟩ := (canon_cons a xs).mp hx
      obtain ⟨hb, hys⟩ := (canon_cons b ys).mp hy
      have hc := congrArg (fun (q : Q) => q.coeff 0) h
      simp only [poly_cons, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero] at hc
      have hab : a = b := residue_injective a b ha hb hc
      subst b
      have ht : poly sr xs = poly sr ys := by
        ext k
        have hk := congrArg (fun (q : Q) => q.coeff (k+1)) h
        simpa [coeff_X_mul] using hk
      congr 1
      exact ih ys hxs hys (by simpa using hlen) ht
end
end PolynomialModel
