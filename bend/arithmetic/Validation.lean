import ProductTree
open ScalarImpl ScalarLaws Field Polynomial PolynomialModel MultiplyPolynomial ProductTree
namespace Validation
noncomputable section

theorem all_valid_spec (xs : Scalars) : PolynomialImpl.all_valid xs = true ↔ Canon xs := by
  induction xs with
  | nil => simp [PolynomialImpl.all_valid]
  | cons a xs ih => simp [PolynomialImpl.all_valid, valid_exact, ih]

theorem accept_spec (xs : Scalars) (basis : Nat) :
    PolynomialImpl.accept xs basis = true ↔ Canon xs ∧ basis = xs.length+1 := by
  simp [PolynomialImpl.accept, all_valid_spec, length_eq, Nat.add_comm]

theorem accepted (xs : Scalars) (basis : Nat) :
    KaratsubaImpl.checked xs basis = some (KaratsubaImpl.coefficients xs) ↔
      Canon xs ∧ basis = xs.length+1 := by
  have h := accept_spec xs basis
  cases ha : PolynomialImpl.accept xs basis <;>
    simp_all [KaratsubaImpl.checked, KaratsubaImpl.gate]

theorem rejected (xs : Scalars) (basis : Nat) :
    KaratsubaImpl.checked xs basis = none ↔ ¬Canon xs ∨ basis ≠ xs.length+1 := by
  have h := accept_spec xs basis
  cases ha : PolynomialImpl.accept xs basis <;>
    simp_all [KaratsubaImpl.checked, KaratsubaImpl.gate] <;> tauto

/-- The checked APIs agree even for noncanonical inputs and incorrect basis sizes. -/
theorem checked_equal (xs : Scalars) (basis : Nat) (hn : xs.length ≤ 256) :
    KaratsubaImpl.checked xs basis = PolynomialImpl.checked xs basis := by
  cases ha : PolynomialImpl.accept xs basis with
  | false => simp [KaratsubaImpl.checked, KaratsubaImpl.gate, PolynomialImpl.checked, PolynomialImpl.gate, ha]
  | true =>
    have hx := ((accept_spec xs basis).mp ha).1
    simp [KaratsubaImpl.checked, KaratsubaImpl.gate, PolynomialImpl.checked, PolynomialImpl.gate, ha,
      coefficients_equal xs hx hn]

end
end Validation
