import Mathlib
import CharSetTac.Frontend

/-!
# `wu` tactic tests

The M3 gate: `by wu` closing real goals, over several base rings, with nondegeneracy
conditions surfaced honestly as side goals.
-/

section Parallelogram

/-- The parallelogram theorem, stated over `ℝ` exactly as in
`CharacteristicSet/ParallelogramExample.lean:134` but with real coordinates. -/
example (x₀ x₁ x₂ x₃ : ℝ)
    (h₁ : x₁ - x₀ = x₃ - x₂) (h₂ : x₂ - x₀ = x₃ - x₁) :
    x₀ + x₃ = x₁ + x₂ := by wu

/-- The second conclusion of the same configuration. -/
example (x₄ x₅ x₆ x₇ : ℝ)
    (h₃ : x₅ - x₄ = x₇ - x₆) (h₄ : x₆ - x₄ = x₇ - x₅) :
    x₄ + x₇ = x₅ + x₆ := by wu

end Parallelogram

section BaseRings

-- `wu` should work over any `CommRing` with `NoZeroDivisors`, not just `ℝ`.

example (a b : ℚ) (h : a = b) : a + a = b + b := by wu

example (a b : ℂ) (h : a = b) : a * a = b * b := by wu

example (a b : ℤ) (h : a - b = 0) : a = b := by wu

example {R : Type*} [CommRing R] [IsDomain R] (a b c : R)
    (h₁ : a = b) (h₂ : b = c) : a = c := by wu

end BaseRings

section Nonlinear

/-- A genuinely triangular system: `y² = x`, `z = y` ⊢ `z² = x`. -/
example (x y z : ℝ) (h₁ : y ^ 2 = x) (h₂ : z = y) : z ^ 2 = x := by wu

/-- Atoms need not be variables: any non-polynomial subterm is abstracted. -/
example (u v : ℝ) (h : Real.sin u = v) : Real.sin u * Real.sin u = v * v := by wu

end Nonlinear

section Degenerate

/-- When the initial is not a numeral, `wu` leaves the nondegeneracy condition as a side
goal rather than silently assuming it. Here dividing through by `a` requires `a ≠ 0`. -/
example (a x y : ℝ) (ha : a ≠ 0) (h : a * x = a * y) : x = y := by wu

end Degenerate

section Axioms

/-- A named version so we can inspect its axioms. -/
theorem parallelogram_wu (x₀ x₁ x₂ x₃ : ℝ)
    (h₁ : x₁ - x₀ = x₃ - x₂) (h₂ : x₂ - x₀ = x₃ - x₁) :
    x₀ + x₃ = x₁ + x₂ := by wu

-- The certificate route adds no axioms beyond the three Lean/Mathlib standards. In
-- particular there is no `ofReduceBool`, i.e. no `native_decide` anywhere. Enforced:
/--
info: 'parallelogram_wu' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms parallelogram_wu

end Axioms
