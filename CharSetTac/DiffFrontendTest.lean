/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DiffFrontend

/-!
# `wu_diff` in use

Each theorem here is one from `WuDifferential/Theorems.lean` with its hand-written
prolongation deleted. Compare:

```lean
-- before
example (y : R) (h : y′ = y ^ 2) : (y′)′ = 2 * y ^ 3 := by
  have h' : (y′)′ = 2 * y * y′ := by
    rw [Wu.deriv_congr h, pow_two, deriv_mul]; ring
  wu

-- after
example (y : R) (h : y′ = y ^ 2) : (y′)′ = 2 * y ^ 3 := by wu_diff
```

The `have` was the only differential content in the proof, and it is exactly what the
frontend now generates: `congrArg` to differentiate the hypothesis, then `simp` with the
Leibniz and power rules to expand `δ` into the derivative atoms.

The explicit versions are kept in `WuDifferential/` deliberately — they document what the
tactic is doing, and they are what one falls back to when the automatic prolongation order
is not enough.
-/

open scoped Differential

section
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [Differential R]

/-- One prolongation, no Leibniz needed. -/
example (y : R) (h : y′ = y) : (y′)′ = y := by wu_diff

/-- The power rule is applied automatically: `δ(y²) = 2y·y′`. -/
example (y : R) (h : y′ = y ^ 2) : (y′)′ = 2 * y ^ 3 := by wu_diff

/-- Two prolongations deep, via `(order := 2)`. -/
example (y : R) (h : y′ = y) : ((y′)′)′ = y := by wu_diff (order := 2)

/-- A coupled system: the harmonic oscillator derived by elimination, where previously the
prolongation of `u′ = v` had to be supplied by hand. -/
example (u v : R) (h₁ : u′ = v) (h₂ : v′ = -u) : (u′)′ + u = 0 := by wu_diff

/-! ### A "limit" that turned out to be a bug

The logistic equation was recorded here as a limit of the frontend — the automatic
expansion supposedly produced a form the elimination could not reduce. **That was wrong.**

The real cause was two missing simp lemmas. `Derivation.leibniz` expanding `d (2 * ...)`
left a live `d 2`, because Mathlib's `map_natCast` is stated for `Nat.cast` and a literal
is `OfNat.ofNat`; and the simp set carried the *ring-hom* `map_one` rather than
`Derivation.map_one_eq_zero`, so `d 1` survived too. Both were reflected as spurious atoms,
quietly corrupting the characteristic set. The only symptom was the goal failing to reduce —
which is exactly what a genuine limitation looks like from outside.

Both are fixed in `CharSetTac/DiffFrontend.lean`, and the theorem now proves. Recorded
because the lesson is about diagnosis: a tactic that reports "does not follow" is stating a
fact about *its input*, and the input is worth reading before the failure is written up as
mathematics. -/

example (y : R) (h : y′ = y * (1 - y)) :
    (y′)′ = y * (1 - y) * (1 - 2 * y) := by wu_diff

end
