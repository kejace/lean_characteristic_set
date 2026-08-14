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

/-! **A limit of the frontend.** The logistic equation `y′ = y(1-y)` is *not* proved by
`wu_diff`: the automatic expansion produces a form the elimination does not reduce, and the
explicit version in `WuDifferential/Theorems.lean` (which states the prolongation as
`y″ = y′ - 2y·y′`) is still needed. Recorded rather than omitted — the frontend covers the
common case, not every case.

```lean
example (y : R) (h : y′ = y * (1 - y)) :
    (y′)′ = y * (1 - y) * (1 - 2 * y) := by wu_diff   -- fails
```
-/

end
