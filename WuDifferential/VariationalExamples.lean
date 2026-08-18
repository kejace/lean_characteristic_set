/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuDifferential.Variational

/-!
# `ℚ[x]{y}`, and the converse in action

Examples for the two most recent additions: `R{y}` over a differential base ring, and the
converse to `E ∘ D = 0`.

## 1. A base that is not constant

`Wu.DiffPolynomial.derivOver` extends a derivation of the coefficients instead of
annihilating them. Taking the base to be `ℚ[x]` with `d/dx` gives `ℚ[x]{y}`, where `x` is a
genuine independent variable — `D x = 1` — and every statement in §1 below is one that
`Wu.DiffPolynomial.deriv` cannot even express, since for it `D (C r) = 0` always.

The payoff is Olver's own worked null Lagrangian (*Applications of Lie Groups*, Ch. 4):

```
  x²y' + 2xy = D(x²y)
```

Both the Lagrangian and its potential are explicitly `x`-dependent, which is exactly why it
is invisible over a base of constants.

## 2. The converse, producing potentials

`euler_eq_zero_iff_mem_range` says that for homogeneous `L` of positive degree, `E L = 0` is
equivalent to `L` being a total derivative. Used left-to-right it **produces** a potential
from a vanishing Euler–Lagrange expression rather than requiring one to be guessed; used
right-to-left (i.e. as `E ∘ D = 0`) it proves a Lagrangian is *not* a total derivative, and
so has genuine dynamics.
-/

open MvPolynomial

namespace WuDifferential.VariationalExamples

/-! ### 1. `ℚ[x]{y}` — a differential base ring -/

section DiffBase

/-- The base `ℚ[x]`. -/
abbrev Base : Type := MvPolynomial Unit ℚ

/-- `d/dx` on the base. -/
noncomputable abbrev dx : Derivation ℚ Base Base := pderiv ()

/-- `ℚ[x]{y}` — differential polynomials whose coefficients are themselves differentiated. -/
abbrev Q : Type := Wu.DiffPolynomial Base Unit

/-- The total derivative over the differential base. -/
noncomputable abbrev D : Derivation ℚ Q Q := Wu.DiffPolynomial.derivOver Base Unit dx

/-- `x`, viewed in `ℚ[x]{y}`. -/
noncomputable abbrev xx : Q := C (X ())

/-- `y^(k)`. -/
local notation "y[" k "]" => (Wu.DiffPolynomial.Y (() : Unit) k : Q)

/-- **`D x = 1`.** The independent variable exists. Contrast
`MvPolynomial.derivation_C`, which says the old `deriv` kills every coefficient. -/
example : D xx = 1 := by
  rw [xx, Wu.DiffPolynomial.derivOver_C]
  simp

/-- The shift is unchanged. -/
example (k : ℕ) : D y[k] = y[k + 1] := Wu.DiffPolynomial.derivOver_Y _ _

/-- The product rule against the independent variable: `D(x·y) = y + x·y'`. -/
example : D (xx * y[0]) = y[0] + xx * y[1] := by
  rw [Derivation.leibniz, Wu.DiffPolynomial.derivOver_Y, xx,
    Wu.DiffPolynomial.derivOver_C]
  simp [smul_eq_mul]
  ring

/-- **Olver's null Lagrangian.** `x²y' + 2xy` is a total derivative, namely `D(x²y)`, and
both sides are explicitly `x`-dependent — unstateable over a base of constants. -/
example : D (C (X () ^ 2) * y[0]) = C (X () ^ 2) * y[1] + C (2 * X ()) * y[0] := by
  rw [Derivation.leibniz, Wu.DiffPolynomial.derivOver_Y, Wu.DiffPolynomial.derivOver_C]
  simp [smul_eq_mul, Derivation.leibniz_pow]
  ring

end DiffBase

/-! ### 2. The converse, producing potentials -/

section Converse

open Wu.Variational

local notation "y[" k "]" => Wu.DiffPolynomial.Y (() : Unit) k

/-- `2y'y''` has order at most `2`. -/
private theorem order_lt_three : order (2 * (y[1] * y[2]) : P) < 3 := by
  refine order_lt_of_vars_lt (by norm_num) fun p hp => ?_
  have hsub : (2 * (y[1] * y[2]) : P).vars ⊆ {((), 1), ((), 2)} := by
    refine (vars_mul _ _).trans (Finset.union_subset ?_ ?_)
    · rw [show (2 : P) = C 2 from (map_ofNat _ 2).symm, vars_C]
      exact Finset.empty_subset _
    · refine (vars_mul _ _).trans (Finset.union_subset ?_ ?_) <;>
        simp [Wu.DiffPolynomial.Y, vars_X]
  rcases Finset.mem_insert.mp (hsub hp) with h | h
  · rw [h]; norm_num
  · rw [Finset.mem_singleton] at h; rw [h]; norm_num

/-- **`2y'y''` is variationally trivial.** The two surviving terms of the alternating sum
cancel: `-D(2y'') + D²(2y') = -2y''' + 2y''' = 0`. -/
theorem euler_two_y1_y2 : E (2 * (y[1] * y[2]) : P) = 0 := by
  rw [E_eq_euler order_lt_three]
  simp [euler, Finset.sum_range_succ, Derivation.leibniz]

/-- It is homogeneous of degree `2`. -/
private theorem homog_two_y1_y2 : (2 * (y[1] * y[2]) : P).IsHomogeneous 2 := by
  have h1 : (y[1] : P).IsHomogeneous 1 := by
    rw [Wu.DiffPolynomial.Y]; exact isHomogeneous_X _ _
  have h2 : (y[2] : P).IsHomogeneous 1 := by
    rw [Wu.DiffPolynomial.Y]; exact isHomogeneous_X _ _
  rw [show (2 : P) = C 2 from (map_ofNat _ 2).symm]
  simpa using ((isHomogeneous_C _ (2 : ℚ)).mul (h1.mul h2))

/-- **A potential, produced rather than guessed.**

Nothing here names `(y')²`. The theorem takes `E L = 0` and homogeneity and returns the
existence of `f` with `D f = L`; the witness comes from the graded homotopy `I(L)/n`. -/
theorem exists_potential_two_y1_y2 : ∃ f : P, Dtot f = 2 * (y[1] * y[2]) :=
  (euler_eq_zero_iff_mem_range (n := 2) (by norm_num) homog_two_y1_y2).mp euler_two_y1_y2

/-! #### The other direction: a Lagrangian with real dynamics -/

private theorem order_lt_two : order ((y[1] : P) ^ 2) < 2 := by
  refine order_lt_of_vars_lt (by norm_num) fun p hp => ?_
  have hsub : ((y[1] : P) ^ 2).vars ⊆ {((), 1)} :=
    (vars_pow _ _).trans (by simp [Wu.DiffPolynomial.Y, vars_X])
  rw [Finset.mem_singleton.mp (hsub hp)]
  norm_num

/-- The free-particle Lagrangian has Euler–Lagrange expression `-2y''`. -/
theorem euler_y1_sq : E ((y[1] : P) ^ 2) = -(2 * y[2]) := by
  rw [E_eq_euler order_lt_two]
  simp [euler, Finset.sum_range_succ, Derivation.leibniz_pow]

/-- **`(y')²` is not a total derivative** — so the free particle has genuine dynamics rather
than being variationally trivial. This is `E ∘ D = 0` used contrapositively, and it needs no
search over candidate potentials. -/
theorem not_exists_potential_y1_sq : ¬ ∃ f : P, Dtot f = (y[1] : P) ^ 2 := by
  rintro ⟨f, hf⟩
  have h0 : E ((y[1] : P) ^ 2) = 0 := hf ▸ E_deriv f
  rw [euler_y1_sq, neg_eq_zero] at h0
  have : (y[2] : P) ≠ 0 := MvPolynomial.X_ne_zero _
  exact this (by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (by norm_num)
    · exact h)

end Converse

end WuDifferential.VariationalExamples
