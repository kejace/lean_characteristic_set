/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Differential

/-!
# Setting for differential examples

A differential ring together with a set of *constants* (parameters with zero derivative).
Model parameters such as growth or transmission rates must be declared constant, otherwise
prolonging a hypothesis produces stray `α′` terms and the elimination has nothing to work
with.

`prolong` is the workhorse: it turns `h : a = b` into a statement about `a′`, leaving the
expansion of `b′` to `simp` with the Leibniz rule and then `ring`.
-/

open scoped Differential

namespace WuDiff

variable {R : Type*} [CommRing R] [Differential R]

/-- Expand `δ` over a ring expression. Used to discharge prolongation obligations. -/
theorem deriv_mul (a b : R) : (a * b)′ = a * b′ + b * a′ := Derivation.leibniz _ a b

/-- `δ` of a square. -/
theorem deriv_sq (a : R) : (a * a)′ = 2 * a * a′ := by
  rw [deriv_mul]; ring

/-- `δ` kills constants, in the form needed to rewrite. -/
theorem deriv_const_mul {c : R} (hc : c′ = 0) (a : R) : (c * a)′ = c * a′ := by
  rw [deriv_mul, hc]; ring

end WuDiff
