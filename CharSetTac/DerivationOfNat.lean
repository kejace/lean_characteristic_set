/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Derivation.Basic

/-!
# A derivation annihilates numeric literals

Mathlib gives `Derivation` the family `map_zero`, `map_one_eq_zero`, `map_natCast`,
`map_intCast`, `map_algebraMap` — and no `map_ofNat`. That is a genuine hole rather than a
stylistic gap: `map_ofNat` ships *next to* `map_natCast` throughout the library
(`Data/Nat/Cast/Basic.lean`, `Algebra/Polynomial/Eval/Defs.lean`,
`Algebra/MvPolynomial/Eval.lean`, `Data/ENat/Basic.lean`, `Data/Matrix/Diagonal.lean`), and
`Derivation` is the odd one out.

## Why it matters

`map_natCast` is about `Nat.cast n`; a numeric *literal* like `2` elaborates to
`OfNat.ofNat 2`. So `simp` leaves `D 2` standing. In this project that has cost real time
twice — `Derivation.leibniz` on `2 * (x * y)` produces `2 • D (x*y) + (x*y) • D 2`, and the
surviving `D 2` gets reflected as a *spurious atom*, which silently poisons the characteristic
set: the equation for `D v` stops being linear in the derivative and the goal stops reducing.
The failure is invisible from outside — the tactic merely reports that the goal does not
follow.

It bit a second time in `WuDifferential/Variational.lean`, where `D 2` survived inside an
Euler–Lagrange computation.

Its own file because it is bound for Mathlib — see `MATHLIBABLE_REPORT.md`, candidate 3.
-/

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M]

/-- **A derivation annihilates a numeric literal.**

The `OfNat` companion to `Derivation.map_natCast`, spelled with Mathlib's `ofNat(n)` macro so
that `simp` matches actual literals. -/
@[simp] theorem map_ofNat (D : Derivation R A M) (n : ℕ) [n.AtLeastTwo] :
    D ofNat(n) = 0 := by
  rw [← Nat.cast_ofNat]; exact D.map_natCast _

end Derivation
