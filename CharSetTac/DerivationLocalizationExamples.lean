/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DerivationLocalization
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# `Derivation.localization` in use

Three instantiations, in increasing order of how much they say.
-/

open MvPolynomial

section BasicOpen

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **The case differential Spec is built from.** On the basic open `D(f)` the sections are
`A_f`, and they carry a derivation extending `d`.

This one line is the reason the whole file exists: `restrict_deriv`, which
`CharSetTac/DiffSheaf.lean` currently takes as an axiom, is the statement that these
extensions agree on overlaps — and there is now something to prove it about. -/
noncomputable example (d : Derivation R A A) (f : A) :
    Derivation R (Localization.Away f) (Localization.Away f) :=
  d.localization (Submonoid.powers f)

/-- The extension restricts to the original derivation, which is what makes "extends" mean
anything. -/
example (d : Derivation R A A) (f : A) (a : A) :
    (d.localization (B := Localization.Away f) (Submonoid.powers f))
        (algebraMap A (Localization.Away f) a)
      = algebraMap A (Localization.Away f) (d a) :=
  Derivation.localization_algebraMap d _ a

end BasicOpen

section RationalFunctions

/-- **Rational functions.** `∂/∂xᵢ` on a polynomial ring extends to the field of fractions.

Classically this is the statement that the quotient rule is consistent — that
`d(p/q) = (q p' - p q')/q²` is well defined. Here it is an instance of the general
construction, and the well-definedness was never argued: `IsLocalization.lift` supplied it. -/
noncomputable example (σ : Type) (i : σ) :
    Derivation ℚ (FractionRing (MvPolynomial σ ℚ)) (FractionRing (MvPolynomial σ ℚ)) :=
  (pderiv i).localization (nonZeroDivisors (MvPolynomial σ ℚ))

end RationalFunctions

section Concrete

/-- **`x² · d(1/x) = -1`.**

The quotient rule on the smallest interesting input, computed rather than assumed. With
`a = 1` and `s = x`, `localization_mk'` gives `x² · d(1/x) = x · d1 - 1 · dx`, and
`d1 = 0`, `dx = 1`.

Worth stating because it is the first thing one would check by hand, and it comes out of a
construction that never picked a representative for `1/x`. -/
example (σ : Type) (i : σ)
    (hx : (X i : MvPolynomial σ ℚ) ∈ nonZeroDivisors (MvPolynomial σ ℚ)) :
    (algebraMap (MvPolynomial σ ℚ) (FractionRing (MvPolynomial σ ℚ)) (X i)) ^ 2 *
        ((pderiv i).localization
            (B := FractionRing (MvPolynomial σ ℚ)) (nonZeroDivisors (MvPolynomial σ ℚ))
          (IsLocalization.mk' (FractionRing (MvPolynomial σ ℚ)) 1 ⟨X i, hx⟩))
      = -1 := by
  rw [Derivation.localization_mk' (B := FractionRing (MvPolynomial σ ℚ)) (pderiv i)
    (nonZeroDivisors (MvPolynomial σ ℚ)) 1 ⟨X i, hx⟩]
  simp

end Concrete
