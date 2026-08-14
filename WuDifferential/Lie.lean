/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Frontend
import Mathlib.RingTheory.Derivation.Lie

/-!
# Lie derivatives and symmetry

A Lie derivative along a vector field *is* a derivation of the function ring, so it drops
into the existing framework with no new machinery at all: `L_X` is a `Derivation`, its
Leibniz rule is `Derivation.leibniz`, and `wu` treats `L_X f` as an atom exactly as it
treats `f′`.

That makes the whole vocabulary of symmetry available immediately:

* `L_X f = 0` says `f` is a **first integral** of the flow of `X`;
* `L_X g = 0` on metric coefficients is the **Killing** condition;
* `[L_X, L_Y] = L_{[X,Y]}` is the bracket, which Mathlib already has as the Lie ring
  structure on derivations.

The theorems below are the closure properties that make "the invariants of a flow" a
subring, and the standard fact that symmetries propagate along commuting flows. None of
them needs anything beyond what the ordinary engine already does.
-/

namespace WuLie

variable {R : Type*} [CommRing R] [IsDomain R]

/-! ### Invariants form a subring -/

/-- A sum of first integrals is a first integral. -/
theorem invariant_add (X : Derivation ℤ R R) (f g : R)
    (hf : X f = 0) (hg : X g = 0) : X (f + g) = 0 := by
  have leib : X (f + g) = X f + X g := map_add _ _ _
  wu

/-- A product of first integrals is a first integral.

This is the multiplicative closure that makes the invariants a *subring* rather than just
a subgroup, and it is exactly where the Leibniz rule enters. -/
theorem invariant_mul (X : Derivation ℤ R R) (f g : R)
    (hf : X f = 0) (hg : X g = 0)
    (leib : X (f * g) = f * X g + g * X f) : X (f * g) = 0 := by wu

/-- Any polynomial in first integrals is a first integral: the quadratic case. -/
theorem invariant_sq (X : Derivation ℤ R R) (f : R) (hf : X f = 0)
    (leib : X (f * f) = f * X f + f * X f) : X (f * f) = 0 := by wu

/-! ### Symmetries propagate along commuting flows -/

/-- If `f` is invariant under `X` and the flows of `X` and `Y` commute, then `Y f` is again
invariant under `X`.

This is how one symmetry generates a family of invariants — the mechanism behind
Noether-style arguments and behind the hierarchies of integrable systems. -/
theorem invariant_of_commuting (X Y : Derivation ℤ R R) (f : R)
    (hf : X f = 0) (hcomm : X (Y f) = Y (X f)) : X (Y f) = 0 := by
  have h : Y (X f) = 0 := by rw [hf, map_zero]
  wu

/-! ### Killing conditions -/

/-- If the metric coefficients are invariant along `X`, so is the metric determinant.

For a surface metric with coefficients `E, F, G`, this says `X` being a Killing field forces
`EG - F²` — the area element squared, and the multiplier that appears throughout the
Gauss–Codazzi computations — to be a first integral. -/
theorem killing_det (X : Derivation ℤ R R) (E F G : R)
    (hE : X E = 0) (hF : X F = 0) (hG : X G = 0)
    (leib : X (E * G - F * F) = E * X G + G * X E - (F * X F + F * X F)) :
    X (E * G - F * F) = 0 := by wu

/-- A Killing field preserves the ratio that defines conformal structure: if `E` and `G`
are invariant then so is `E * G`, hence any invariant built from them. Stated for the
combination appearing in the Codazzi equations. -/
theorem killing_codazzi_combination (X : Derivation ℤ R R) (E G L N : R)
    (hE : X E = 0) (hG : X G = 0) (hL : X L = 0) (hN : X N = 0)
    (leib : X (G * L + E * N) = G * X L + L * X G + (E * X N + N * X E)) :
    X (G * L + E * N) = 0 := by wu

/-! ### Conserved quantities of a flow

Written with the vector field acting directly, which is the form a first-integral
computation actually takes. -/

/-- The harmonic oscillator's energy, as a Lie-derivative statement: the field
`X = v ∂_u - u ∂_v` annihilates `u² + v²`. -/
theorem harmonic_first_integral (X : Derivation ℤ R R) (u v : R)
    (hu : X u = v) (hv : X v = -u)
    (leib : X (u * u + v * v) = u * X u + u * X u + (v * X v + v * X v)) :
    X (u * u + v * v) = 0 := by wu

end WuLie
