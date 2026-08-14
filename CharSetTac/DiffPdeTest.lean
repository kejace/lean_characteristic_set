/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DiffFrontend

/-!
# `wu_pde` — several derivations

`wu_diff` prolongs by `Differential.deriv`, of which a ring has exactly one. `wu_pde` takes
the derivations explicitly, so it reaches genuine PDE systems.

The example is Cauchy–Riemann for `z ↦ z²`, which is where TauCeti keeps its only
two-derivation content (`Geometry/Symplectic/JHolomorphic/Square.lean`). Writing `u = x²-y²`
and `v = 2xy` with `∂₁, ∂₂` acting on the coordinates, both CR equations follow by
elimination.

This was out of reach for `wu_diff` in principle, not merely in practice: with one
derivation there is nothing to call `∂₂`.
-/

variable {R : Type*} [CommRing R] [IsDomain R]

/-- `∂₁u = ∂₂v`. -/
example (d₁ d₂ : Derivation ℤ R R) (x y u v : R)
    (hx1 : d₁ x = 1) (hy1 : d₁ y = 0) (hx2 : d₂ x = 0) (hy2 : d₂ y = 1)
    (hu : u = x ^ 2 - y ^ 2) (hv : v = 2 * (x * y)) :
    d₁ u = d₂ v := by
  wu_pde (derivs := [d₁, d₂])

/-- `∂₂u = -∂₁v`. -/
example (d₁ d₂ : Derivation ℤ R R) (x y u v : R)
    (hx1 : d₁ x = 1) (hy1 : d₁ y = 0) (hx2 : d₂ x = 0) (hy2 : d₂ y = 1)
    (hu : u = x ^ 2 - y ^ 2) (hv : v = 2 * (x * y)) :
    d₂ u = -(d₁ v) := by
  wu_pde (derivs := [d₁, d₂])

/-- Harmonicity: `∂₁∂₁u + ∂₂∂₂u = 0`, at second order.

This was recorded here as a *limit* — uniform prolongation supposedly generating too many
mixed partials for the algebraic basic set to cope with. **That diagnosis was wrong.** The
blocker was two missing simp lemmas leaving `d 1` and `d 2` alive as spurious atoms; see
the note in `CharSetTac/DiffFrontendTest.lean`. With those fixed it proves, uniformly. -/
example (d₁ d₂ : Derivation ℤ R R) (x y u : R)
    (hx1 : d₁ x = 1) (hy1 : d₁ y = 0) (hx2 : d₂ x = 0) (hy2 : d₂ y = 1)
    (hu : u = x ^ 2 - y ^ 2) :
    d₁ (d₁ u) + d₂ (d₂ u) = 0 := by
  wu_pde (derivs := [d₁, d₂]) (order := 2)

/-! ### The numeral trap

`hv : v = 2 * (x * y)` is what exposed it. `Derivation.leibniz` expands `d (2 * (x*y))` to
`2 • d (x*y) + (x*y) • d 2`, and nothing in Mathlib's simp set kills that `d 2`:
`Derivation.map_natCast` is stated for `Nat.cast n`, while a literal `2` elaborates to
`OfNat.ofNat n`.

The surviving `d 2` was then reflected as a *spurious atom* multiplied by `x*y`, so the
equation for `d v` stopped being linear in the derivative and the characteristic set was
quietly wrong. The tactic reported only that the goal did not follow.

`Wu.Derivation.map_ofNat` fixes it, and needs `no_index` on the literal — without that,
`exact` finds the lemma but `simp` will not match it, because the `OfNat` instance path in
a `CommRing` differs from the one `Nat.cast_ofNat` produces.

The same class of bug bit `d 1`: the simp set carried the *ring-hom* `map_one`, which does
not apply to a derivation at all. `Derivation.map_one_eq_zero` is the right lemma. Between
them these two accounted for every "limit" this frontend had been credited with. -/

example (d : Derivation ℤ R R) : d (2 : R) = 0 := by simp

example (d : Derivation ℤ R R) : d (1 : R) = 0 := by simp

example (d : Derivation ℤ R R) (x y : R) :
    d (2 * (x * y)) = 2 * (x * d y + y * d x) := by
  simp only [Derivation.leibniz, Derivation.map_ofNat, smul_eq_mul]
  ring
