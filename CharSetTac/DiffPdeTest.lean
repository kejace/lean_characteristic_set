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

/-! ### A limit, and it is the informative one

Harmonicity — `∂₁∂₁u + ∂₂∂₂u = 0` for the same `u` — is **not** proved by

```lean
wu_pde (derivs := [d₁, d₂]) (order := 2)
```

and this is worth stating precisely, because it is the boundary of the whole
uniform-prolongation approach rather than a tuning failure.

With one derivation, prolonging everything is cheap: the derivatives of a given quantity
are totally ordered, so round `k` adds one new equation per hypothesis and the chain is
naturally triangular. With two derivations at order 2 the same strategy generates every
mixed partial of everything — most of it irrelevant to the goal — and the algebraic basic
set has no way to tell which equations matter. Restricting the prolongation to `[hu]` does
not rescue it either: the coordinate facts then never get prolonged, so `∂₁∂₁x` is unknown
and the second-order expansion has free atoms in it.

Both failures have the same cause and it is the one the differential machinery exists to
address: **which prolongations to take is a ranking decision, and this tactic does not make
it.** `CharSetTac/Diff/Ranking.lean` and `Diff/Coherence.lean` are where that belongs.

So `wu_pde` is honestly scoped at first order in several derivations, which is exactly where
Cauchy–Riemann lives, and the second-order case is evidence for the ranking work rather than
a gap to paper over. -/

/-! ### The numeral trap

`hv : v = 2 * (x * y)` is what exposed it. `Derivation.leibniz` expands `d (2 * (x*y))` to
`2 • d (x*y) + (x*y) • d 2`, and nothing in Mathlib's simp set kills that `d 2`:
`Derivation.map_natCast` is stated for `Nat.cast n`, while a literal `2` elaborates to
`OfNat.ofNat 2`.

The surviving `d 2` was then reflected as a *spurious atom* multiplied by `x*y`, so the
equation for `d v` stopped being linear in the derivative and the characteristic set was
quietly wrong. The tactic reported only that the goal did not follow.

`Wu.Derivation.map_ofNat` fixes it, and needs `no_index` on the literal — without that,
`exact` finds the lemma but `simp` will not match it, because the `OfNat` instance path in
a `CommRing` differs from the one `Nat.cast_ofNat` produces. -/

example (d : Derivation ℤ R R) : d (2 : R) = 0 := by simp

example (d : Derivation ℤ R R) (x y : R) :
    d (2 * (x * y)) = 2 * (x * d y + y * d x) := by
  simp only [Derivation.leibniz, Wu.Derivation.map_ofNat, smul_eq_mul]
  ring
