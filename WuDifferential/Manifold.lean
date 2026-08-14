/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Differential
import Mathlib.Geometry.Manifold.DerivationBundle

/-!
# From abstract differential rings to smooth functions on a manifold

Everything else in `WuDifferential/` is stated over an abstract `[CommRing R]
[Differential R]`. This file connects that to Mathlib's manifold theory, so the theorems
are about something.

## The connection

Mathlib already models a global vector field the way we need it. In
`Mathlib/Geometry/Manifold/DerivationBundle.lean` a vector field on `M` is literally a term
of type

```
Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯
```

— a derivation of the ring of smooth functions into itself — and `C^∞⟮I, M; 𝕜⟯` is a
`CommRing` (`Mathlib/Geometry/Manifold/Algebra/SmoothFunctions.lean`). That is exactly the
shape `Differential` wants, so `differentialOfVectorField` below is the whole bridge.

Differentiating along `X` is then `′`, and a hypothesis like `y′ = y` says `y` is an
eigenfunction of the directional derivative.

## Why this needed a change to `wu`

`C^∞⟮I, M; ℝ⟯` is **not** an integral domain: two bump functions with disjoint support
multiply to zero. Every theorem here would therefore have been inapplicable, because `wu`
used to require `IsDomain` unconditionally — it finishes by cancelling the multiplier `M`
from `M * (lhs - rhs) = 0`, which needs `NoZeroDivisors`.

But when the certificate has no nondegeneracy factors the multiplier is `1`, and there is
nothing to cancel. `wu` now detects that and takes a domain-free route, which is what lets
the theorems below be stated over a bare `CommRing` and instantiated here. Rings of
functions are precisely the rings one wants to instantiate a differential-algebra result
at, so this was worth fixing rather than working around.

Theorems that *do* carry nondegeneracy conditions still need a domain, and that is not an
artefact: on a function ring the honest statement needs the multiplier to be a unit —
nowhere vanishing — which is `Wu.eq_zero_of_isUnit_mul` in `CharSetTac/DiffSheaf.lean`.

## What this is not

This is a bridge to *differential algebra* on a manifold, not to Riemannian geometry.
As of Mathlib v4.33.0 there are no Christoffel symbols, no Levi-Civita connection (Mathlib
cannot construct any connection — see the `TODO` at
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean:484`), and no
curvature of any kind: `grep -rni curvature Mathlib/` returns a single hit, and it is prose
in an unrelated measure-theory file. `WuDifferential/Curvature.lean` and the geometric half
of `PDE.lean` therefore stay in hand-rolled coordinates, because there is nothing in
Mathlib to state them against.
-/

open scoped Differential Manifold ContDiff

namespace Wu

/-! ### Domain-free consequences

These are the theorems from `WuDifferential/Theorems.lean` whose certificates need no
nondegeneracy condition, restated over a bare `CommRing` so that they apply to function
rings. The proofs are unchanged — only the hypotheses are weaker. -/

section CommRingOnly
variable {R : Type*} [CommRing R] [Differential R]

/-- `y′ = y` implies `y″ = y`: the exponential satisfies every higher-order version of its
own equation. No nondegeneracy condition, so no domain assumption. -/
theorem exp_second_commRing (y : R) (h : y′ = y) : (y′)′ = y := by
  have h' : (y′)′ = y′ := Wu.deriv_congr h
  wu

/-- The harmonic oscillator, obtained by eliminating `v` from the first-order system. -/
theorem harmonic_commRing (u v : R) (h₁ : u′ = v) (h₂ : v′ = -u) (h₁' : (u′)′ = v′) :
    (u′)′ + u = 0 := by
  wu

/-- A linear system with constant coefficients: `u′ = v`, `v′ = u` gives `u″ = u`. -/
theorem hyperbolic_commRing (u v : R) (h₁ : u′ = v) (h₂ : v′ = u) (h₁' : (u′)′ = v′) :
    (u′)′ = u := by
  wu

end CommRingOnly

/-! ### The bridge -/

section Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **A vector field makes the smooth functions a differential ring.**

`Differential` asks for a `Derivation ℤ R R`; a vector field is a `Derivation ℝ` of the
same ring, and restricting scalars along `ℤ → ℝ` is all that is needed. -/
noncomputable def differentialOfVectorField
    (X : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) : Differential C^∞⟮I, M; ℝ⟯ :=
  ⟨X.restrictScalars ℤ⟩

/-- An eigenfunction of a directional derivative satisfies the second-order equation too.

This is `exp_second_commRing` at `R = C^∞⟮I, M; ℝ⟯`: a statement about genuine smooth
functions on a genuine manifold, proved by the algebraic engine. -/
theorem exp_second_smooth (X : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)
    (y : C^∞⟮I, M; ℝ⟯) :
    letI := differentialOfVectorField X
    y′ = y → (y′)′ = y :=
  letI := differentialOfVectorField X
  fun h => exp_second_commRing y h

/-- The harmonic oscillator for a pair of smooth functions along a vector field. -/
theorem harmonic_smooth (X : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯)
    (u v : C^∞⟮I, M; ℝ⟯) :
    letI := differentialOfVectorField X
    u′ = v → v′ = -u → (u′)′ = v′ → (u′)′ + u = 0 :=
  letI := differentialOfVectorField X
  fun h₁ h₂ h₁' => harmonic_commRing u v h₁ h₂ h₁'

end Manifold

end Wu
