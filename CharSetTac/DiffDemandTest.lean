/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DiffDemand

/-!
# `wu_pde!` — demand-driven prolongation

## Why this exists, stated accurately

It was built to fix a failure that turned out to have a different cause. Harmonicity at
second order was failing, I attributed it to uniform prolongation generating too many
irrelevant mixed partials, and demand-driven prolongation was the proposed remedy.

The actual blocker was two missing simp lemmas — `d 1` and `d 2` surviving as spurious
atoms. With those fixed, the uniform tactic proves harmonicity too. **The diagnosis was
wrong and the enabling fix was elsewhere.**

## Why it survives anyway

Because it is much cheaper, which is a claim worth measuring rather than asserting. Same
theorem, same statement, `set_option Elab.async false`:

```
wu_pde  (order := 2)   52027 heartbeats     30-odd equations generated
wu_pde!                 4208                six
```

**12×.** Uniform prolongation generates every mixed partial of everything to the given
order; demand-driven generates only what the goal reaches. That gap widens with the number
of derivations and the order, so it decides what stays tractable even though it decided
nothing here.

## How it works

Start from the derivatives the *goal* mentions. For each, find the hypothesis whose leader
is the same base at a lower multi-index, and prolong that hypothesis by exactly the
difference. The new equation mentions further derivatives, so repeat to a fixpoint.

This is the rule differential elimination has always used — prolong to meet the leader you
are reducing against — applied at the tactic level rather than inside the engine.
-/

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Harmonicity of `Re(z²)`, second order in two derivations. -/
example (d₁ d₂ : Derivation ℤ R R) (x y u : R)
    (hx1 : d₁ x = 1) (hy1 : d₁ y = 0) (hx2 : d₂ x = 0) (hy2 : d₂ y = 1)
    (hu : u = x ^ 2 - y ^ 2) :
    d₁ (d₁ u) + d₂ (d₂ u) = 0 := by
  wu_pde! (derivs := [d₁, d₂])

/-- Harmonicity of the imaginary part, `Im(z²) = 2xy`. -/
example (d₁ d₂ : Derivation ℤ R R) (x y v : R)
    (hx1 : d₁ x = 1) (hy1 : d₁ y = 0) (hx2 : d₂ x = 0) (hy2 : d₂ y = 1)
    (hv : v = 2 * (x * y)) :
    d₁ (d₁ v) + d₂ (d₂ v) = 0 := by
  wu_pde! (derivs := [d₁, d₂])

/-- First order still works — the closure degenerates to what uniform prolongation does. -/
example (d₁ d₂ : Derivation ℤ R R) (x y u v : R)
    (hx1 : d₁ x = 1) (hy1 : d₁ y = 0) (hx2 : d₂ x = 0) (hy2 : d₂ y = 1)
    (hu : u = x ^ 2 - y ^ 2) (hv : v = 2 * (x * y)) :
    d₁ u = d₂ v := by
  wu_pde! (derivs := [d₁, d₂])

/-! ### An open case, flagged rather than explained

`d₁ (d₁ (d₁ u)) = 0` for the same quadratic `u` is **not** proved. The closure saturates at
18 hypotheses at any depth, so it is not a fixpoint-depth issue, and beyond that I have not
diagnosed it.

That last sentence is deliberate. The previous two things recorded in this project as
"limits of the frontend" — the logistic equation and second-order harmonicity — were both
*bugs*, and both were written up with confident-sounding mathematical explanations that were
wrong. A tactic reporting "does not follow" is making a claim about its input, and the input
deserves reading before the failure is described as a limitation.

So: this fails, the cause is unknown, and it should be diagnosed before anyone builds a
theory on top of it.
-/
