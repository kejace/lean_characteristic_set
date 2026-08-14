/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Frontend
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# Differential consequences via algebraic certificates

A feasibility probe for the differential setting, and the evidence behind a design claim:
**a certificate-checking tactic does not need Rosenfeld's lemma.**

## The argument

Rosenfeld's lemma is the bridge from differential to algebraic ideals. In the form used by
Boulier, Lemaire, Poteaux and Moreno Maza, *An equivalence theorem for regular differential
chains*, J. Symbolic Computation 93 (2019) 34-55, Proposition 35:

> Since `A` is a coherent set of pairwise partially reduced differential polynomials,
> Rosenfeld's Lemma applies and we have `[A] : h^∞ ∩ R₁ = (A) : h^∞`,

where `h` is the product of the initials **and separants** of `A`. That is: for elements
partially reduced with respect to a coherent chain, membership in the saturated
*differential* ideal coincides with membership in the saturated *algebraic* ideal.

That equivalence is what makes the Rosenfeld-Groebner *algorithm* correct and complete: it
is a statement about the method as a whole, and it is what you must formalize to prove the
decomposition procedure itself correct. A tactic that emits a checked certificate never
needs it, because it never claims completeness. It claims only that *this* identity holds,
and the identity is checked directly.

Note also where the saturation comes from: `h` includes the **separants**, and a separant
is exactly the initial of a prolonged equation. So the nondegeneracy conditions the
differential case needs are produced by the existing machinery with no special handling —
they are just more polynomials required not to vanish.

Concretely, the differential analogue of our algebraic certificate is

```
I * g = ∑ⱼ ∑_θ c_{j,θ} * θ(hⱼ)
```

where `θ` ranges over derivative operators. Soundness needs one elementary fact — that a
derivation sends `0` to `0`, so `hⱼ = 0` implies `θ(hⱼ) = 0` — and then `ring` closes the
identity with the derivatives treated as opaque atoms. Nothing about coherence,
autoreducedness, rankings, or saturated differential ideals enters the *checking* step.
All of that governs how an oracle *finds* the certificate, and the oracle is untrusted.

## What this file shows

That the existing algebraic engine already proves differential consequences, once the
differentiated ("prolonged") hypotheses are supplied. The prolongation step is the only
genuinely differential ingredient, and it is three lines.
-/

open scoped Differential

namespace Wu

variable {R : Type*} [CommRing R] [Differential R]

/-- Differentiating a hypothesis: from `a = 0` conclude `a′ = 0`.

This is the *only* differential fact the certificate route needs. It is immediate, because
a derivation is additive and therefore sends `0` to `0`. -/
theorem deriv_eq_zero {a : R} (h : a = 0) : a′ = 0 := by
  rw [h]; exact map_zero _

/-- Prolongation of an equation, in the form the tactic consumes: `a = b` gives
`a′ = b′`. -/
theorem deriv_congr {a b : R} (h : a = b) : a′ = b′ := by rw [h]

end Wu

section Examples

variable {R : Type*} [CommRing R] [IsDomain R] [Differential R]

/-- `y′ = y` implies `y″ = y`.

The certificate is `(y″ - y) = (y′ - y)′ + (y′ - y)`, i.e. one prolongation of the
hypothesis plus the hypothesis itself. `wu` finds and checks it with the derivatives as
atoms; the only differential input is `h'`. -/
example (y : R) (h : y′ = y) : (y′)′ = y := by
  have h' : (y′)′ = y′ := Wu.deriv_congr h
  wu

/-- A nonlinear one: `y′ = y ^ 2` implies `y″ = 2 * y ^ 3`.

Here the prolongation genuinely uses the Leibniz rule, and the resulting algebraic system
is not linear — exactly the situation Wu's method is for. -/
example (y : R) (h : y′ = y ^ 2) : (y′)′ = 2 * y ^ 3 := by
  have h' : (y′)′ = 2 * y * y′ := by
    rw [Wu.deriv_congr h, pow_two]
    rw [Derivation.leibniz]
    ring
  wu

/-- Two coupled equations, eliminating a variable.

`u′ = v` and `v′ = -u` give `u″ + u = 0`: the harmonic oscillator, derived by elimination
rather than by solving. -/
example (u v : R) (h₁ : u′ = v) (h₂ : v′ = -u) : (u′)′ + u = 0 := by
  have h₃ : (u′)′ = v′ := Wu.deriv_congr h₁
  wu

end Examples
