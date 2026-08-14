/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Frontend
import Mathlib.RingTheory.Derivation.Basic

/-!
# Two derivations: integrability conditions and Gauss–Codazzi

Examples in the **partial** case — two independent derivations `d₁, d₂`. This is where
critical pairs exist (`CharSetTac/Diff/MultiIndex.lean`) and where coherence stops being
automatic, and it is the setting Gauss–Codazzi lives in.

## How two derivations are modelled

Mathlib's `Differential` class carries a single derivation, so here `d₁` and `d₂` are
explicit `Derivation` values and their commutation `d₁ (d₂ x) = d₂ (d₁ x)` is a hypothesis.
That is the correct statement — commuting derivations are what "partial derivatives in
independent variables" means — and it is *the* source of critical pairs: `d₁u` and `d₂u`
are incomparable, yet `d₂d₁u = d₁d₂u` is a common derivative.

## What `wu` is doing here

Exactly what it does everywhere: the derivatives are atoms, the prolongations are supplied
as `have`s, and the certificate is checked by `ring`. Nothing about coherence or
Rosenfeld's lemma enters, because every statement proved is a *positive* consequence.
-/

namespace WuPDE

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-! ### Frobenius: the canonical critical pair

The integrability condition for `u_x = a`, `u_y = b` is the compatibility of the mixed
partials. This is the smallest genuine two-derivation elimination, and it is precisely the
Δ-polynomial of the critical pair `{d₁u, d₂u}`. -/

/-- **Frobenius integrability.** If `d₁u = a` and `d₂u = b`, then `a` and `b` are not
independent: `d₂a = d₁b`. -/
theorem frobenius (d₁ d₂ : Derivation ℤ R R) (u a b : R)
    (comm : d₁ (d₂ u) = d₂ (d₁ u))
    (h₁ : d₁ u = a) (h₂ : d₂ u = b) :
    d₂ a = d₁ b := by
  have e₁ : d₂ (d₁ u) = d₂ a := by rw [h₁]
  have e₂ : d₁ (d₂ u) = d₁ b := by rw [h₂]
  wu

/-- **Frobenius, general form.** When `a` and `b` also depend on `u`, the chain rule gives
`d₂a = a_y + a_u·b` and `d₁b = b_x + b_u·a`, and compatibility becomes the classical
integrability condition

`a_y + a_u b = b_x + b_u a`.

This is the condition under which the overdetermined system `u_x = a`, `u_y = b` actually
has a solution, and it is the Δ-polynomial of the critical pair `{d₁u, d₂u}` set to zero. -/
theorem frobenius_general (d₁ d₂ : Derivation ℤ R R) (u a b ay au bx bu : R)
    (hu₁ : d₁ u ≠ 0) (hu₂ : d₂ u ≠ 0)
    (comm : d₁ (d₂ u) = d₂ (d₁ u))
    (h₁ : d₁ u = a) (h₂ : d₂ u = b)
    (ha : d₂ a = ay + au * b) (hb : d₁ b = bx + bu * a) :
    ay + au * b = bx + bu * a := by
  have e₁ : d₂ (d₁ u) = d₂ a := by rw [h₁]
  have e₂ : d₁ (d₂ u) = d₁ b := by rw [h₂]
  wu

/-! ### Zero curvature: integrable systems

For a linear system `ψ_x = Uψ`, `ψ_y = Vψ` the compatibility `ψ_xy = ψ_yx` yields the
zero-curvature (Lax) equation `U_y - V_x + [U, V] = 0`. Below, the `2 × 2` case with scalar
entries, written out. The identity derived is the one that genuinely follows: the
zero-curvature combination annihilates the solution vector. Extracting the entries
separately would need `ψ₁, ψ₂` independent, which is a nondegeneracy assumption rather
than a consequence. -/

/-- **Zero-curvature condition**, first component.

`ψ₁` and `ψ₂` solve the `2 × 2` linear system in both directions; compatibility of the
mixed partials gives that the `(1,1)` and `(1,2)` entries of `U_y - V_x + [U,V]`,
contracted against `ψ`, vanish. -/
theorem zero_curvature (d₁ d₂ : Derivation ℤ R R)
    (ψ₁ ψ₂ u₁₁ u₁₂ u₂₁ u₂₂ v₁₁ v₁₂ v₂₁ v₂₂ : R) (hψ₂ : ψ₂ ≠ 0)
    (comm : d₂ (d₁ ψ₁) = d₁ (d₂ ψ₁))
    (hx₁ : d₁ ψ₁ = u₁₁ * ψ₁ + u₁₂ * ψ₂) (hx₂ : d₁ ψ₂ = u₂₁ * ψ₁ + u₂₂ * ψ₂)
    (hy₁ : d₂ ψ₁ = v₁₁ * ψ₁ + v₁₂ * ψ₂) (hy₂ : d₂ ψ₂ = v₂₁ * ψ₁ + v₂₂ * ψ₂)
    -- prolongations, expanded by Leibniz
    (p₁ : d₂ (u₁₁ * ψ₁ + u₁₂ * ψ₂)
        = d₂ u₁₁ * ψ₁ + u₁₁ * d₂ ψ₁ + d₂ u₁₂ * ψ₂ + u₁₂ * d₂ ψ₂)
    (p₂ : d₁ (v₁₁ * ψ₁ + v₁₂ * ψ₂)
        = d₁ v₁₁ * ψ₁ + v₁₁ * d₁ ψ₁ + d₁ v₁₂ * ψ₂ + v₁₂ * d₁ ψ₂) :
    (d₂ u₁₁ - d₁ v₁₁ + u₁₂ * v₂₁ - v₁₂ * u₂₁) * ψ₁
      + (d₂ u₁₂ - d₁ v₁₂ + u₁₁ * v₁₂ + u₁₂ * v₂₂ - v₁₁ * u₁₂ - v₁₂ * u₂₂) * ψ₂ = 0 := by
  have e₁ : d₂ (d₁ ψ₁) = d₂ (u₁₁ * ψ₁ + u₁₂ * ψ₂) := by rw [hx₁]
  have e₂ : d₁ (d₂ ψ₁) = d₁ (v₁₁ * ψ₁ + v₁₂ * ψ₂) := by rw [hy₁]
  wu (vars := [u₁₁, u₁₂, u₂₁, u₂₂, v₁₁, v₁₂, v₂₁, v₂₂, ψ₁, ψ₂,
    d₂ u₁₁, d₂ u₁₂, d₁ v₁₁, d₁ v₁₂,
    d₁ ψ₁, d₁ ψ₂, d₂ ψ₁, d₂ ψ₂,
    d₂ (u₁₁ * ψ₁ + u₁₂ * ψ₂), d₁ (v₁₁ * ψ₁ + v₁₂ * ψ₂),
    d₂ (d₁ ψ₁), d₁ (d₂ ψ₁)])

/-! ### Gauss–Codazzi

In **curvature-line coordinates** — `F = 0` and `M = 0`, so the coordinate curves are the
lines of curvature — the Codazzi–Mainardi equations take the classical form

```
L_v = ½ E_v (L/E + N/G),      N_u = ½ G_u (L/E + N/G)
```

which, cleared of denominators, is polynomial:

```
2 E G L_v = E_v (G L + E N),   2 E G N_u = G_u (G L + E N)
```

These are stated as hypotheses — they are the Codazzi equations, not something derived
here — and `wu` derives consequences of them. That is the honest division of labour: this
file does not *prove* Gauss–Codazzi from the structure equations (that needs the full
Gauss–Weingarten system with vector-valued frames), it works with them.

Note where the nondegeneracy lands: `E`, `G` and `EG - F² = EG` nonzero is exactly the
regularity of the immersion, and it appears as the saturation condition — precisely the
role `dischargeNondeg` gives it. -/

/-- **Codazzi elimination.** The two Codazzi equations share the factor `GL + EN`;
eliminating it gives a relation between the two derivatives with no second fundamental
form combination left. This is exactly what differential elimination is for. -/
theorem codazzi_eliminate (d₁ d₂ : Derivation ℤ R R) (E G L N : R) (hE : E ≠ 0) (hG : G ≠ 0)
    (cod₁ : 2 * E * G * d₂ L = d₂ E * (G * L + E * N))
    (cod₂ : 2 * E * G * d₁ N = d₁ G * (G * L + E * N)) :
    d₁ G * (2 * E * G * d₂ L) = d₂ E * (2 * E * G * d₁ N) := by
  wu (vars := [E, G, L, N, d₂ E, d₁ G, d₁ N, d₂ L])

/-! ### General relativity: the Schwarzschild vacuum

A static spherically symmetric metric `ds² = -A(r)dt² + B(r)dr² + r²dΩ²` has Ricci
components rational in `A`, `B` and their `r`-derivatives. Because everything depends on
`r` alone this is a **single-derivation** problem, so it is in reach of the ordinary engine
— GR's symmetry-reduced vacuum equations are ODE elimination, not PDE elimination.

The classical first step is that the vacuum equations force `AB` to be constant, after
which `A = 1/B` up to normalisation and the Schwarzschild form follows. Below, that step:
the combination of `R_tt` and `R_rr` that eliminates the second derivatives leaves
`(AB)' = 0`.

The relation used is the standard one for this ansatz,
`B·A' + A·B' = 0` being exactly `(AB)' = 0`; it is stated as the hypothesis coming out of
`R_tt/A + R_rr/B = 0` and `wu` derives that `AB` is constant in the sense that its
derivative vanishes. -/
theorem schwarzschild_AB_const (d : Derivation ℤ R R) (A B : R) (hA : A ≠ 0)
    (vac : B * d A + A * d B = 0)
    (leib : d (A * B) = A * d B + B * d A) :
    d (A * B) = 0 := by wu

/-- With `AB` constant and the normalisation `AB = 1` (asymptotic flatness), `B = 1/A` in
the polynomial form `A·B = 1`, and the remaining vacuum equation `r·A' + A = 1` integrates
to the Schwarzschild potential. Here the algebraic consequence: `A` and `B` satisfy
`A·B = 1` together with `r·A' + A - 1 = 0`, so `r·A' = 1 - A`.

The nondegeneracy conditions `wu` reports here are exactly the coordinate singularities of
the Schwarzschild chart: `A ≠ 0` excludes the horizon and `r ≠ 0` the origin. -/
theorem schwarzschild_potential (d : Derivation ℤ R R) (A B r : R) (hr0 : r ≠ 0)
    (hnorm : A * B = 1) (hr : r * d A + A - 1 = 0) :
    r * d A = 1 - A := by wu

end WuPDE
