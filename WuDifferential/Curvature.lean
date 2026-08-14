/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Frontend

/-!
# Christoffel symbols and curvature identities

Curvature computations are polynomial once denominators are cleared. For a surface metric
with coefficients `E, F, G` and `W = EG - F²`, the Christoffel symbols are

```
2W Γ¹₁₁ = G E_u - 2F F_u + F E_v      2W Γ²₁₁ = 2E F_u - E E_v - F E_u
2W Γ¹₁₂ = G E_v - F G_u               2W Γ²₁₂ = E G_u - F E_v
2W Γ¹₂₂ = 2G F_v - G G_u - F G_v      2W Γ²₂₂ = E G_v - 2F F_v + F G_u
```

and everything downstream — metric compatibility, the contracted symbols, the Gauss
equation — is a polynomial identity in these and the metric derivatives.

**`W ≠ 0` is exactly regularity of the metric** (the conditions below are written as
`2W ≠ 0`, which is regularity together with characteristic ≠ 2 — both already assumed), so the nondegeneracy condition Wu's method
needs here is the hypothesis one would state anyway. That is the recurring pattern in this
subject: the multipliers are the things that are nonzero by definition.

Coordinates are written as independent symbols (`Eu` for `∂E/∂u` and so on) rather than as
applications of a `Derivation`, because these identities are *algebraic* consequences of
the Christoffel definitions — no prolongation is involved, so no differential structure is
needed to state them.
-/

namespace WuCurvature

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-! ### Metric compatibility: `∇g = 0`

The defining property of the Levi-Civita connection. In coordinates,
`∂_k g_ij = Γˡ_ki g_lj + Γˡ_kj g_il`, and for a surface the `(1,1)` component in the `u`
direction reads `E_u = 2(E Γ¹₁₁ + F Γ²₁₁)`.

That this follows from the Christoffel formulas is exactly the kind of polynomial
consequence the tactic is for: substituting the two definitions and cancelling leaves
`E_u · W / W`. -/

/-- Metric compatibility, `(1,1)` component, `u` direction. -/
theorem metric_compat_Eu (E F G W Eu Ev Fu G111 G211 : R) (hW0 : 2 * (E * G) - 2 * F ^ 2 ≠ 0)
    (hW : E * G - F * F = W)
    (h111 : 2 * W * G111 = G * Eu - 2 * F * Fu + F * Ev)
    (h211 : 2 * W * G211 = 2 * E * Fu - E * Ev - F * Eu) :
    Eu = 2 * (E * G111 + F * G211) := by
  wu (vars := [E, F, G, Eu, Ev, Fu, W, G111, G211])

/-- Metric compatibility, `(1,1)` component, `v` direction: `E_v = 2(E Γ¹₁₂ + F Γ²₁₂)`. -/
theorem metric_compat_Ev (E F G W Ev Gu G112 G212 : R) (hW0 : 2 * (E * G) - 2 * F ^ 2 ≠ 0)
    (hW : E * G - F * F = W)
    (h112 : 2 * W * G112 = G * Ev - F * Gu)
    (h212 : 2 * W * G212 = E * Gu - F * Ev) :
    Ev = 2 * (E * G112 + F * G212) := by
  wu (vars := [E, F, G, Ev, Gu, W, G112, G212])

/-- Metric compatibility, `(2,2)` component, `v` direction: `G_v = 2(F Γ¹₂₂ + G Γ²₂₂)`. -/
theorem metric_compat_Gv (E F G W Gu Gv Fv G122 G222 : R) (hW0 : 2 * (E * G) - 2 * F ^ 2 ≠ 0)
    (hW : E * G - F * F = W)
    (h122 : 2 * W * G122 = 2 * G * Fv - G * Gu - F * Gv)
    (h222 : 2 * W * G222 = E * Gv - 2 * F * Fv + F * Gu) :
    Gv = 2 * (F * G122 + G * G222) := by
  wu (vars := [E, F, G, Gu, Gv, Fv, W, G122, G222])

/-! ### The contracted Christoffel symbol

`Γⁱ_{i1} = ∂_u log √(det g)` — the identity that makes the divergence formula
`∇_i V^i = (1/√g) ∂_i(√g V^i)` work, and the reason `√det g` appears in every integral on a
manifold. In cleared form: `2W(Γ¹₁₁ + Γ²₁₂) = W_u`. -/

/-- The contracted Christoffel symbols give the logarithmic derivative of the metric
determinant. -/
theorem contracted_christoffel (E F G W Eu Ev Fu Gu Wu G111 G212 : R)
    (hW0 : 2 * (E * G) - 2 * F ^ 2 ≠ 0)
    (hW : E * G - F * F = W)
    (hWu : Eu * G + E * Gu - 2 * F * Fu = Wu)
    (h111 : 2 * W * G111 = G * Eu - 2 * F * Fu + F * Ev)
    (h212 : 2 * W * G212 = E * Gu - F * Ev) :
    2 * W * (G111 + G212) = Wu := by
  wu (vars := [E, F, G, Eu, Ev, Fu, Gu, W, Wu, G111, G212])

/-! ### Orthogonal coordinates

With `F = 0` the symbols collapse to the classical forms `Γ¹₁₁ = E_u/(2E)`,
`Γ²₁₁ = -E_v/(2G)`, `Γ¹₁₂ = E_v/(2E)`, `Γ²₁₂ = G_u/(2G)`, `Γ¹₂₂ = -G_u/(2E)`,
`Γ²₂₂ = G_v/(2G)`. These are the coordinates in which the Gauss equation is usually
written, and in which the Codazzi equations of `WuDifferential/PDE.lean` are stated. -/

/-- In orthogonal coordinates the general formula reduces to the classical one. -/
theorem christoffel_orthogonal (E G Eu Ev G111 G211 : R)
    (hEG : 2 * (E * G) ≠ 0)
    (h111 : 2 * (E * G) * G111 = G * Eu)
    (h211 : 2 * (E * G) * G211 = -(E * Ev)) :
    2 * E * G111 = Eu ∧ 2 * G * G211 = -Ev := by
  constructor
  · wu (vars := [E, G, Eu, Ev, G111, G211])
  · wu (vars := [E, G, Eu, Ev, G211, G111])

/-- The contracted symbol in orthogonal coordinates: `Γ¹₁₁ + Γ²₁₂ = (EG)_u / (2EG)`. -/
theorem contracted_orthogonal (E G Eu Gu G111 G212 : R) (hE : E ≠ 0) (hG : G ≠ 0)
    (h111 : 2 * E * G111 = Eu) (h212 : 2 * G * G212 = Gu) :
    2 * E * G * (G111 + G212) = Eu * G + E * Gu := by
  wu (vars := [E, G, Eu, Gu, G111, G212])

end WuCurvature
