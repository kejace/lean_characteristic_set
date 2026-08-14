/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuDifferential.SurfaceGauss

/-!
# The normal connection of a surface in codimension two

The third integrability condition. `WuDifferential/SurfaceGauss.lean` handles a single
normal; here there are two, `n₁` and `n₂`, orthonormal and both orthogonal to the tangent
plane.

With two normals there is something new to differentiate: the **normal connection**. Its
1-form is

```
s₁ = ⟪(n₁)_u, n₂⟫        s₂ = ⟪(n₁)_v, n₂⟫
```

measuring how fast the normal frame rotates within the normal plane. In codimension one
this is identically absent — there is nothing for the normal to rotate into.

## What is derived here

`ricci_raw` is the whole analytic content, and it is pure Schwarz: differentiating `s₁` in
`v` and `s₂` in `u`, the third-derivative terms `(n₁)_uv` and `(n₁)_vu` cancel, leaving

```
∂_v s₁ - ∂_u s₂ = ⟪(n₁)_u, (n₂)_v⟫ - ⟪(n₁)_v, (n₂)_u⟫
```

Notably this needs **no orthogonality at all** — not `⟪n₁,n₂⟫ = 0`, not the unit
conditions. It is the commutation of partial derivatives and nothing else. The geometry
enters only when the right-hand side is expanded in the frame, which is the elimination
step in `WuDifferential/SurfaceCodim2.lean`.

`skew` records the one orthogonality fact that step does need: the connection is
skew-symmetric, `⟪(n₂)_u, n₁⟫ = -s₁`, which is `⟪n₁, n₂⟫ = 0` differentiated.

This file does not import `CharSetTac`.
-/

open scoped RealInnerProductSpace ContDiff

namespace WuSurface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section NormalConnection

variable (n₁ n₂ : ℝ × ℝ → V)

/-- The `u` component of the normal connection form. -/
noncomputable def s₁ (p : ℝ × ℝ) : ℝ := ⟪d1 n₁ p, n₂ p⟫

/-- The `v` component of the normal connection form. -/
noncomputable def s₂ (p : ℝ × ℝ) : ℝ := ⟪d2 n₁ p, n₂ p⟫

variable {n₁ n₂}

/-- **The raw Ricci relation.** `∂_v s₁ - ∂_u s₂` is the antisymmetrised pairing of the two
normals' derivatives.

This is Schwarz and nothing else: no orthogonality, no unit conditions, no relation to the
surface. The curvature of the normal connection is a commutator of partial derivatives
before it is anything geometric. -/
theorem ricci_raw (h₁ : ContDiff ℝ ∞ n₁) (h₂ : ContDiff ℝ ∞ n₂) (p : ℝ × ℝ) :
    d2 (s₁ n₁ n₂) p - d1 (s₂ n₁ n₂) p
      = ⟪d1 n₁ p, d2 n₂ p⟫ - ⟪d2 n₁ p, d1 n₂ p⟫ := by
  have hd1 := (contDiff_d1 h₁).differentiable (by simp) p
  have hd2 := (contDiff_d2 h₁).differentiable (by simp) p
  have hn := h₂.differentiable (by simp) p
  have e1 : d2 (s₁ n₁ n₂) p = ⟪d2 (d1 n₁) p, n₂ p⟫ + ⟪d1 n₁ p, d2 n₂ p⟫ := by
    rw [show s₁ n₁ n₂ = fun q => ⟪d1 n₁ q, n₂ q⟫ from rfl, d2_inner hd1 hn]; ring
  have e2 : d1 (s₂ n₁ n₂) p = ⟪d1 (d2 n₁) p, n₂ p⟫ + ⟪d2 n₁ p, d1 n₂ p⟫ := by
    rw [show s₂ n₁ n₂ = fun q => ⟪d2 n₁ q, n₂ q⟫ from rfl, d1_inner hd2 hn]; ring
  rw [e1, e2, d_swap h₁ p]
  ring

/-- **The normal connection is skew.** `⟪(n₂)_u, n₁⟫ = -s₁`, from `⟪n₁, n₂⟫ = 0`.

This is what makes the normal plane rotate rigidly rather than deform, and it is the only
orthogonality fact the Ricci elimination needs. -/
theorem skew₁ (h₁ : ContDiff ℝ ∞ n₁) (h₂ : ContDiff ℝ ∞ n₂)
    (h₁₂ : ∀ q, ⟪n₁ q, n₂ q⟫ = (0 : ℝ)) (p : ℝ × ℝ) :
    ⟪d1 n₂ p, n₁ p⟫ = -s₁ n₁ n₂ p := by
  have h0 : d1 (fun q => ⟪n₁ q, n₂ q⟫) p = 0 := by
    rw [show (fun q => ⟪n₁ q, n₂ q⟫) = fun _ : ℝ × ℝ => (0 : ℝ) from funext h₁₂, d1]; simp
  rw [d1_inner (h₁.differentiable (by simp) p) (h₂.differentiable (by simp) p)] at h0
  change ⟪d1 n₂ p, n₁ p⟫ = -⟪d1 n₁ p, n₂ p⟫
  rw [real_inner_comm (d1 n₂ p) (n₁ p)] at h0
  linarith

/-- The `v` counterpart of `skew₁`. -/
theorem skew₂ (h₁ : ContDiff ℝ ∞ n₁) (h₂ : ContDiff ℝ ∞ n₂)
    (h₁₂ : ∀ q, ⟪n₁ q, n₂ q⟫ = (0 : ℝ)) (p : ℝ × ℝ) :
    ⟪d2 n₂ p, n₁ p⟫ = -s₂ n₁ n₂ p := by
  have h0 : d2 (fun q => ⟪n₁ q, n₂ q⟫) p = 0 := by
    rw [show (fun q => ⟪n₁ q, n₂ q⟫) = fun _ : ℝ × ℝ => (0 : ℝ) from funext h₁₂, d2]; simp
  rw [d2_inner (h₁.differentiable (by simp) p) (h₂.differentiable (by simp) p)] at h0
  change ⟪d2 n₂ p, n₁ p⟫ = -⟪d2 n₁ p, n₂ p⟫
  rw [real_inner_comm (d2 n₂ p) (n₁ p)] at h0
  linarith

/-! ### The frame expansion

Expanding `⟪(n₁)_u, (n₂)_v⟫` in the frame is linearity plus the orthogonality relations,
and it is done where it is used, in `WuDifferential/SurfaceCodim2.lean` — the same
arrangement as `gauss_raw` and `gauss_equation`.

One feature of that expansion is worth recording here, because it is the reason the Ricci
equation is about the *tangential* data at all. Each `(n_α)_u` decomposes with an
`n`-component equal to `±s`, and pairing two such decompositions contributes
`s₁·(-s₂) + s₂·(s₁) = 0`: **the connection form cancels out of its own curvature.** What
survives is entirely the shape operators. -/

end NormalConnection

end WuSurface
