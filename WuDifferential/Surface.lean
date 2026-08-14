/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Frontend
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Parametrised surfaces: the fundamental forms, derived

`WuDifferential/Curvature.lean` states the Christoffel relations as *hypotheses* — `E`,
`F`, `G`, `Eu`, `Ev`, … are bare ring variables and `2W·Γ¹₁₁ = G·Eu - 2F·Fu + F·Ev` is
assumed. That is honest as far as it goes, but the equations come from nowhere.

This file derives them instead, from a parametrised surface and Mathlib's `fderiv`.

## Setup

A surface is a map `f : ℝ × ℝ → V` into a real inner product space, together with a unit
normal field `n` orthogonal to both tangent vectors. Taking `n` as given data rather than
building it from a cross product costs nothing — the three conditions `⟪n, f_u⟫ = 0`,
`⟪n, f_v⟫ = 0`, `⟪n, n⟫ = 1` are all that is ever used — and it means the development is
not tied to `ℝ³`.

## Why this route, and not the Riemannian one

Mathlib has Riemannian metrics but **no connection** (it cannot construct one — see the
`TODO` at `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean:484`), no
Christoffel symbols, and no curvature. So there is no abstract tower to hang this on. The
classical parametrised-surface route needs none of it: everything below is `fderiv` on
`ℝ × ℝ` plus the inner product, both of which Mathlib has thoroughly.

The pay-off is that the Christoffel symbols become *definitions* — the coefficients of the
second derivatives in the frame `{f_u, f_v, n}` — rather than assumptions, and the
identities relating them to `E, F, G` become *theorems*.
-/

open scoped RealInnerProductSpace ContDiff

namespace WuSurface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### Partial derivatives -/

/-- Partial derivative in the first coordinate. -/
noncomputable def d1 (g : ℝ × ℝ → V) (p : ℝ × ℝ) : V := fderiv ℝ g p (1, 0)

/-- Partial derivative in the second coordinate. -/
noncomputable def d2 (g : ℝ × ℝ → V) (p : ℝ × ℝ) : V := fderiv ℝ g p (0, 1)

/-- A partial derivative of a smooth map is smooth, so the construction iterates. -/
theorem contDiff_d1 {g : ℝ × ℝ → V} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (d1 g) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_d2 {g : ℝ × ℝ → V} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (d2 g) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

/-! ### Leibniz for the inner product

The one analytic input the algebra needs: differentiating `⟪a, b⟫` gives
`⟪a′, b⟫ + ⟪a, b′⟫`. Everything downstream is a consequence of this and of Schwarz. -/

theorem d1_inner {a b : ℝ × ℝ → V} {p : ℝ × ℝ}
    (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p) :
    d1 (fun q => ⟪a q, b q⟫) p = ⟪a p, d1 b p⟫ + ⟪d1 a p, b p⟫ :=
  fderiv_inner_apply ℝ ha hb _

theorem d2_inner {a b : ℝ × ℝ → V} {p : ℝ × ℝ}
    (ha : DifferentiableAt ℝ a p) (hb : DifferentiableAt ℝ b p) :
    d2 (fun q => ⟪a q, b q⟫) p = ⟪a p, d2 b p⟫ + ⟪d2 a p, b p⟫ :=
  fderiv_inner_apply ℝ ha hb _

/-! ### The first fundamental form -/

variable (f : ℝ × ℝ → V)

/-- `E = ⟪f_u, f_u⟫`. -/
noncomputable def E (p : ℝ × ℝ) : ℝ := ⟪d1 f p, d1 f p⟫

/-- `F = ⟪f_u, f_v⟫`. -/
noncomputable def F (p : ℝ × ℝ) : ℝ := ⟪d1 f p, d2 f p⟫

/-- `G = ⟪f_v, f_v⟫`. -/
noncomputable def G (p : ℝ × ℝ) : ℝ := ⟪d2 f p, d2 f p⟫

variable {f}

-- `E f` is eta-contracted in `d1 (E f) p`, so `rw [E]` finds nothing to rewrite; unfold it
-- to the explicit lambda first, which holds by `rfl`.
private theorem E_eq : E f = fun q => ⟪d1 f q, d1 f q⟫ := rfl
private theorem F_eq : F f = fun q => ⟪d1 f q, d2 f q⟫ := rfl
private theorem G_eq : G f = fun q => ⟪d2 f q, d2 f q⟫ := rfl

/-- **`E_u = 2⟪f_uu, f_u⟫`** — derived, where `Curvature.lean` would assume it. -/
theorem d1_E (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    d1 (E f) p = 2 * ⟪d1 (d1 f) p, d1 f p⟫ := by
  have h := (contDiff_d1 hf).differentiable (by simp) p
  rw [E_eq, d1_inner h h, real_inner_comm]
  ring

/-- `E_v = 2⟪f_uv, f_u⟫`. -/
theorem d2_E (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    d2 (E f) p = 2 * ⟪d2 (d1 f) p, d1 f p⟫ := by
  have h := (contDiff_d1 hf).differentiable (by simp) p
  rw [E_eq, d2_inner h h, real_inner_comm]
  ring

/-- `G_u = 2⟪f_vu, f_v⟫`. -/
theorem d1_G (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    d1 (G f) p = 2 * ⟪d1 (d2 f) p, d2 f p⟫ := by
  have h := (contDiff_d2 hf).differentiable (by simp) p
  rw [G_eq, d1_inner h h, real_inner_comm]
  ring

/-- `G_v = 2⟪f_vv, f_v⟫`. -/
theorem d2_G (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    d2 (G f) p = 2 * ⟪d2 (d2 f) p, d2 f p⟫ := by
  have h := (contDiff_d2 hf).differentiable (by simp) p
  rw [G_eq, d2_inner h h, real_inner_comm]
  ring

/-- `F_u = ⟪f_u, f_vu⟫ + ⟪f_uu, f_v⟫`. -/
theorem d1_F (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    d1 (F f) p = ⟪d1 f p, d1 (d2 f) p⟫ + ⟪d1 (d1 f) p, d2 f p⟫ := by
  rw [F_eq, d1_inner ((contDiff_d1 hf).differentiable (by simp) p)
        ((contDiff_d2 hf).differentiable (by simp) p)]

/-- `F_v = ⟪f_u, f_vv⟫ + ⟪f_uv, f_v⟫`. -/
theorem d2_F (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    d2 (F f) p = ⟪d1 f p, d2 (d2 f) p⟫ + ⟪d2 (d1 f) p, d2 f p⟫ := by
  rw [F_eq, d2_inner ((contDiff_d1 hf).differentiable (by simp) p)
        ((contDiff_d2 hf).differentiable (by simp) p)]

/-! ### Symmetry of second partials

The other analytic input. Mathlib proves it as `ContDiffAt.isSymmSndFDerivAt`, stated for
the second `fderiv` as a bilinear object; getting from there to `∂₁∂₂ = ∂₂∂₁` on our
partial derivatives is `fderiv_clm_apply` with a constant second argument. -/

/-- Evaluating a `fderiv` at a fixed direction commutes with differentiating: the `v` slot
is constant, so only the second derivative moves. -/
private theorem fderiv_apply_const {g : ℝ × ℝ → V} {p : ℝ × ℝ}
    (hg : DifferentiableAt ℝ (fderiv ℝ g) p) (v w : ℝ × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ g q v) p w = fderiv ℝ (fderiv ℝ g) p w v := by
  rw [fderiv_clm_apply hg (differentiableAt_const _)]
  simp

/-- **`f_uv = f_vu`.** -/
theorem d_swap (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) : d2 (d1 f) p = d1 (d2 f) p := by
  -- pin the smoothness level: left as a metavariable, `simp` cannot discharge `?m + 1 ≤ ∞`
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p := by
    have h : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
    exact h.differentiable (by simp) p
  show fderiv ℝ (fun q => fderiv ℝ f q (1, 0)) p (0, 1)
     = fderiv ℝ (fun q => fderiv ℝ f q (0, 1)) p (1, 0)
  rw [fderiv_apply_const hd, fderiv_apply_const hd]
  -- `simp` reduces `minSmoothness ℝ 2 ≤ ∞` to `2 ≤ ∞` but stops there; `∞` is not `⊤` in
  -- `WithTop ℕ∞` (that is `ω`), so `le_top` does not apply directly.
  exact hf.contDiffAt.isSymmSndFDerivAt
    (by simp; exact WithTop.coe_le_coe.mpr le_top) _ _

/-! ### The six second-derivative inner products

**This is the section that replaces `Curvature.lean`'s hypotheses.** Each of these is
assumed there and proved here, from the definitions of `E`, `F`, `G` and the two analytic
facts above. Together they are what makes the Christoffel symbols determinate. -/

theorem inner_d11_d1 (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    ⟪d1 (d1 f) p, d1 f p⟫ = d1 (E f) p / 2 := by rw [d1_E hf]; ring

theorem inner_d21_d1 (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    ⟪d2 (d1 f) p, d1 f p⟫ = d2 (E f) p / 2 := by rw [d2_E hf]; ring

theorem inner_d21_d2 (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    ⟪d2 (d1 f) p, d2 f p⟫ = d1 (G f) p / 2 := by rw [d1_G hf, d_swap hf]; ring

theorem inner_d22_d2 (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    ⟪d2 (d2 f) p, d2 f p⟫ = d2 (G f) p / 2 := by rw [d2_G hf]; ring

/-- `⟪f_uu, f_v⟫ = F_u - E_v/2`. The one that genuinely needs both inputs. -/
theorem inner_d11_d2 (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    ⟪d1 (d1 f) p, d2 f p⟫ = d1 (F f) p - d2 (E f) p / 2 := by
  have h := d1_F hf p
  rw [← d_swap hf] at h
  -- `real_inner_comm x y : ⟪y, x⟫ = ⟪x, y⟫` — the explicit argument is the *second* slot
  rw [h, real_inner_comm (d2 (d1 f) p) (d1 f p), inner_d21_d1 hf]
  ring

/-- `⟪f_vv, f_u⟫ = F_v - G_u/2`. -/
theorem inner_d22_d1 (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    ⟪d2 (d2 f) p, d1 f p⟫ = d2 (F f) p - d1 (G f) p / 2 := by
  rw [d2_F hf, ← inner_d21_d2 hf, real_inner_comm (d2 (d2 f) p) (d1 f p)]
  ring

/-! ### Gauss–Weingarten, and the Christoffel symbols as derived quantities

Where the two halves meet. A surface point has the frame `{f_u, f_v, n}`; expanding a
second derivative in it *defines* the Christoffel symbols as its tangential coefficients.
Pairing that decomposition against `f_u` and `f_v` gives two linear equations, whose
right-hand sides are the inner products **derived** above rather than assumed.

Eliminating the unwanted coefficient from those two equations is a polynomial elimination —
so it is `wu` that closes the gap, and what comes out is precisely the relation
`WuDifferential/Curvature.lean` takes as a hypothesis. -/

section Frame

variable {p : ℝ × ℝ} {n : V} {c₁ c₂ l : ℝ}

/-- Pairing a frame decomposition `w = c₁ f_u + c₂ f_v + l n` against `f_u`. The normal
term drops out, which is the only thing orthogonality is ever used for. -/
theorem inner_frame_d1 {w : V} (hn1 : ⟪n, d1 f p⟫ = 0)
    (hw : w = c₁ • d1 f p + c₂ • d2 f p + l • n) :
    ⟪w, d1 f p⟫ = c₁ * E f p + c₂ * F f p := by
  rw [hw, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, hn1]
  rw [show ⟪d2 f p, d1 f p⟫ = F f p from real_inner_comm _ _]
  rw [show ⟪d1 f p, d1 f p⟫ = E f p from rfl]
  ring

/-- The same against `f_v`. -/
theorem inner_frame_d2 {w : V} (hn2 : ⟪n, d2 f p⟫ = 0)
    (hw : w = c₁ • d1 f p + c₂ • d2 f p + l • n) :
    ⟪w, d2 f p⟫ = c₁ * F f p + c₂ * G f p := by
  rw [hw, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, hn2]
  rw [show ⟪d1 f p, d2 f p⟫ = F f p from rfl]
  rw [show ⟪d2 f p, d2 f p⟫ = G f p from rfl]
  ring

/-- **`2W Γ¹₁₁ = G E_u - 2F F_u + F E_v`.**

This is `WuDifferential/Curvature.lean`'s hypothesis `h111`, here a *theorem*: the inputs
are the frame decomposition of `f_uu` and the derived inner products, and the elimination
of `Γ²₁₁` between the two pairings is done by `wu`.

**No regularity hypothesis is needed.** `wu` returns a certificate with multiplier `1`, so
`EG - F² ≠ 0` never enters. That is not an accident of this proof: stating the relation in
*cleared* form `2W·Γ¹₁₁ = …` rather than solving for `Γ¹₁₁` means nothing is ever divided
by `W`. Regularity is needed to recover `Γ¹₁₁` itself, not to state this. The hand-written
version in `Curvature.lean` carries `2W ≠ 0` throughout; it did not have to. -/
theorem christoffel_111 (hf : ContDiff ℝ ∞ f) (hn1 : ⟪n, d1 f p⟫ = 0)
    (hn2 : ⟪n, d2 f p⟫ = 0)
    (hdec : d1 (d1 f) p = c₁ • d1 f p + c₂ • d2 f p + l • n) :
    2 * (E f p * G f p - F f p ^ 2) * c₁
      = G f p * d1 (E f) p - 2 * F f p * d1 (F f) p + F f p * d2 (E f) p := by
  have h₁ : c₁ * E f p + c₂ * F f p = d1 (E f) p / 2 := by
    rw [← inner_frame_d1 hn1 hdec, inner_d11_d1 hf]
  have h₂ : c₁ * F f p + c₂ * G f p = d1 (F f) p - d2 (E f) p / 2 := by
    rw [← inner_frame_d2 hn2 hdec, inner_d11_d2 hf]
  wu

/-- **`2W Γ²₁₁ = 2E F_u - E E_v - F E_u`** — Curvature.lean's `h211`, likewise derived. -/
theorem christoffel_211 (hf : ContDiff ℝ ∞ f) (hn1 : ⟪n, d1 f p⟫ = 0)
    (hn2 : ⟪n, d2 f p⟫ = 0)
    (hdec : d1 (d1 f) p = c₁ • d1 f p + c₂ • d2 f p + l • n) :
    2 * (E f p * G f p - F f p ^ 2) * c₂
      = 2 * E f p * d1 (F f) p - E f p * d2 (E f) p - F f p * d1 (E f) p := by
  have h₁ : c₁ * E f p + c₂ * F f p = d1 (E f) p / 2 := by
    rw [← inner_frame_d1 hn1 hdec, inner_d11_d1 hf]
  have h₂ : c₁ * F f p + c₂ * G f p = d1 (F f) p - d2 (E f) p / 2 := by
    rw [← inner_frame_d2 hn2 hdec, inner_d11_d2 hf]
  wu

/-- **`2W Γ¹₁₂ = G E_v - F G_u`** — the mixed symbol, from the decomposition of `f_uv`. -/
theorem christoffel_112 (hf : ContDiff ℝ ∞ f) (hn1 : ⟪n, d1 f p⟫ = 0)
    (hn2 : ⟪n, d2 f p⟫ = 0)
    (hdec : d2 (d1 f) p = c₁ • d1 f p + c₂ • d2 f p + l • n) :
    2 * (E f p * G f p - F f p ^ 2) * c₁
      = G f p * d2 (E f) p - F f p * d1 (G f) p := by
  have h₁ : c₁ * E f p + c₂ * F f p = d2 (E f) p / 2 := by
    rw [← inner_frame_d1 hn1 hdec, inner_d21_d1 hf]
  have h₂ : c₁ * F f p + c₂ * G f p = d1 (G f) p / 2 := by
    rw [← inner_frame_d2 hn2 hdec, inner_d21_d2 hf]
  wu

/-- **`2W Γ²₁₂ = E G_u - F E_v`** — Curvature.lean's `h212`. -/
theorem christoffel_212 (hf : ContDiff ℝ ∞ f) (hn1 : ⟪n, d1 f p⟫ = 0)
    (hn2 : ⟪n, d2 f p⟫ = 0)
    (hdec : d2 (d1 f) p = c₁ • d1 f p + c₂ • d2 f p + l • n) :
    2 * (E f p * G f p - F f p ^ 2) * c₂
      = E f p * d1 (G f) p - F f p * d2 (E f) p := by
  have h₁ : c₁ * E f p + c₂ * F f p = d2 (E f) p / 2 := by
    rw [← inner_frame_d1 hn1 hdec, inner_d21_d1 hf]
  have h₂ : c₁ * F f p + c₂ * G f p = d1 (G f) p / 2 := by
    rw [← inner_frame_d2 hn2 hdec, inner_d21_d2 hf]
  wu

end Frame

end WuSurface
