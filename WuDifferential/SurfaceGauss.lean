/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuDifferential.Surface

/-!
# The second fundamental form, and the Gauss–Codazzi integrability conditions

Continues `WuDifferential/Surface.lean`. The normal is now a *field* `n : ℝ × ℝ → V`,
because both equations come from differentiating it.

## The mechanism

Everything below is one identity — `(f_uu)_v = (f_uv)_u`, which is `d_swap` applied to
`d1 f` — paired against the three frame directions:

* against **`n`** it gives **Codazzi**;
* against **`f_v`** it gives **Gauss**.

Pairing rather than equating coefficients is deliberate: equating coefficients needs
`{f_u, f_v, n}` to be a basis, which is extra work and extra hypotheses. The inner products
need only orthogonality, which is given.

## Nothing here is postulated

`L, M, N` are defined as inner products. The Weingarten pairings `⟪n_u, f_u⟫ = -L` and its
relatives are *derived*, by differentiating `⟪n, f_u⟫ = 0`. So is `⟪n_u, n⟫ = 0`, from
`⟪n, n⟫ = 1`. The only inputs are the normal-field conditions and smoothness.

This file, like `Surface.lean`, does not import `CharSetTac`: it produces the equations.
`WuDifferential/SurfaceGaussWu.lean` performs the elimination on them.
-/

open scoped RealInnerProductSpace ContDiff

namespace WuSurface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section SecondForm

variable (f n : ℝ × ℝ → V)

/-- `L = ⟪f_uu, n⟫`. -/
noncomputable def L (p : ℝ × ℝ) : ℝ := ⟪d1 (d1 f) p, n p⟫

/-- `M = ⟪f_uv, n⟫`. -/
noncomputable def M (p : ℝ × ℝ) : ℝ := ⟪d2 (d1 f) p, n p⟫

/-- `N = ⟪f_vv, n⟫`. -/
noncomputable def N (p : ℝ × ℝ) : ℝ := ⟪d2 (d2 f) p, n p⟫

variable {f n}

private theorem L_eq : L f n = fun q => ⟪d1 (d1 f) q, n q⟫ := rfl
private theorem M_eq : M f n = fun q => ⟪d2 (d1 f) q, n q⟫ := rfl

/-! ### Weingarten: the derivatives of the normal

Differentiating the three defining conditions of `n` gives its pairings against the frame.
None of this is assumed. -/

/-- From `⟪n, n⟫ = 1`: the normal's derivative is tangential. -/
theorem inner_d1n_n (hn : ContDiff ℝ ∞ n) (hnn : ∀ q, ⟪n q, n q⟫ = (1 : ℝ)) (p : ℝ × ℝ) :
    ⟪d1 n p, n p⟫ = 0 := by
  have hd := hn.differentiable (by simp) p
  have h0 : d1 (fun q => ⟪n q, n q⟫) p = 0 := by
    have : (fun q => ⟪n q, n q⟫) = fun _ : ℝ × ℝ => (1 : ℝ) := funext hnn
    rw [this, d1]; simp
  rw [d1_inner hd hd, real_inner_comm] at h0
  linarith

/-- The `v` counterpart: `⟪n_v, n⟫ = 0`. -/
theorem inner_d2n_n (hn : ContDiff ℝ ∞ n) (hnn : ∀ q, ⟪n q, n q⟫ = (1 : ℝ)) (p : ℝ × ℝ) :
    ⟪d2 n p, n p⟫ = 0 := by
  have hd := hn.differentiable (by simp) p
  have h0 : d2 (fun q => ⟪n q, n q⟫) p = 0 := by
    have : (fun q => ⟪n q, n q⟫) = fun _ : ℝ × ℝ => (1 : ℝ) := funext hnn
    rw [this, d2]; simp
  rw [d2_inner hd hd, real_inner_comm] at h0
  linarith

/-- From `⟪n, f_u⟫ = 0`: `⟪n_u, f_u⟫ = -L`. -/
theorem inner_d1n_d1f (hf : ContDiff ℝ ∞ f) (hn : ContDiff ℝ ∞ n)
    (hn1 : ∀ q, ⟪n q, d1 f q⟫ = (0 : ℝ)) (p : ℝ × ℝ) :
    ⟪d1 n p, d1 f p⟫ = -L f n p := by
  have h0 : d1 (fun q => ⟪n q, d1 f q⟫) p = 0 := by
    have : (fun q => ⟪n q, d1 f q⟫) = fun _ : ℝ × ℝ => (0 : ℝ) := funext hn1
    rw [this, d1]; simp
  rw [d1_inner (hn.differentiable (by simp) p)
      ((contDiff_d1 hf).differentiable (by simp) p)] at h0
  rw [L_eq]
  rw [real_inner_comm (d1 (d1 f) p) (n p)] at *
  linarith

/-- From `⟪n, f_u⟫ = 0` differentiated in `v`: `⟪n_v, f_u⟫ = -M`. -/
theorem inner_d2n_d1f (hf : ContDiff ℝ ∞ f) (hn : ContDiff ℝ ∞ n)
    (hn1 : ∀ q, ⟪n q, d1 f q⟫ = (0 : ℝ)) (p : ℝ × ℝ) :
    ⟪d2 n p, d1 f p⟫ = -M f n p := by
  have h0 : d2 (fun q => ⟪n q, d1 f q⟫) p = 0 := by
    have : (fun q => ⟪n q, d1 f q⟫) = fun _ : ℝ × ℝ => (0 : ℝ) := funext hn1
    rw [this, d2]; simp
  rw [d2_inner (hn.differentiable (by simp) p)
      ((contDiff_d1 hf).differentiable (by simp) p)] at h0
  rw [M_eq]
  rw [real_inner_comm (d2 (d1 f) p) (n p)] at *
  linarith

/-- From `⟪n, f_v⟫ = 0`: `⟪n_u, f_v⟫ = -M`, using `f_vu = f_uv`. -/
theorem inner_d1n_d2f (hf : ContDiff ℝ ∞ f) (hn : ContDiff ℝ ∞ n)
    (hn2 : ∀ q, ⟪n q, d2 f q⟫ = (0 : ℝ)) (p : ℝ × ℝ) :
    ⟪d1 n p, d2 f p⟫ = -M f n p := by
  have h0 : d1 (fun q => ⟪n q, d2 f q⟫) p = 0 := by
    have : (fun q => ⟪n q, d2 f q⟫) = fun _ : ℝ × ℝ => (0 : ℝ) := funext hn2
    rw [this, d1]; simp
  rw [d1_inner (hn.differentiable (by simp) p)
      ((contDiff_d2 hf).differentiable (by simp) p)] at h0
  -- Leibniz produced `f_vu`; Schwarz turns it into the `f_uv` that `M` is defined by
  rw [← d_swap hf p] at h0
  change ⟪d1 n p, d2 f p⟫ = -⟪d2 (d1 f) p, n p⟫
  rw [real_inner_comm (d2 (d1 f) p) (n p)] at h0
  linarith

/-- From `⟪n, f_v⟫ = 0` differentiated in `v`: `⟪n_v, f_v⟫ = -N`. -/
theorem inner_d2n_d2f (hf : ContDiff ℝ ∞ f) (hn : ContDiff ℝ ∞ n)
    (hn2 : ∀ q, ⟪n q, d2 f q⟫ = (0 : ℝ)) (p : ℝ × ℝ) :
    ⟪d2 n p, d2 f p⟫ = -N f n p := by
  have h0 : d2 (fun q => ⟪n q, d2 f q⟫) p = 0 := by
    have : (fun q => ⟪n q, d2 f q⟫) = fun _ : ℝ × ℝ => (0 : ℝ) := funext hn2
    rw [this, d2]; simp
  rw [d2_inner (hn.differentiable (by simp) p)
      ((contDiff_d2 hf).differentiable (by simp) p)] at h0
  rw [N]
  rw [real_inner_comm (d2 (d2 f) p) (n p)] at *
  linarith

/-- Pairing a frame decomposition against an **arbitrary** vector. Pure linearity — the
orthogonality of `n` is not used, because the target is not a frame vector. This is what
lets the same lemma serve for pairing against `n_u` and `n_v`. -/
theorem inner_frame_gen {p : ℝ × ℝ} {c₁ c₂ l : ℝ} {w z : V}
    (hw : w = c₁ • d1 f p + c₂ • d2 f p + l • n p) :
    ⟪w, z⟫ = c₁ * ⟪d1 f p, z⟫ + c₂ * ⟪d2 f p, z⟫ + l * ⟪n p, z⟫ := by
  rw [hw, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left]

/-! ### The Gauss identity, before any elimination

Pairing `(f_uu)_v = (f_uv)_u` against `f_v` and using Leibniz on both sides gives a relation
with **no Christoffel symbols in it at all** — just second and third derivatives of `f`.
This is the raw integrability condition; turning it into the Gauss equation is the
elimination step. -/

/-- `⟪f_uu, f_vv⟫ - ⟪f_uv, f_uv⟫ = (F_u - E_v/2)_v - (G_u/2)_u`.

The left side is `LN - M²` plus Christoffel terms once expanded in the frame; the right
side is second derivatives of the first fundamental form. That is the Gauss equation
waiting to be assembled. -/
theorem gauss_raw (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    ⟪d1 (d1 f) p, d2 (d2 f) p⟫ - ⟪d2 (d1 f) p, d2 (d1 f) p⟫
      = d2 (fun q => ⟪d1 (d1 f) q, d2 f q⟫) p - d1 (fun q => ⟪d2 (d1 f) q, d2 f q⟫) p := by
  have h11 := (contDiff_d1 (contDiff_d1 hf)).differentiable (by simp) p
  have h21 := (contDiff_d2 (contDiff_d1 hf)).differentiable (by simp) p
  have h1 := (contDiff_d1 hf).differentiable (by simp) p
  have h2 := (contDiff_d2 hf).differentiable (by simp) p
  rw [d2_inner h11 h2, d1_inner h21 h2]
  -- `(f_uu)_v = (f_uv)_u` is `d_swap` one level up
  rw [d_swap (contDiff_d1 hf) p]
  rw [← d_swap hf p]
  ring

end SecondForm

end WuSurface
