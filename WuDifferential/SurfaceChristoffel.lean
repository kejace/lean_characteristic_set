/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuDifferential.Surface
import CharSetTac.Frontend

/-!
# The Christoffel relations, by `wu`

`WuDifferential/Surface.lean` derives the frame pairings from Mathlib's `fderiv`; this file
performs the algebraic step that turns them into the Christoffel relations, and does it with
the tactic.

Each theorem below is a hypothesis of `WuDifferential/Curvature.lean`, here proved. The
input is the frame decomposition of a second derivative plus the derived inner products;
the work is eliminating the unwanted coefficient between the two pairings.

`WuDifferential/SurfaceComparison.lean` proves the same four statements by hand, from the
same inputs, so the two can be read side by side.
-/

open scoped RealInnerProductSpace ContDiff

namespace WuSurface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {f : ℝ × ℝ → V} {p : ℝ × ℝ} {n : V} {c₁ c₂ l : ℝ}

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

end WuSurface
