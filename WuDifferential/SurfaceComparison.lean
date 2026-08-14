/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuDifferential.Surface

/-!
# The Christoffel relations, by hand

The same four theorems as `WuDifferential/SurfaceChristoffel.lean`, from the same inputs,
without the tactic — so the two can be read side by side.

**This file does not import `CharSetTac`.** `WuDifferential/Surface.lean`, which supplies
the analytic input, does not either: it is `fderiv` and the inner product and nothing else.
So these proofs are genuinely independent of the tactic rather than merely avoiding the
`wu` token.

## What the comparison shows

Each proof is a `linear_combination` whose multipliers had to be computed by hand. For
`christoffel_111'` the elimination of `Γ²₁₁` between

```
c₁ E + c₂ F = E_u / 2
c₁ F + c₂ G = F_u - E_v / 2
```

is `2G ·` the first minus `2F ·` the second — the `c₂` terms cancel as `2c₂FG - 2c₂FG`, and
what is left is `2c₁(EG - F²)` against `G E_u - 2F F_u + F E_v`. Finding those multipliers
is exactly the pseudo-division `wu` performs; here they are supplied.

For a 2×2 linear system that is easy enough to do in one's head, which is the honest
assessment: on *this* problem the tactic saves little. Its value shows where the system is
larger or the elimination order is not obvious — and the Christoffel relations are only the
first step towards Gauss–Codazzi, where it will not be. What the tactic already gives here
is that the multipliers are found rather than guessed, and that it reported the correct
nondegeneracy condition, namely none.

## The regularity hypothesis, again

Written in cleared form these need no `EG - F² ≠ 0`, and the hand proofs confirm it — a
`linear_combination` certificate divides by nothing. `WuDifferential/Curvature.lean` carries
`2W ≠ 0` through all six of its theorems and did not have to.
-/

open scoped RealInnerProductSpace ContDiff

namespace WuSurface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {f : ℝ × ℝ → V} {p : ℝ × ℝ} {n : V} {c₁ c₂ l : ℝ}

/-- `2W Γ¹₁₁ = G E_u - 2F F_u + F E_v`, by hand. Compare `christoffel_111`. -/
theorem christoffel_111' (hf : ContDiff ℝ ∞ f) (hn1 : ⟪n, d1 f p⟫ = 0)
    (hn2 : ⟪n, d2 f p⟫ = 0)
    (hdec : d1 (d1 f) p = c₁ • d1 f p + c₂ • d2 f p + l • n) :
    2 * (E f p * G f p - F f p ^ 2) * c₁
      = G f p * d1 (E f) p - 2 * F f p * d1 (F f) p + F f p * d2 (E f) p := by
  have h₁ : c₁ * E f p + c₂ * F f p = d1 (E f) p / 2 := by
    rw [← inner_frame_d1 hn1 hdec, inner_d11_d1 hf]
  have h₂ : c₁ * F f p + c₂ * G f p = d1 (F f) p - d2 (E f) p / 2 := by
    rw [← inner_frame_d2 hn2 hdec, inner_d11_d2 hf]
  -- eliminate `c₂`: the `2c₂FG` terms cancel between the two
  linear_combination (2 * G f p) * h₁ - (2 * F f p) * h₂

/-- `2W Γ²₁₁ = 2E F_u - E E_v - F E_u`, by hand. Compare `christoffel_211`. -/
theorem christoffel_211' (hf : ContDiff ℝ ∞ f) (hn1 : ⟪n, d1 f p⟫ = 0)
    (hn2 : ⟪n, d2 f p⟫ = 0)
    (hdec : d1 (d1 f) p = c₁ • d1 f p + c₂ • d2 f p + l • n) :
    2 * (E f p * G f p - F f p ^ 2) * c₂
      = 2 * E f p * d1 (F f) p - E f p * d2 (E f) p - F f p * d1 (E f) p := by
  have h₁ : c₁ * E f p + c₂ * F f p = d1 (E f) p / 2 := by
    rw [← inner_frame_d1 hn1 hdec, inner_d11_d1 hf]
  have h₂ : c₁ * F f p + c₂ * G f p = d1 (F f) p - d2 (E f) p / 2 := by
    rw [← inner_frame_d2 hn2 hdec, inner_d11_d2 hf]
  -- eliminate `c₁` instead: the `2c₁EF` terms cancel
  linear_combination (-(2 * F f p)) * h₁ + (2 * E f p) * h₂

/-- `2W Γ¹₁₂ = G E_v - F G_u`, by hand. Compare `christoffel_112`. -/
theorem christoffel_112' (hf : ContDiff ℝ ∞ f) (hn1 : ⟪n, d1 f p⟫ = 0)
    (hn2 : ⟪n, d2 f p⟫ = 0)
    (hdec : d2 (d1 f) p = c₁ • d1 f p + c₂ • d2 f p + l • n) :
    2 * (E f p * G f p - F f p ^ 2) * c₁
      = G f p * d2 (E f) p - F f p * d1 (G f) p := by
  have h₁ : c₁ * E f p + c₂ * F f p = d2 (E f) p / 2 := by
    rw [← inner_frame_d1 hn1 hdec, inner_d21_d1 hf]
  have h₂ : c₁ * F f p + c₂ * G f p = d1 (G f) p / 2 := by
    rw [← inner_frame_d2 hn2 hdec, inner_d21_d2 hf]
  linear_combination (2 * G f p) * h₁ - (2 * F f p) * h₂

/-- `2W Γ²₁₂ = E G_u - F E_v`, by hand. Compare `christoffel_212`. -/
theorem christoffel_212' (hf : ContDiff ℝ ∞ f) (hn1 : ⟪n, d1 f p⟫ = 0)
    (hn2 : ⟪n, d2 f p⟫ = 0)
    (hdec : d2 (d1 f) p = c₁ • d1 f p + c₂ • d2 f p + l • n) :
    2 * (E f p * G f p - F f p ^ 2) * c₂
      = E f p * d1 (G f) p - F f p * d2 (E f) p := by
  have h₁ : c₁ * E f p + c₂ * F f p = d2 (E f) p / 2 := by
    rw [← inner_frame_d1 hn1 hdec, inner_d21_d1 hf]
  have h₂ : c₁ * F f p + c₂ * G f p = d1 (G f) p / 2 := by
    rw [← inner_frame_d2 hn2 hdec, inner_d21_d2 hf]
  linear_combination (-(2 * F f p)) * h₁ + (2 * E f p) * h₂

end WuSurface
