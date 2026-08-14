/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuGeometry.Basic

/-!
# The same geometry theorems without `wu`

Every theorem of `WuGeometry/Theorems.lean`, proved without the tactic, so the two can be
read side by side. Each proof is exactly the script `wu?` prints — unfold the predicates,
state the certificate, cancel the multiplier, discharge its nonvanishing — which is what
you would have had to write.

## What the comparison shows

For most of these `wu` saves little. Once the predicates are unfolded the identities are
linear or nearly so and the coefficients are tiny: `parallelogram_diag_bisect` needs three
terms with coefficients ±1. If these were the whole benchmark, the tactic would be a
convenience rather than a capability.

**Pappus is the exception, and it is the whole argument.** Its certificate is 3367
characters — over a hundred terms of degree 8 in six parameters. `wu` finds it in under
100 ms. Nobody finds that by inspection, and that is what "the tactic finds the
combination" buys.

The other thing on display is the *cost* of the method. Every proof ends by cancelling a
multiplier and discharging its nonvanishing. For `parallelogram_para` that multiplier is
`1` and the step is vacuous; for `orthocentre` it is `b·c₂`; for Pappus a product of six
factors. Those are the conditions **Wu's method** needs, not the ones the theorem needs —
`orthocentre` proved by direct substitution (`linear_combination hB - hA`) needs none of
them.
-/

namespace WuGeometry.ByHand
open WuGeometry

/-- Compare: `WuGeometry.parallelogram_diag_bisect`. Certificate: 29 characters. -/
theorem parallelogram_diag_bisect (A B C D M N : Pt)
    (hpar : Parallelogram A B C D)
    (hM : Midpoint M A C) (hN : Midpoint N B D) :
    M.1 = N.1 := by
  simp only [wu_unfold] at *
  obtain ⟨hp1, hp2⟩ := hpar; obtain ⟨hm1, hm2⟩ := hM; obtain ⟨hn1, hn2⟩ := hN
  have wu_key : 2 * (M.1 - N.1) = 0 := by
    linear_combination
      -1 * hp1 + 1 * hm1 + -1 * hn1
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

/-- Compare: `WuGeometry.parallelogram_diag_bisect_y`. Certificate: 29 characters. -/
theorem parallelogram_diag_bisect_y (A B C D M N : Pt)
    (hpar : Parallelogram A B C D)
    (hM : Midpoint M A C) (hN : Midpoint N B D) :
    M.2 = N.2 := by
  simp only [wu_unfold] at *
  obtain ⟨hp1, hp2⟩ := hpar; obtain ⟨hm1, hm2⟩ := hM; obtain ⟨hn1, hn2⟩ := hN
  have wu_key : 2 * (M.2 - N.2) = 0 := by
    linear_combination
      -1 * hp2 + 1 * hm2 + -1 * hn2
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

/-- Compare: `WuGeometry.parallelogram_para`. Certificate: 37 characters. -/
theorem parallelogram_para (A B C D : Pt) (h : Parallelogram A B C D) :
    (B.1 - A.1) * (C.2 - D.2) - (C.1 - D.1) * (B.2 - A.2) = 0 := by
  simp only [wu_unfold] at *
  obtain ⟨h1, h2⟩ := h
  have wu_key : 1 * ((B.1 - A.1) * (C.2 - D.2) - (C.1 - D.1) * (B.2 - A.2) - 0) = 0 := by
    linear_combination
      (-A.2 + B.2) * h1 + (A.1 + -B.1) * h2
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

/-- Compare: `WuGeometry.midline_parallel`. Certificate: 81 characters. -/
theorem midline_parallel (A B C M N : Pt)
    (hM : Midpoint M A B) (hN : Midpoint N A C) :
    (N.1 - M.1) * (C.2 - B.2) - (C.1 - B.1) * (N.2 - M.2) = 0 := by
  simp only [wu_unfold] at *
  obtain ⟨hm1, hm2⟩ := hM; obtain ⟨hn1, hn2⟩ := hN
  have wu_key : 1 * ((N.1 - M.1) * (C.2 - B.2) - (C.1 - B.1) * (N.2 - M.2) - 0) = 0 := by
    linear_combination
      (-N.2 + M.2) * hm1 + (N.1 + -M.1) * hm2 + (N.2 + -M.2) * hn1 + (-N.1 + M.1)
      * hn2
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

/-- Compare: `WuGeometry.varignon`. Certificate: 165 characters. -/
theorem varignon (A B C D P Q R S : Pt)
    (hP : Midpoint P A B) (hQ : Midpoint Q B C)
    (hR : Midpoint R C D) (hS : Midpoint S D A) :
    (Q.1 - P.1) * (R.2 - S.2) - (R.1 - S.1) * (Q.2 - P.2) = 0 := by
  simp only [wu_unfold] at *
  obtain ⟨hp1, hp2⟩ := hP; obtain ⟨hq1, hq2⟩ := hQ
  obtain ⟨hr1, hr2⟩ := hR; obtain ⟨hs1, hs2⟩ := hS
  have wu_key : 2 * ((Q.1 - P.1) * (R.2 - S.2) - (R.1 - S.1) * (Q.2 - P.2) - 0) = 0 := by
    linear_combination
      (-Q.2 + P.2) * hp1 + (Q.1 + -P.1) * hp2 + (Q.2 + -P.2) * hq1 + (-Q.1 + P.1)
      * hq2 + (-Q.2 + P.2) * hr1 + (Q.1 + -P.1) * hr2 + (Q.2 + -P.2) * hs1 + (-Q.1
      + P.1) * hs2
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

/-- Compare: `WuGeometry.rhombus_diag_perp`. Certificate: 52 characters. -/
theorem rhombus_diag_perp (A B C D : Pt)
    (hpar : Parallelogram A B C D)
    (hside : EqDist A B A D) :
    Perp A C B D := by
  simp only [wu_unfold] at *
  obtain ⟨hp1, hp2⟩ := hpar
  have wu_key : 1 * ((C.1 - A.1) * (D.1 - B.1) + (C.2 - A.2) * (D.2 - B.2) - 0) = 0 := by
    linear_combination
      (-D.1 + B.1) * hp1 + (-D.2 + B.2) * hp2 + -1 * hside
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

/-- Compare: `WuGeometry.orthocentre`. Certificate: 28 characters. -/
theorem orthocentre (b c₁ c₂ h₁ h₂ : ℝ)
    (hb : b ≠ 0) (hc : c₂ ≠ 0)
    (hA : Perp ((0 : ℝ), (0 : ℝ)) (h₁, h₂) (b, (0 : ℝ)) (c₁, c₂))
    (hB : Perp (b, (0 : ℝ)) (h₁, h₂) ((0 : ℝ), (0 : ℝ)) (c₁, c₂)) :
    Perp (c₁, c₂) (h₁, h₂) ((0 : ℝ), (0 : ℝ)) (b, (0 : ℝ)) := by
  simp only [wu_unfold] at *
  have wu_key : 1 * (b * c₂) * ((h₁ - c₁) * (b - 0) + (h₂ - c₂) * (0 - 0) - 0) = 0 := by
    linear_combination
      -(b * c₂) * hA + b * c₂ * hB
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

/-- Compare: `WuGeometry.perp_bisector`. Certificate: 137 characters. -/
theorem perp_bisector (A B M P : Pt)
    (hAB : B.2 - A.2 ≠ 0)
    (hM : Midpoint M A B)
    (hperp : Perp P M A B) :
    EqDist P A P B := by
  simp only [wu_unfold] at *
  obtain ⟨hm1, hm2⟩ := hM
  have wu_key : 1 * (B.2 + -A.2) * ((A.1 - P.1) ^ 2 + (A.2 - P.2) ^ 2 - ((B.1 - P.1) ^ 2 + (B.2 -
      P.2) ^ 2) - 0) = 0 := by
    linear_combination
      (B.1 * B.2 + -(A.1 * B.2) + -(A.2 * B.1) + A.1 * A.2) * hm1 + (B.2 ^ 2 + -2
      * (A.2 * B.2) + A.2 ^ 2) * hm2 + (-2 * B.2 + 2 * A.2) * hperp
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

/-- Compare: `WuGeometry.thales`. Certificate: 48 characters. -/
theorem thales (A B O P : Pt)
    (hO : Midpoint O A B)
    (hP : OnCircle P O A) :
    Perp P A P B := by
  simp only [wu_unfold] at *
  obtain ⟨ho1, ho2⟩ := hO
  have wu_key : 1 * ((A.1 - P.1) * (B.1 - P.1) + (A.2 - P.2) * (B.2 - P.2) - 0) = 0 := by
    linear_combination
      (P.1 + -A.1) * ho1 + (P.2 + -A.2) * ho2 + 1 * hP
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

/-- Compare: `WuGeometry.centroid_on_median`. Certificate: 81 characters. -/
theorem centroid_on_median (A B C G M : Pt)
    (hG₁ : 3 * G.1 - (A.1 + B.1 + C.1) = 0)
    (hG₂ : 3 * G.2 - (A.2 + B.2 + C.2) = 0)
    (hM : Midpoint M B C) :
    Collinear₃ A M G := by
  simp only [wu_unfold] at *
  obtain ⟨hm1, hm2⟩ := hM
  have wu_key : 2 * ((M.1 - A.1) * (G.2 - A.2) - (G.1 - A.1) * (M.2 - A.2) - 0) = 0 := by
    linear_combination
      (A.2 + -G.2) * hG₁ + (-A.1 + G.1) * hG₂ + (-A.2 + G.2) * hm1 + (A.1 + -G.1)
      * hm2
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

/-- Compare: `WuGeometry.pappus`. Certificate: 3367 characters. -/
theorem pappus (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) (P Q R : Pt)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (h₁₂ : a₂ * b₂ - a₁ * b₁ ≠ 0) (h₁₃ : a₃ * b₃ - a₁ * b₁ ≠ 0)
    (h₂₃ : a₃ * b₃ - a₂ * b₂ ≠ 0)
    (hP : Inter P (a₁, (0 : ℝ)) ((0 : ℝ), b₂) (a₂, (0 : ℝ)) ((0 : ℝ), b₁))
    (hQ : Inter Q (a₁, (0 : ℝ)) ((0 : ℝ), b₃) (a₃, (0 : ℝ)) ((0 : ℝ), b₁))
    (hR : Inter R (a₂, (0 : ℝ)) ((0 : ℝ), b₃) (a₃, (0 : ℝ)) ((0 : ℝ), b₂)) :
    Collinear₃ P Q R := by
  simp only [wu_unfold] at *
  obtain ⟨hpa, hpb⟩ := hP; obtain ⟨hqa, hqb⟩ := hQ; obtain ⟨hra, hrb⟩ := hR
  have wu_key : 1 * a₂ * (a₃ * b₃ + -(a₂ * b₂)) * a₃ * (a₃ * b₃ + -(a₁ * b₁)) * a₁ * (a₂ * b₂ +
      -(a₁ * b₁)) * ((Q.1 - P.1) * (R.2 - P.2) - (R.1 - P.1) * (Q.2 - P.2) - 0) =
      0 := by
    linear_combination
      (a₁ * a₂ ^ 2 * a₃ ^ 3 * b₂ * b₃ ^ 2 + -(a₁ * a₂ ^ 3 * a₃ ^ 2 * b₂ * b₃ ^ 2)
      + -(a₁ ^ 2 * a₂ * a₃ ^ 3 * b₁ * b₃ ^ 2) + a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2 * b₁ * b₃
      ^ 2 + -(a₁ * a₂ ^ 2 * a₃ ^ 3 * b₁ * b₂ * b₃) + a₁ * a₂ ^ 3 * a₃ ^ 2 * b₁ *
      b₂ * b₃ + a₁ ^ 2 * a₂ * a₃ ^ 3 * b₁ ^ 2 * b₃ + -(a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2 *
      b₁ ^ 2 * b₃)) * hpa + (-(a₁ * a₂ ^ 2 * a₃ ^ 3 * b₂ * b₃ ^ 2) + a₁ ^ 2 * a₂ ^
      2 * a₃ ^ 2 * b₂ * b₃ ^ 2 + a₁ ^ 2 * a₂ * a₃ ^ 3 * b₁ * b₃ ^ 2 + -(a₁ ^ 3 *
      a₂ * a₃ ^ 2 * b₁ * b₃ ^ 2) + a₁ * a₂ ^ 2 * a₃ ^ 3 * b₂ ^ 2 * b₃ + -(a₁ ^ 2 *
      a₂ ^ 2 * a₃ ^ 2 * b₂ ^ 2 * b₃) + -(a₁ ^ 2 * a₂ * a₃ ^ 3 * b₁ * b₂ * b₃) + a₁
      ^ 3 * a₂ * a₃ ^ 2 * b₁ * b₂ * b₃) * hpb + (a₁ * a₂ ^ 2 * a₃ ^ 3 * b₂ * b₃ *
      P.2 + -(a₁ ^ 2 * a₂ * a₃ ^ 3 * b₁ * b₃ * P.2) + -(a₁ * a₂ ^ 3 * a₃ ^ 2 * b₂
      ^ 2 * P.2) + a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2 * b₁ * b₂ * P.2 + a₁ * a₂ ^ 2 * a₃ ^ 2
      * b₁ * b₂ * b₃ * P.1 + -(a₁ ^ 2 * a₂ * a₃ ^ 2 * b₁ ^ 2 * b₃ * P.1) + -(a₁ *
      a₂ ^ 3 * a₃ * b₁ * b₂ ^ 2 * P.1) + a₁ ^ 2 * a₂ ^ 2 * a₃ * b₁ ^ 2 * b₂ * P.1
      + -(a₁ * a₂ ^ 2 * a₃ ^ 3 * b₂ ^ 2 * b₃) + a₁ * a₂ ^ 3 * a₃ ^ 2 * b₂ ^ 2 * b₃
      + a₁ ^ 2 * a₂ * a₃ ^ 3 * b₁ * b₂ * b₃ + -(a₁ * a₂ ^ 3 * a₃ ^ 2 * b₁ * b₂ *
      b₃) + -(a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2 * b₁ * b₂ * b₃) + a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2
      * b₁ ^ 2 * b₃ + a₁ * a₂ ^ 3 * a₃ ^ 2 * b₁ * b₂ ^ 2 + -(a₁ ^ 2 * a₂ ^ 2 * a₃
      ^ 2 * b₁ ^ 2 * b₂)) * hqa + (-(a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2 * b₂ * b₃ * P.2) +
      a₁ ^ 3 * a₂ * a₃ ^ 2 * b₁ * b₃ * P.2 + a₁ ^ 2 * a₂ ^ 3 * a₃ * b₂ ^ 2 * P.2 +
      -(a₁ ^ 3 * a₂ ^ 2 * a₃ * b₁ * b₂ * P.2) + -(a₁ * a₂ ^ 2 * a₃ ^ 2 * b₂ * b₃ ^
      2 * P.1) + a₁ ^ 2 * a₂ * a₃ ^ 2 * b₁ * b₃ ^ 2 * P.1 + a₁ * a₂ ^ 3 * a₃ * b₂
      ^ 2 * b₃ * P.1 + -(a₁ ^ 2 * a₂ ^ 2 * a₃ * b₁ * b₂ * b₃ * P.1) + a₁ * a₂ ^ 3
      * a₃ ^ 2 * b₂ * b₃ ^ 2 + -(a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2 * b₁ * b₃ ^ 2) + -(a₁ *
      a₂ ^ 3 * a₃ ^ 2 * b₂ ^ 2 * b₃) + a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2 * b₂ ^ 2 * b₃ +
      -(a₁ ^ 2 * a₂ ^ 3 * a₃ * b₂ ^ 2 * b₃) + a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2 * b₁ * b₂ *
      b₃ + -(a₁ ^ 3 * a₂ * a₃ ^ 2 * b₁ * b₂ * b₃) + a₁ ^ 3 * a₂ ^ 2 * a₃ * b₁ * b₂
      * b₃) * hqb + (a₁ * a₂ ^ 2 * a₃ ^ 3 * b₂ * b₃ * Q.2 + -(a₁ ^ 2 * a₂ * a₃ ^ 3
      * b₁ * b₃ * Q.2) + -(a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2 * b₁ * b₂ * Q.2) + a₁ ^ 3 * a₂
      * a₃ ^ 2 * b₁ ^ 2 * Q.2 + a₁ * a₂ ^ 2 * a₃ ^ 2 * b₂ ^ 2 * b₃ * Q.1 + -(a₁ ^
      2 * a₂ * a₃ ^ 2 * b₁ * b₂ * b₃ * Q.1) + -(a₁ ^ 2 * a₂ ^ 2 * a₃ * b₁ * b₂ ^ 2
      * Q.1) + a₁ ^ 3 * a₂ * a₃ * b₁ ^ 2 * b₂ * Q.1 + -(a₁ * a₂ ^ 2 * a₃ ^ 3 * b₂
      * b₃ * P.2) + a₁ ^ 2 * a₂ * a₃ ^ 3 * b₁ * b₃ * P.2 + a₁ ^ 2 * a₂ ^ 2 * a₃ ^
      2 * b₁ * b₂ * P.2 + -(a₁ ^ 3 * a₂ * a₃ ^ 2 * b₁ ^ 2 * P.2) + -(a₁ * a₂ ^ 2 *
      a₃ ^ 2 * b₂ ^ 2 * b₃ * P.1) + a₁ ^ 2 * a₂ * a₃ ^ 2 * b₁ * b₂ * b₃ * P.1 + a₁
      ^ 2 * a₂ ^ 2 * a₃ * b₁ * b₂ ^ 2 * P.1 + -(a₁ ^ 3 * a₂ * a₃ * b₁ ^ 2 * b₂ *
      P.1)) * hra + (-(a₁ * a₂ ^ 3 * a₃ ^ 2 * b₂ * b₃ * Q.2) + a₁ ^ 2 * a₂ ^ 2 *
      a₃ ^ 2 * b₁ * b₃ * Q.2 + a₁ ^ 2 * a₂ ^ 3 * a₃ * b₁ * b₂ * Q.2 + -(a₁ ^ 3 *
      a₂ ^ 2 * a₃ * b₁ ^ 2 * Q.2) + -(a₁ * a₂ ^ 2 * a₃ ^ 2 * b₂ * b₃ ^ 2 * Q.1) +
      a₁ ^ 2 * a₂ * a₃ ^ 2 * b₁ * b₃ ^ 2 * Q.1 + a₁ ^ 2 * a₂ ^ 2 * a₃ * b₁ * b₂ *
      b₃ * Q.1 + -(a₁ ^ 3 * a₂ * a₃ * b₁ ^ 2 * b₃ * Q.1) + a₁ * a₂ ^ 3 * a₃ ^ 2 *
      b₂ * b₃ * P.2 + -(a₁ ^ 2 * a₂ ^ 2 * a₃ ^ 2 * b₁ * b₃ * P.2) + -(a₁ ^ 2 * a₂
      ^ 3 * a₃ * b₁ * b₂ * P.2) + a₁ ^ 3 * a₂ ^ 2 * a₃ * b₁ ^ 2 * P.2 + a₁ * a₂ ^
      2 * a₃ ^ 2 * b₂ * b₃ ^ 2 * P.1 + -(a₁ ^ 2 * a₂ * a₃ ^ 2 * b₁ * b₃ ^ 2 * P.1)
      + -(a₁ ^ 2 * a₂ ^ 2 * a₃ * b₁ * b₂ * b₃ * P.1) + a₁ ^ 3 * a₂ * a₃ * b₁ ^ 2 *
      b₃ * P.1) * hrb
  refine Iff.mp sub_eq_zero (Iff.mp (mul_eq_zero_iff_left ?_) wu_key)
  repeat' first | apply mul_ne_zero | apply pow_ne_zero
  all_goals first | assumption | (apply sub_ne_zero.mpr; assumption) | norm_num

end WuGeometry.ByHand
