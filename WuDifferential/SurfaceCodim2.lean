/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Frontend
import Mathlib.Data.Real.Basic

/-!
# Codimension two: the normal connection, and where the tactic actually helps

A surface in `ℝ⁴` has a **two-dimensional normal bundle**, and that changes the picture in
a way worth being precise about — more precise than "higher codimension is harder".

## What does *not* get harder: Gauss

The Christoffel symbols depend only on the induced metric `E, F, G`. They do not know the
codimension. So the elimination in `WuDifferential/SurfaceGaussWu.lean` is *literally
unchanged* in codimension two; the only difference is that `LN - M²` becomes a sum
`∑_α (L^α N^α - (M^α)²)` over the normal directions. That is a longer expression, not a
harder elimination — more terms through the same machinery.

## What is genuinely new: the Ricci equation

With two normals there is a **normal connection**: `n₁` and `n₂` can rotate into one
another along the surface, and its curvature `R^⊥` is a third integrability condition with
no codimension-one analogue at all. It is governed by the commutator of the two shape
operators,

```
R^⊥ ~ [A₁, A₂],     A_α = g⁻¹ II_α
```

and *this* is where the elimination changes character. Each `A_α` is `g⁻¹ II_α`, so its
entries carry a denominator `W = EG - F²`; the commutator multiplies two of them, so the
identity is polynomial only after clearing `W²`.

That is the same mechanism as the Gauss equation — quantities with a common denominator
appearing quadratically — but arising from a genuinely different equation, and here `wu`
reports `W ≠ 0` as a real condition rather than none.

## The payoff

The whole normal curvature collapses to a single `3 × 3` determinant:

```
W² [A₁, A₂] = det ⎛ E   F   G  ⎞ · ⎛  F   G ⎞
                  ⎜ L₁  M₁  N₁ ⎟   ⎝ -E  -F ⎠
                  ⎝ L₂  M₂  N₂ ⎠
```

so **the normal bundle is flat exactly when that determinant vanishes** — the matrix on the
right has determinant `EG - F² = W ≠ 0`, so it never degenerates. Equivalently: the two
second fundamental forms are simultaneously diagonalisable with respect to the metric.

`normal_curvature` below is the `(1,2)` entry of that identity, proved by `wu`;
`normal_curvature'` is the same by hand.
-/

namespace WuCodim2

/-- **The normal curvature of a surface in `ℝ⁴`, by `wu`.**

`a` and `b` are the shape operators `g⁻¹ II₁` and `g⁻¹ II₂`, available only in cleared form
`W · aᵢⱼ = (adj g · II₁)ᵢⱼ`. The `(1,2)` entry of `[A₁, A₂]`, cleared by `W²`, is `G` times
the `3 × 3` determinant.

The multiplier `W²` is **found by the tactic**, not supplied: it is squared precisely
because the commutator is quadratic in `W`-denominated quantities. Contrast
`WuSurface.christoffel_111`, where the certificate needed no multiplier at all.

The full shape operators are given, but `ha21`/`hb21` go unused — the `(1,2)` entry of the
commutator does not see the second row. That is the tactic reporting what the result
actually depends on, the same way it reported that the Christoffel relations need no
regularity. -/
theorem normal_curvature (E F G W L1 M1 N1 L2 M2 N2 a11 a12 a21 a22 b11 b12 b21 b22 : ℝ)
    (hW0 : E * G - F ^ 2 ≠ 0) (hW : E * G - F ^ 2 = W)
    (ha11 : W * a11 = G * L1 - F * M1) (ha12 : W * a12 = G * M1 - F * N1)
    (ha21 : W * a21 = -(F * L1) + E * M1) (ha22 : W * a22 = -(F * M1) + E * N1)
    (hb11 : W * b11 = G * L2 - F * M2) (hb12 : W * b12 = G * M2 - F * N2)
    (hb21 : W * b21 = -(F * L2) + E * M2) (hb22 : W * b22 = -(F * M2) + E * N2) :
    W ^ 2 * (a11 * b12 + a12 * b22 - (b11 * a12 + b12 * a22))
      = G * (E * M1 * N2 - E * M2 * N1 - F * L1 * N2 + F * L2 * N1
             + G * L1 * M2 - G * L2 * M1) := by
  wu (vars := [E, F, G, W, L1, M1, N1, L2, M2, N2,
               a11, a12, a21, a22, b11, b12, b21, b22])

/-- The same, by hand. Each product of shape-operator entries has to be built separately —
four of them here — because `a` is only available as `W · a = …` and the identity needs
`a · b`.

Same shape as `WuSurface.gauss_equation'`, and the same conclusion: not deep, but
bookkeeping in which a dropped `W` gives a wrong theorem rather than a failed proof. -/
theorem normal_curvature' (E F G W L1 M1 N1 L2 M2 N2 a11 a12 a21 a22 b11 b12 b21 b22 : ℝ)
    (ha11 : W * a11 = G * L1 - F * M1) (ha12 : W * a12 = G * M1 - F * N1)
    (ha22 : W * a22 = -(F * M1) + E * N1)
    (hb11 : W * b11 = G * L2 - F * M2) (hb12 : W * b12 = G * M2 - F * N2)
    (hb22 : W * b22 = -(F * M2) + E * N2) :
    W ^ 2 * (a11 * b12 + a12 * b22 - (b11 * a12 + b12 * a22))
      = G * (E * M1 * N2 - E * M2 * N1 - F * L1 * N2 + F * L2 * N1
             + G * L1 * M2 - G * L2 * M1) := by
  have m1 : W ^ 2 * (a11 * b12) = (G * L1 - F * M1) * (G * M2 - F * N2) := by
    linear_combination congrArg₂ (· * ·) ha11 hb12
  have m2 : W ^ 2 * (a12 * b22) = (G * M1 - F * N1) * (-(F * M2) + E * N2) := by
    linear_combination congrArg₂ (· * ·) ha12 hb22
  have m3 : W ^ 2 * (b11 * a12) = (G * L2 - F * M2) * (G * M1 - F * N1) := by
    linear_combination congrArg₂ (· * ·) hb11 ha12
  have m4 : W ^ 2 * (b12 * a22) = (G * M2 - F * N2) * (-(F * M1) + E * N1) := by
    linear_combination congrArg₂ (· * ·) hb12 ha22
  linear_combination m1 + m2 - m3 - m4

/-- **Flatness of the normal bundle.** The `(1,2)` entry of the commutator vanishes exactly
when the `3 × 3` determinant does, provided `G ≠ 0` and the metric is regular.

This is the codimension-two statement with no codimension-one counterpart: in codimension
one there is nothing for the normal to rotate into. -/
theorem flat_normal_bundle_iff
    (E F G W L1 M1 N1 L2 M2 N2 a11 a12 a21 a22 b11 b12 b21 b22 : ℝ)
    (hW0 : W ≠ 0) (hG : G ≠ 0)
    (ha11 : W * a11 = G * L1 - F * M1) (ha12 : W * a12 = G * M1 - F * N1)
    (ha22 : W * a22 = -(F * M1) + E * N1)
    (hb11 : W * b11 = G * L2 - F * M2) (hb12 : W * b12 = G * M2 - F * N2)
    (hb22 : W * b22 = -(F * M2) + E * N2) :
    a11 * b12 + a12 * b22 - (b11 * a12 + b12 * a22) = 0
      ↔ E * M1 * N2 - E * M2 * N1 - F * L1 * N2 + F * L2 * N1
          + G * L1 * M2 - G * L2 * M1 = 0 := by
  have key := normal_curvature' E F G W L1 M1 N1 L2 M2 N2 a11 a12 a21 a22 b11 b12 b21 b22
    ha11 ha12 ha22 hb11 hb12 hb22
  constructor
  · intro h
    rw [h, mul_zero] at key
    exact (mul_eq_zero.mp key.symm).resolve_left hG
  · intro h
    rw [h, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 hW0)

end WuCodim2
