/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuDifferential.SurfaceGauss

/-!
# The Gauss equation, by hand

`WuDifferential/SurfaceGaussWu.lean` proves this with one `wu` call. Here is the same
statement without the tactic, so the two can be compared. **No `CharSetTac` import.**

## What the by-hand version costs

The obstacle is that the Christoffel symbols are available only as `2W Γ = A`, and the
identity needs them *multiplied together*. There is no way to substitute `Γ = A/(2W)`
without leaving the polynomial world, so each product has to be built by hand:

```
4W² (Γᵢ Γⱼ) = (2W Γᵢ)(2W Γⱼ) = Aᵢ Aⱼ
```

That is one auxiliary step per product, and there are **seven** of them. Only then can the
whole thing be assembled, with the seven multipliers `-E, -F, -F, -G, +E, +2F, +G` read off
the frame expansion, plus `4W²` on the raw identity itself.

None of it is deep. All of it is bookkeeping, and it is bookkeeping where a dropped factor
of `2W` or a sign gives a wrong theorem rather than a failed proof — which is precisely the
kind of error the certificate architecture cannot produce, since `ring1` checks the whole
identity at once.

## The honest comparison

* `SurfaceChristoffel.lean` — 2×2 linear. The tactic saves nothing worth mentioning.
* This file — six variables, quadratic, cleared denominators. Seven hand-built products,
  and the multiplier `4W²` has to be known *in advance* to even state the goal correctly.

Wu's method finds the multiplier rather than being told it. On a problem where the exponent
is not guessable — deeper prolongations, or higher codimension where the second fundamental
form carries a normal index — that difference stops being a convenience.
-/

namespace WuSurface

/-- The Gauss equation, proved by explicitly building each Christoffel product.

Compare `WuSurface.gauss_equation`, which is the same statement by `wu`. -/
theorem gauss_equation'
    (E F G W Eu Ev Fu Fv Gu Gv g111 g211 g112 g212 g122 g222 L M N R : ℝ)
    (h111 : 2 * W * g111 = G * Eu - 2 * F * Fu + F * Ev)
    (h211 : 2 * W * g211 = 2 * E * Fu - E * Ev - F * Eu)
    (h112 : 2 * W * g112 = G * Ev - F * Gu)
    (h212 : 2 * W * g212 = E * Gu - F * Ev)
    (h122 : 2 * W * g122 = 2 * G * Fv - G * Gu - F * Gv)
    (h222 : 2 * W * g222 = E * Gv - 2 * F * Fv + F * Gu)
    (hraw : (g111 * (g122 * E + g222 * F) + g211 * (g122 * F + g222 * G) + L * N)
          - (g112 * (g112 * E + g212 * F) + g212 * (g112 * F + g212 * G) + M * M) = R) :
    4 * W ^ 2 * (L * N - M * M)
      = 4 * W ^ 2 * R
        - ((G * Eu - 2 * F * Fu + F * Ev) * (2 * G * Fv - G * Gu - F * Gv) * E
         + (G * Eu - 2 * F * Fu + F * Ev) * (E * Gv - 2 * F * Fv + F * Gu) * F
         + (2 * E * Fu - E * Ev - F * Eu) * (2 * G * Fv - G * Gu - F * Gv) * F
         + (2 * E * Fu - E * Ev - F * Eu) * (E * Gv - 2 * F * Fv + F * Gu) * G)
        + ((G * Ev - F * Gu) ^ 2 * E
         + 2 * (G * Ev - F * Gu) * (E * Gu - F * Ev) * F
         + (E * Gu - F * Ev) ^ 2 * G) := by
  -- Seven products, each `4W²ΓᵢΓⱼ = AᵢAⱼ`, built from the cleared relations pairwise.
  have m1 : 4 * W ^ 2 * (g111 * g122)
      = (G * Eu - 2 * F * Fu + F * Ev) * (2 * G * Fv - G * Gu - F * Gv) := by
    linear_combination congrArg₂ (· * ·) h111 h122
  have m2 : 4 * W ^ 2 * (g111 * g222)
      = (G * Eu - 2 * F * Fu + F * Ev) * (E * Gv - 2 * F * Fv + F * Gu) := by
    linear_combination congrArg₂ (· * ·) h111 h222
  have m3 : 4 * W ^ 2 * (g211 * g122)
      = (2 * E * Fu - E * Ev - F * Eu) * (2 * G * Fv - G * Gu - F * Gv) := by
    linear_combination congrArg₂ (· * ·) h211 h122
  have m4 : 4 * W ^ 2 * (g211 * g222)
      = (2 * E * Fu - E * Ev - F * Eu) * (E * Gv - 2 * F * Fv + F * Gu) := by
    linear_combination congrArg₂ (· * ·) h211 h222
  have m5 : 4 * W ^ 2 * (g112 * g112) = (G * Ev - F * Gu) ^ 2 := by
    linear_combination congrArg₂ (· * ·) h112 h112
  have m6 : 4 * W ^ 2 * (g112 * g212) = (G * Ev - F * Gu) * (E * Gu - F * Ev) := by
    linear_combination congrArg₂ (· * ·) h112 h212
  have m7 : 4 * W ^ 2 * (g212 * g212) = (E * Gu - F * Ev) ^ 2 := by
    linear_combination congrArg₂ (· * ·) h212 h212
  -- assemble: multipliers read off the frame expansion
  linear_combination 4 * W ^ 2 * hraw - E * m1 - F * m2 - F * m3 - G * m4
    + E * m5 + 2 * F * m6 + G * m7

end WuSurface
