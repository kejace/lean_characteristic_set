/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuDifferential.SurfaceGauss
import CharSetTac.Frontend

/-!
# Codazzi and Gauss, by elimination

`WuDifferential/SurfaceGauss.lean` produces the equations from `fderiv`; this file does the
algebra on them.

## Codazzi

Pairing `(f_uu)_v = (f_uv)_u` against `n` and expanding both second derivatives in the
frame. The elimination is light — the content is in the pairing, not the algebra.

## Gauss, and why *this* is where the tactic earns its place

The Gauss equation is a different kind of problem, and it is worth being precise about why,
because the Christoffel relations in `SurfaceChristoffel.lean` were *not*.

There, two linear equations in two unknowns: eliminate by Cramer, multipliers visible at a
glance. Here:

* six Christoffel symbols to eliminate, not one;
* each is only available in **cleared** form `2W Γ = (…)`, i.e. it is a rational quantity
  with denominator `2W`;
* and the frame expansion of `⟪f_uu, f_vv⟫ - ⟪f_uv, f_uv⟫` is **quadratic** in them.

The quadratic occurrence is the crux. A product `Γ·Γ` carries denominator `(2W)²`, so the
identity only becomes polynomial after multiplying by `(2W)²` — and *which* power is needed
is not known before doing the elimination. That is exactly the bookkeeping Wu's method does
for you: the multiplier is a product of initials with exponents the algorithm discovers.

So the answer to "what makes a bigger problem" is neither dimension nor differential order
by itself. Both merely make systems larger, and a larger *linear* system still eliminates
by Cramer. What changes the character is **nonlinearity in the eliminated variables**, and
in differential geometry that arrives the moment quantities carrying a common denominator
appear multiplied together. Gauss is the first place on this path where it does.
-/

open scoped RealInnerProductSpace ContDiff

namespace WuSurface

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {f n : ℝ × ℝ → V} {p : ℝ × ℝ} {a₁ a₂ b₁ b₂ : ℝ}

/-- **The Codazzi–Mainardi equation.**

`L_v - M_u = Γ¹₁₂ L + (Γ²₁₂ - Γ¹₁₁) M - Γ²₁₁ N`, where the `Γ` are the tangential
coefficients of the frame decompositions of `f_uu` and `f_uv`.

Everything on the right comes from the derived Weingarten pairings; nothing is assumed
beyond the frame decompositions themselves. -/
theorem codazzi (hf : ContDiff ℝ ∞ f) (hn : ContDiff ℝ ∞ n)
    (hn1 : ∀ q, ⟪n q, d1 f q⟫ = (0 : ℝ)) (hn2 : ∀ q, ⟪n q, d2 f q⟫ = (0 : ℝ))
    (hnn : ∀ q, ⟪n q, n q⟫ = (1 : ℝ))
    (hd11 : d1 (d1 f) p = a₁ • d1 f p + a₂ • d2 f p + L f n p • n p)
    (hd12 : d2 (d1 f) p = b₁ • d1 f p + b₂ • d2 f p + M f n p • n p) :
    d2 (L f n) p - d1 (M f n) p
      = b₁ * L f n p + (b₂ - a₁) * M f n p - a₂ * N f n p := by
  have hnd := hn.differentiable (by simp) p
  have h11 := (contDiff_d1 (contDiff_d1 hf)).differentiable (by simp) p
  have h21 := (contDiff_d2 (contDiff_d1 hf)).differentiable (by simp) p
  -- Leibniz on `L = ⟪f_uu, n⟫` and `M = ⟪f_uv, n⟫`
  have hL : d2 (L f n) p = ⟪d2 (d1 (d1 f)) p, n p⟫ + ⟪d1 (d1 f) p, d2 n p⟫ := by
    rw [show L f n = fun q => ⟪d1 (d1 f) q, n q⟫ from rfl, d2_inner h11 hnd]; ring
  have hM : d1 (M f n) p = ⟪d1 (d2 (d1 f)) p, n p⟫ + ⟪d2 (d1 f) p, d1 n p⟫ := by
    rw [show M f n = fun q => ⟪d2 (d1 f) q, n q⟫ from rfl, d1_inner h21 hnd]; ring
  -- the third-derivative terms agree, by Schwarz one level up
  have hswap : d2 (d1 (d1 f)) p = d1 (d2 (d1 f)) p := d_swap (contDiff_d1 hf) p
  -- expand the two remaining pairings in the frame; the derived Weingarten values enter here
  have e1 : ⟪d1 (d1 f) p, d2 n p⟫ = -(a₁ * M f n p) - a₂ * N f n p := by
    rw [inner_frame_gen hd11, real_inner_comm (d2 n p) (d1 f p),
      real_inner_comm (d2 n p) (d2 f p), real_inner_comm (d2 n p) (n p),
      inner_d2n_d1f hf hn hn1, inner_d2n_d2f hf hn hn2]
    rw [inner_d2n_n hn hnn]
    ring
  have e2 : ⟪d2 (d1 f) p, d1 n p⟫ = -(b₁ * L f n p) - b₂ * M f n p := by
    rw [inner_frame_gen hd12, real_inner_comm (d1 n p) (d1 f p),
      real_inner_comm (d1 n p) (d2 f p), real_inner_comm (d1 n p) (n p),
      inner_d1n_d1f hf hn hn1, inner_d1n_d2f hf hn hn2, inner_d1n_n hn hnn]
    ring
  rw [hL, hM, hswap, e1, e2]
  ring

/-! ### Gauss

Two frame expansions, then the elimination. -/

variable {c₁ c₂ : ℝ}

/-- `⟪f_uu, f_vv⟫` expanded in the frame. -/
theorem inner_d11_d22_frame (hn1 : ⟪n p, d1 f p⟫ = (0 : ℝ)) (hn2 : ⟪n p, d2 f p⟫ = (0 : ℝ))
    (hd11 : d1 (d1 f) p = a₁ • d1 f p + a₂ • d2 f p + L f n p • n p)
    (hd22 : d2 (d2 f) p = c₁ • d1 f p + c₂ • d2 f p + N f n p • n p) :
    ⟪d1 (d1 f) p, d2 (d2 f) p⟫
      = a₁ * (c₁ * E f p + c₂ * F f p) + a₂ * (c₁ * F f p + c₂ * G f p)
        + L f n p * N f n p := by
  rw [inner_frame_gen hd11, real_inner_comm (d2 (d2 f) p) (d1 f p),
    real_inner_comm (d2 (d2 f) p) (d2 f p), real_inner_comm (d2 (d2 f) p) (n p),
    inner_frame_d1 hn1 hd22, inner_frame_d2 hn2 hd22,
    show ⟪d2 (d2 f) p, n p⟫ = N f n p from rfl]

/-- `⟪f_uv, f_uv⟫` expanded in the frame. -/
theorem inner_d21_d21_frame (hn1 : ⟪n p, d1 f p⟫ = (0 : ℝ)) (hn2 : ⟪n p, d2 f p⟫ = (0 : ℝ))
    (hd12 : d2 (d1 f) p = b₁ • d1 f p + b₂ • d2 f p + M f n p • n p) :
    ⟪d2 (d1 f) p, d2 (d1 f) p⟫
      = b₁ * (b₁ * E f p + b₂ * F f p) + b₂ * (b₁ * F f p + b₂ * G f p)
        + M f n p * M f n p := by
  rw [inner_frame_gen hd12, real_inner_comm (d2 (d1 f) p) (d1 f p),
    real_inner_comm (d2 (d1 f) p) (d2 f p), real_inner_comm (d2 (d1 f) p) (n p),
    inner_frame_d1 hn1 hd12, inner_frame_d2 hn2 hd12,
    show ⟪d2 (d1 f) p, n p⟫ = M f n p from rfl]

/-- **The Gauss equation, in cleared form.**

`4W²(LN - M²)` equals the raw integrability right-hand side, corrected by the quadratic
Christoffel terms — each `Γ` replaced by its numerator `2WΓ`.

Every hypothesis here is a theorem elsewhere in this development: the `h…` are
`SurfaceChristoffel.lean`, and `hraw` is `gauss_raw` combined with the two frame expansions
above. Nothing is postulated.

**This is the elimination the tactic exists for.** Six variables go, they occur
*quadratically*, and they are only available in cleared form — so the identity is
polynomial only after multiplying by `(2W)²`, and that exponent is not known in advance.
The Christoffel relations of `SurfaceChristoffel.lean` were a 2×2 linear solve; this is
not. Compare `SurfaceGaussComparison.lean` for what supplying the certificate by hand
looks like. -/
theorem gauss_equation
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
  wu (vars := [E, F, G, W, Eu, Ev, Fu, Fv, Gu, Gv, L, M, N, R,
               g111, g211, g112, g212, g122, g222])

end WuSurface
