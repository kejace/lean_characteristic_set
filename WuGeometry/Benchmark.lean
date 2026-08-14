/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuGeometry.Bench

/-!
# `wu` benchmark

Each entry is a real theorem elaborated through `#wu_bench`, which times it and logs the
result. Because `#wu_bench` elaborates the actual declaration, a broken entry breaks the
build: no row can be silently skipped or quietly weakened.

Where `wu` needs a nondegeneracy condition it appears as an explicit `≠ 0` hypothesis, and
where the default first-appearance variable order is wrong the entry says so with
`(vars := ...)`. Both are part of the measurement: they record what the method actually
needed, not an idealised version of it.

Anything Wu's method could *not* do is recorded in the `Not proved` section at the end
rather than omitted.
-/

namespace WuGeometry

/-! ### Metric identities -/

-- `A.2 ≠ B.2` is inherent, not an artifact: the perpendicularity constraint pins one
-- coordinate of `C` only when the corresponding difference is nonzero.
#wu_bench theorem pythagoras (A B C : Pt) (hAB : A.2 ≠ B.2) (h : Perp A B A C) :
    (C.1 - B.1) ^ 2 + (C.2 - B.2) ^ 2
      - ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2)
      - ((C.1 - A.1) ^ 2 + (C.2 - A.2) ^ 2) = 0 := by wu

#wu_bench theorem parallelogram_law (A B C D : Pt) (h : Parallelogram A B C D) :
    (C.1 - A.1) ^ 2 + (C.2 - A.2) ^ 2 + ((D.1 - B.1) ^ 2 + (D.2 - B.2) ^ 2)
      - 2 * ((B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2)
      - 2 * ((D.1 - A.1) ^ 2 + (D.2 - A.2) ^ 2) = 0 := by wu

#wu_bench theorem rectangle_diagonals_equal (A B C D : Pt) (hAB : A.2 ≠ B.2)
    (hpar : Parallelogram A B C D) (hright : Perp A B A D) :
    EqDist A C B D := by wu

#wu_bench theorem median_to_hypotenuse (A B C M : Pt) (hCA : C.2 ≠ A.2)
    (hright : Perp C A C B) (hM : Midpoint M A B) :
    EqDist C M A M := by wu

#wu_bench theorem isosceles_median_perp (A B C M : Pt)
    (hiso : EqDist A B A C) (hM : Midpoint M B C) :
    Perp A M B C := by wu

/-! ### Circles -/

#wu_bench theorem chord_perp_bisector (O A B M : Pt)
    (hAB : OnCircle B O A) (hM : Midpoint M A B) :
    Perp O M A B := by wu

#wu_bench theorem thales_converse (A B O P : Pt) (hPA : P.2 ≠ A.2)
    (hO : Midpoint O A B) (hperp : Perp P A P B) :
    OnCircle P O A := by wu

#wu_bench theorem inscribed_diameter (A B O P : Pt)
    (hO : Midpoint O A B) (hP : OnCircle P O A) :
    Perp P A P B := by wu

/-! ### Centroid and medians -/

#wu_bench theorem centroid_divides_median (A B C G M : Pt)
    (hG₁ : 3 * G.1 - (A.1 + B.1 + C.1) = 0)
    (hG₂ : 3 * G.2 - (A.2 + B.2 + C.2) = 0)
    (hM : Midpoint M B C) :
    G.1 - A.1 - 2 * (M.1 - G.1) = 0 := by wu

#wu_bench theorem centroid_divides_median_y (A B C G M : Pt)
    (hG₁ : 3 * G.1 - (A.1 + B.1 + C.1) = 0)
    (hG₂ : 3 * G.2 - (A.2 + B.2 + C.2) = 0)
    (hM : Midpoint M B C) :
    G.2 - A.2 - 2 * (M.2 - G.2) = 0 := by wu

/-! ### Varignon, completed -/

#wu_bench theorem varignon_second (A B C D P Q R S : Pt)
    (hP : Midpoint P A B) (hQ : Midpoint Q B C)
    (hR : Midpoint R C D) (hS : Midpoint S D A) :
    (S.1 - P.1) * (R.2 - Q.2) - (R.1 - Q.1) * (S.2 - P.2) = 0 := by wu

#wu_bench theorem varignon_diagonals (A B C D P Q R S M N : Pt)
    (hP : Midpoint P A B) (hQ : Midpoint Q B C)
    (hR : Midpoint R C D) (hS : Midpoint S D A)
    (hM : Midpoint M P R) (hN : Midpoint N Q S) :
    M.1 = N.1 := by wu

/-! ### Simson line

`P` on the circumcircle of `ABC`; the feet of the perpendiculars from `P` to the three
sides are collinear. The circumcentre `O` is introduced explicitly so that "on the
circumcircle" is a polynomial condition. This is by far the largest system here, so it
gets a coordinate frame (`A` at the origin, `B` on the x-axis), an explicit variable order
putting the constructed points last, and a raised heartbeat budget. -/

set_option maxHeartbeats 2000000 in
#wu_bench theorem simson (b c₁ c₂ o₁ o₂ p₁ p₂ x₁ x₂ y₁ y₂ z₁ z₂ : ℝ)
    (hb : b ≠ 0) (hc₁ : c₁ ≠ 0) (hcb : c₁ ≠ b) (hc₂ : c₂ ≠ 0)
    (hCA : c₂ ^ 2 + c₁ ^ 2 ≠ 0)
    (hCB : c₂ ^ 2 + c₁ ^ 2 - 2 * (b * c₁) + b ^ 2 ≠ 0)
    (hOB : OnCircle (b, (0 : ℝ)) (o₁, o₂) ((0 : ℝ), (0 : ℝ)))
    (hOC : OnCircle (c₁, c₂) (o₁, o₂) ((0 : ℝ), (0 : ℝ)))
    (hOP : OnCircle (p₁, p₂) (o₁, o₂) ((0 : ℝ), (0 : ℝ)))
    (hX : Foot (x₁, x₂) (p₁, p₂) (b, (0 : ℝ)) (c₁, c₂))
    (hY : Foot (y₁, y₂) (p₁, p₂) (c₁, c₂) ((0 : ℝ), (0 : ℝ)))
    (hZ : Foot (z₁, z₂) (p₁, p₂) ((0 : ℝ), (0 : ℝ)) (b, (0 : ℝ))) :
    Collinear₃ (x₁, x₂) (y₁, y₂) (z₁, z₂) := by
  wu (vars := [b, c₁, c₂, o₁, o₂, p₁, p₂, x₁, x₂, y₁, y₂, z₁, z₂])

/-! ### Algebraic residue of a PDE

The tanh method reduces a travelling-wave PDE to a purely *algebraic* system in the
ansatz coefficients, and that system is exactly `wu`'s shape. This is the residue for
Burgers' equation `u_t + u u_x - ν u_xx = 0`.

With `u = f(ξ)`, `ξ = x - c t`, integrating once gives `-c f + f²/2 - ν f' = A`.
Substituting `f = a₀ + a₁ w` with `w = tanh(k ξ)`, so `w' = k (1 - w²)`, and collecting
powers of `w` gives the three coefficient equations below (cleared of denominators).

`wu` then derives the standard travelling-wave relations. Note this proves a statement
about the *coefficient system*; it does not prove anything about Burgers' equation
itself, since deriving the system is the (differential) step `wu` cannot do. -/

#wu_bench theorem burgers_tanh_speed (a₀ a₁ c k ν A : ℝ) (ha₁ : a₁ ≠ 0)
    (e₀ : -2 * c * a₀ + a₀ ^ 2 - 2 * ν * a₁ * k - 2 * A = 0)
    (e₁ : -c * a₁ + a₀ * a₁ = 0)
    (e₂ : a₁ ^ 2 + 2 * ν * a₁ * k = 0) :
    a₀ = c := by wu (vars := [c, k, ν, A, a₁, a₀]) [e₁]

#wu_bench theorem burgers_tanh_amplitude (a₀ a₁ c k ν A : ℝ) (ha₁ : a₁ ≠ 0) (hk : k ≠ 0)
    (e₀ : -2 * c * a₀ + a₀ ^ 2 - 2 * ν * a₁ * k - 2 * A = 0)
    (e₁ : -c * a₁ + a₀ * a₁ = 0)
    (e₂ : a₁ ^ 2 + 2 * ν * a₁ * k = 0) :
    a₁ = -2 * ν * k := by wu (vars := [c, k, a₀, A, a₁, ν]) [e₂]

/-! ### Not proved, and why

Recorded rather than omitted.

**Ceva and Menelaus.** These are statements about *ratios* along the sides. Turning them
into polynomial form needs the cevian feet parameterised by explicit ratio variables
(`P = A + t(B - A)` and so on), which changes what is being stated rather than just how.
Left out until that parameterisation is done properly.

**`a₁ = -2νk` under the default order.** With `a₁` as the main variable, the hypothesis
`a₁² + 2νa₁k = 0` has degree 2 in `a₁` while the goal `a₁ + 2νk` has degree 1, so
pseudo-division by it leaves the goal untouched and `wu` reports no certificate. The
mathematical content is that `a₁(a₁ + 2νk) = 0` needs *factoring*, which pseudo-reduction
does not do. Reordering so that `ν` is the main variable makes both sides degree 1 and the
reduction goes through — hence the `(vars := ...)` on `burgers_tanh_amplitude`. This is a
real limitation of the method, not of this implementation: Wu's method proves membership
in a saturated ideal, and `a₁ = 0` is a genuine component of the variety.

**Nine-point circle, Desargues, butterfly, Ptolemy, Napoleon.** Not attempted here. They
need more construction points, and on the evidence of Simson (66 ms with a hand-chosen
variable order, but a heartbeat timeout without one) they would each need their order
tuned individually rather than being dropped in.

-/

end WuGeometry
