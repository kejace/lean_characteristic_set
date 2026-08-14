/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuGeometry.Basic

/-!
# Classical plane geometry theorems, proved by `wu`

Each theorem is stated with the predicates of `WuGeometry.Basic`, and proved by `wu`,
which unfolds them to polynomial equations and runs Wu's characteristic set method.

## Reading the statements

Points are free `Pt` variables, so these are theorems about *all* configurations
satisfying the hypotheses. Where Wu's method needs a nondegeneracy condition (a triangle
not collapsing, two lines not parallel), it appears as an explicit `≠ 0` hypothesis:
the tactic surfaces exactly which degeneracies it excluded, rather than assuming them
silently.

Coordinates are placed by choosing a convenient frame (e.g. `A` at the origin, `B` on the
x-axis) where doing so is without loss of generality. That is standard practice in
mechanical geometry theorem proving and keeps the polynomial systems small.
-/

namespace WuGeometry

/-! ### Parallelogram -/

/-- In a parallelogram `ABCD`, the diagonals bisect each other: the midpoint of `AC`
coincides with the midpoint of `BD`, coordinate by coordinate. -/
theorem parallelogram_diag_bisect (A B C D M N : Pt)
    (hpar : Parallelogram A B C D)
    (hM : Midpoint M A C) (hN : Midpoint N B D) :
    M.1 = N.1 := by wu

theorem parallelogram_diag_bisect_y (A B C D M N : Pt)
    (hpar : Parallelogram A B C D)
    (hM : Midpoint M A C) (hN : Midpoint N B D) :
    M.2 = N.2 := by wu

/-- Opposite sides of a parallelogram are parallel. -/
theorem parallelogram_para (A B C D : Pt) (h : Parallelogram A B C D) :
    (B.1 - A.1) * (C.2 - D.2) - (C.1 - D.1) * (B.2 - A.2) = 0 := by wu

/-! ### Midpoints -/

/-- The midline of a triangle is parallel to the third side: if `M` and `N` are the
midpoints of `AB` and `AC`, then `MN` is parallel to `BC`. -/
theorem midline_parallel (A B C M N : Pt)
    (hM : Midpoint M A B) (hN : Midpoint N A C) :
    (N.1 - M.1) * (C.2 - B.2) - (C.1 - B.1) * (N.2 - M.2) = 0 := by wu

/-- Varignon: the midpoints of the sides of any quadrilateral form a parallelogram.
Here the `PQ ∥ SR` half. -/
theorem varignon (A B C D P Q R S : Pt)
    (hP : Midpoint P A B) (hQ : Midpoint Q B C)
    (hR : Midpoint R C D) (hS : Midpoint S D A) :
    (Q.1 - P.1) * (R.2 - S.2) - (R.1 - S.1) * (Q.2 - P.2) = 0 := by wu

/-! ### Perpendicularity and the orthocentre -/

/-- The diagonals of a rhombus are perpendicular. -/
theorem rhombus_diag_perp (A B C D : Pt)
    (hpar : Parallelogram A B C D)
    (hside : EqDist A B A D) :
    Perp A C B D := by wu

/-- The three altitudes of a triangle are concurrent.

`A` is at the origin and `B` on the x-axis, without loss of generality. `H` is on the
altitude from `A` and on the altitude from `B`; the conclusion is that `CH` is then
perpendicular to `AB`. -/
theorem orthocentre (b c₁ c₂ h₁ h₂ : ℝ)
    (hb : b ≠ 0) (hc : c₂ ≠ 0)
    (hA : Perp ((0 : ℝ), (0 : ℝ)) (h₁, h₂) (b, (0 : ℝ)) (c₁, c₂))
    (hB : Perp (b, (0 : ℝ)) (h₁, h₂) ((0 : ℝ), (0 : ℝ)) (c₁, c₂)) :
    Perp (c₁, c₂) (h₁, h₂) ((0 : ℝ), (0 : ℝ)) (b, (0 : ℝ)) := by
  wu (vars := [b, c₁, c₂, h₁, h₂])

/-! ### Circles -/

/-- A point on the perpendicular bisector of `AB` is equidistant from `A` and `B`. -/
theorem perp_bisector (A B M P : Pt)
    (hAB : B.2 - A.2 ≠ 0)
    (hM : Midpoint M A B)
    (hperp : Perp P M A B) :
    EqDist P A P B := by
  wu (vars := [A.1, A.2, B.1, B.2, P.1, M.1, M.2, P.2])

/-- Thales: an angle inscribed in a semicircle is a right angle.

`O` is the centre, `A` and `B` are diametrically opposite (`O` is their midpoint), and `P`
is on the circle. Then `PA ⟂ PB`. -/
theorem thales (A B O P : Pt)
    (hO : Midpoint O A B)
    (hP : OnCircle P O A) :
    Perp P A P B := by wu

/-! ### Concurrency and collinearity -/

/-- The medians of a triangle meet: the centroid lies on all three.

With `G` the centroid, stated as the point with `3G = A + B + C`, `G` is collinear with
`A` and the midpoint of `BC`. -/
theorem centroid_on_median (A B C G M : Pt)
    (hG₁ : 3 * G.1 - (A.1 + B.1 + C.1) = 0)
    (hG₂ : 3 * G.2 - (A.2 + B.2 + C.2) = 0)
    (hM : Midpoint M B C) :
    Collinear₃ A M G := by wu

/-- Pappus' hexagon theorem, affine form.

`A₁ A₂ A₃` lie on one line and `B₁ B₂ B₃` on another; the three intersection points of
opposite sides are collinear. Coordinates are chosen so the two lines are the coordinate
axes, which is without loss of generality for the affine statement. -/
theorem pappus (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) (P Q R : Pt)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (h₁₂ : a₂ * b₂ - a₁ * b₁ ≠ 0) (h₁₃ : a₃ * b₃ - a₁ * b₁ ≠ 0)
    (h₂₃ : a₃ * b₃ - a₂ * b₂ ≠ 0)
    (hP : Inter P (a₁, (0 : ℝ)) ((0 : ℝ), b₂) (a₂, (0 : ℝ)) ((0 : ℝ), b₁))
    (hQ : Inter Q (a₁, (0 : ℝ)) ((0 : ℝ), b₃) (a₃, (0 : ℝ)) ((0 : ℝ), b₁))
    (hR : Inter R (a₂, (0 : ℝ)) ((0 : ℝ), b₃) (a₃, (0 : ℝ)) ((0 : ℝ), b₂)) :
    Collinear₃ P Q R := by
  wu (vars := [a₁, a₂, a₃, b₁, b₂, b₃, P.1, P.2, Q.1, Q.2, R.1, R.2])

end WuGeometry
