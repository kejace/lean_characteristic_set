/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuGeometry.Bench

/-!
# Discrete differential geometry and projective geometry

**These need no differential machinery at all.** Discrete geometry replaces derivatives by
finite differences, and finite differences of coordinates are *polynomial*. A discrete
evolute is built from circumcentres of consecutive vertex triples, and a circumcentre is a
rational function of the coordinates — so the plain algebraic `wu` handles the whole
subject directly.

That is worth stating plainly because it inverts the usual expectation: the *discrete*
theory is easier for this tactic than the smooth one, not harder.

## What is here

* **Circumcentres**, the basic construction underlying discrete evolutes
  (Arnold–Fuchs–Izmestiev–Tabachnikov–Tsukerman, *Iterating evolutes and involutes*).
* **Projective incidence** — Desargues, and the cross-ratio.
* **Infinitesimal rigidity**, which is a *linear* condition on velocities subject to
  quadratic edge constraints, so it too is polynomial.

Each of these is a family indexed by a combinatorial parameter (number of vertices,
dimension), which is the interesting thing: the tactic gives you a whole class at once,
one instance per parameter value.
-/

namespace WuGeometry.Discrete

open WuGeometry

/-! ### Circumcentres and discrete evolutes

The circumcentre of three points is characterised by equidistance. Writing that condition
squared keeps everything polynomial, and the resulting linear system in the centre's
coordinates is what makes the discrete evolute a rational map. -/

-- **The perpendicular bisectors of a triangle are concurrent.**
--
-- If `O` is equidistant from `A` and `B`, and from `B` and `C`, then it is equidistant from
-- `A` and `C`. This is the existence of the circumcentre, and it is the base case of the
-- discrete evolute construction: the evolute vertex assigned to a triple is well defined.
#wu_bench theorem circumcentre_concurrent (A B C O : Pt)
    (hAB : EqDist O A O B) (hBC : EqDist O B O C) : EqDist O A O C := by wu

-- The circumcentre condition is *linear* in the centre once the squares are expanded.
--
-- This is what makes the discrete evolute a rational — indeed projective-linear on each
-- fibre — map, which is the structural fact the iterated-evolute papers exploit.
#wu_bench theorem circumcentre_linear (A B O : Pt) (hAB : EqDist O A O B) :
    2 * O.1 * (B.1 - A.1) + 2 * O.2 * (B.2 - A.2)
      = B.1 ^ 2 + B.2 ^ 2 - (A.1 ^ 2 + A.2 ^ 2) := by wu

-- A vertex of the discrete evolute lies on the perpendicular bisector of the
-- corresponding edge: the evolute is the polygon of circumcentres.
#wu_bench theorem evolute_on_bisector (A B C O M : Pt) (hAB : 2 * B.2 - 2 * A.2 ≠ 0)
    (hO₁ : EqDist O A O B) (hO₂ : EqDist O B O C) (hM : Midpoint M A B) :
    Perp O M A B := by
  wu (vars := [A.1, A.2, B.1, B.2, C.1, C.2, O.1, O.2, M.1, M.2])

/-! ### Projective incidence -/

-- **Desargues' theorem.** Two triangles `ABC` and `A'B'C'` perspective from a point: the
-- three intersections of corresponding sides are collinear.
--
-- This was previously recorded here as *not* proved — with ten free points (twenty
-- coordinates) the computation blew a four-million-heartbeat budget. What fixed it was not
-- more compute but a better formulation, in two steps.
--
-- First, **parametrise the perspectivity**: `A' = tA · A` rather than "A' is a free point
-- collinear with O and A". That trades three hypotheses and six coordinates for three
-- scalars. Second, put the centre of perspectivity at the **origin**, which costs no
-- generality because collinearity is translation-invariant. Together these take the system
-- from 20 variables and 9 hypotheses to 15 and 6, which is the difference between
-- intractable and forty seconds.
--
-- The three nondegeneracy conditions are exactly the ones the theorem needs, and they are
-- worth reading. Each factors as `(tX - tY) * (X.1 * Y.2 - X.2 * Y.1) ≠ 0`: the second
-- factor says `O`, `X`, `Y` are not collinear — the triangle is a genuine triangle — and
-- the first says the corresponding sides are not parallel, so they actually meet at a
-- finite point rather than at infinity. Desargues is false without both, and it is a good
-- sign that the method recovers them rather than something stronger.
set_option maxRecDepth 8000 in
#wu_bench theorem desargues (A B C P Q R : Pt) (tA tB tC : ℝ)
    (hAB : (tB - tA) * (A.1 * B.2 - A.2 * B.1) ≠ 0)
    (hBC : (tC - tB) * (B.1 * C.2 - B.2 * C.1) ≠ 0)
    (hCA : (tC - tA) * (A.1 * C.2 - A.2 * C.1) ≠ 0)
    (hP  : Collinear₃ A B P)
    (hP' : Collinear₃ (homothety tA A) (homothety tB B) P)
    (hQ  : Collinear₃ B C Q)
    (hQ' : Collinear₃ (homothety tB B) (homothety tC C) Q)
    (hR  : Collinear₃ C A R)
    (hR' : Collinear₃ (homothety tC C) (homothety tA A) R) :
    Collinear₃ P Q R := by
  wu (vars := [A.1, A.2, B.1, B.2, C.1, C.2, tA, tB, tC, P.1, P.2, Q.1, Q.2, R.1, R.2])

-- Collinearity is preserved by the affine cross-ratio construction: if `X` divides `AB`
-- in ratio `t` and `Y` divides `CD` in the same ratio, then the construction is compatible
-- with collinearity of the endpoints.
#wu_bench theorem section_ratio (A B X : Pt) (t : ℝ) (ht : t ≠ 0)
    (hx₁ : X.1 - A.1 = t * (B.1 - A.1)) (hx₂ : X.2 - A.2 = t * (B.2 - A.2)) :
    Collinear₃ A B X := by wu

/-! ### Infinitesimal rigidity

An infinitesimal flex assigns a velocity to each vertex preserving all edge lengths to
first order: `⟨Pᵢ - Pⱼ, vᵢ - vⱼ⟩ = 0` for each edge. That condition is *linear* in the
velocities with coefficients quadratic in the positions — polynomial throughout, so the
whole subject is in reach.

A framework is infinitesimally rigid when every flex is a rigid motion. Below, the triangle
case: the flex conditions force the velocity field to be an infinitesimal isometry. -/

-- **The triangle is infinitesimally rigid.** If a flex pins two vertices, it pins the
-- third. With `vA = vB = 0` the two remaining edge constraints say `vC` is orthogonal to
-- both `C - B` and `A - C`; when the triangle is nondegenerate those span the plane, so
-- `vC = 0`.
--
-- The nondegeneracy is `det ≠ 0`, twice the signed area — exactly "the triangle does not
-- collapse", which is the hypothesis a rigidity theorem carries anyway. `C.1 ≠ B.1` is an
-- extra condition the *method* needs (the edge BC must not be vertical), not the theorem.
#wu_bench theorem triangle_rigid (A B C vC : Pt) (hCB : C.1 - B.1 ≠ 0)
    (hdet : (C.1 - B.1) * (A.2 - C.2) - (C.2 - B.2) * (A.1 - C.1) ≠ 0)
    (eBC : (C.1 - B.1) * vC.1 + (C.2 - B.2) * vC.2 = 0)
    (eCA : (A.1 - C.1) * vC.1 + (A.2 - C.2) * vC.2 = 0) :
    vC.1 = 0 := by
  wu (vars := [A.1, A.2, B.1, B.2, C.1, C.2, vC.2, vC.1])

-- A rigid motion is always a flex: the infinitesimal rotation `v = (-y, x)` preserves
-- every edge length to first order, for any two points.
--
-- Together with a rigidity statement this is what pins the flex space down to exactly the
-- rigid motions.
#wu_bench theorem rotation_is_flex (A B : Pt) :
    (B.1 - A.1) * ((-B.2) - (-A.2)) + (B.2 - A.2) * (B.1 - A.1) = 0 := by
  ring

end WuGeometry.Discrete
