/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Frontend
import Mathlib.Data.Real.Basic

/-!
# Plane geometry predicates for `wu`

Wu's method proves geometry theorems by turning them into polynomial identities in point
coordinates. Stating theorems directly in coordinates is unreadable, so this file provides
the usual predicates together with `@[wu_unfold]` lemmas that reduce each one to its
polynomial form. `wu` applies that simp set before reflecting, so a theorem can be stated
the way a geometer would write it and still be proved by the engine.

## Why these particular forms

Every predicate is chosen to unfold to a *polynomial equation*, never an inequality or a
division:

* `Collinear₃` is the vanishing of the cross product, not "equal slopes" — slopes need
  division and break on vertical lines.
* `Perp` is the vanishing of the dot product.
* `EqDist` compares *squared* distances, so no square roots appear.
* `Concyclic` uses the classical determinant condition for four points on a circle,
  expanded so that the circle's centre and radius never have to be named.

Predicates that genuinely need two scalar equations (`Midpoint`, `Parallelogram`) unfold to
a conjunction; `wu` splits those automatically.
-/

namespace WuGeometry

/-- A point of the affine plane, in Cartesian coordinates. -/
abbrev Pt := ℝ × ℝ

namespace Pt

/-- The `x` coordinate. -/
abbrev x (P : Pt) : ℝ := P.1

/-- The `y` coordinate. -/
abbrev y (P : Pt) : ℝ := P.2

end Pt

/-- `A`, `B`, `C` are collinear: the cross product of `B - A` and `C - A` vanishes. -/
def Collinear₃ (A B C : Pt) : Prop :=
  (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) = 0

@[wu_unfold] theorem collinear₃_def (A B C : Pt) :
    Collinear₃ A B C ↔ (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) = 0 := Iff.rfl

/-- Line `AB` is perpendicular to line `CD`: the dot product vanishes. -/
def Perp (A B C D : Pt) : Prop :=
  (B.1 - A.1) * (D.1 - C.1) + (B.2 - A.2) * (D.2 - C.2) = 0

@[wu_unfold] theorem perp_def (A B C D : Pt) :
    Perp A B C D ↔ (B.1 - A.1) * (D.1 - C.1) + (B.2 - A.2) * (D.2 - C.2) = 0 := Iff.rfl

/-- Line `AB` is parallel to line `CD`. -/
def Para (A B C D : Pt) : Prop :=
  (B.1 - A.1) * (D.2 - C.2) - (D.1 - C.1) * (B.2 - A.2) = 0

@[wu_unfold] theorem para_def (A B C D : Pt) :
    Para A B C D ↔ (B.1 - A.1) * (D.2 - C.2) - (D.1 - C.1) * (B.2 - A.2) = 0 := Iff.rfl

/-- `M` is the midpoint of `A` and `B`. Two scalar equations, one per coordinate. -/
def Midpoint (M A B : Pt) : Prop :=
  2 * M.1 - (A.1 + B.1) = 0 ∧ 2 * M.2 - (A.2 + B.2) = 0

@[wu_unfold] theorem midpoint_def (M A B : Pt) :
    Midpoint M A B ↔ (2 * M.1 - (A.1 + B.1) = 0 ∧ 2 * M.2 - (A.2 + B.2) = 0) := Iff.rfl

/-- `|AB| = |CD|`, compared as squared distances so that no square root appears. -/
def EqDist (A B C D : Pt) : Prop :=
  (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 - ((D.1 - C.1) ^ 2 + (D.2 - C.2) ^ 2) = 0

@[wu_unfold] theorem eqDist_def (A B C D : Pt) :
    EqDist A B C D ↔
      (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 - ((D.1 - C.1) ^ 2 + (D.2 - C.2) ^ 2) = 0 := Iff.rfl

/-- `ABCD` is a parallelogram: `AB` and `DC` are equal as vectors. -/
def Parallelogram (A B C D : Pt) : Prop :=
  B.1 - A.1 - (C.1 - D.1) = 0 ∧ B.2 - A.2 - (C.2 - D.2) = 0

@[wu_unfold] theorem parallelogram_def (A B C D : Pt) :
    Parallelogram A B C D ↔
      (B.1 - A.1 - (C.1 - D.1) = 0 ∧ B.2 - A.2 - (C.2 - D.2) = 0) := Iff.rfl

/-- `P` lies on the circle with centre `O` through `A`. -/
def OnCircle (P O A : Pt) : Prop :=
  (P.1 - O.1) ^ 2 + (P.2 - O.2) ^ 2 - ((A.1 - O.1) ^ 2 + (A.2 - O.2) ^ 2) = 0

@[wu_unfold] theorem onCircle_def (P O A : Pt) :
    OnCircle P O A ↔
      (P.1 - O.1) ^ 2 + (P.2 - O.2) ^ 2 - ((A.1 - O.1) ^ 2 + (A.2 - O.2) ^ 2) = 0 := Iff.rfl

/-- `P` is the foot of the perpendicular from `X` to line `AB`: `P` is on `AB`, and `XP`
is perpendicular to `AB`. -/
def Foot (P X A B : Pt) : Prop :=
  Collinear₃ A B P ∧ Perp X P A B

@[wu_unfold] theorem foot_def (P X A B : Pt) :
    Foot P X A B ↔ (Collinear₃ A B P ∧ Perp X P A B) := Iff.rfl

/-- `M` is the intersection of lines `AB` and `CD`. -/
def Inter (M A B C D : Pt) : Prop :=
  Collinear₃ A B M ∧ Collinear₃ C D M

@[wu_unfold] theorem inter_def (M A B C D : Pt) :
    Inter M A B C D ↔ (Collinear₃ A B M ∧ Collinear₃ C D M) := Iff.rfl

/-- Four points are concyclic.

This is the classical `4 × 4` determinant condition for concyclicity, expanded. Writing it
this way avoids having to introduce the circle's centre and radius as extra variables,
which would enlarge the polynomial system Wu's method has to triangularise. -/
def Concyclic (A B C D : Pt) : Prop :=
  ((A.1 ^ 2 + A.2 ^ 2) * ((B.1 - C.1) * (C.2 - D.2) - (C.1 - D.1) * (B.2 - C.2))
    - (B.1 ^ 2 + B.2 ^ 2) * ((A.1 - C.1) * (C.2 - D.2) - (C.1 - D.1) * (A.2 - C.2))
    + (C.1 ^ 2 + C.2 ^ 2) * ((A.1 - B.1) * (B.2 - D.2) - (B.1 - D.1) * (A.2 - B.2))
    - (D.1 ^ 2 + D.2 ^ 2) * ((A.1 - B.1) * (B.2 - C.2) - (B.1 - C.1) * (A.2 - B.2))) = 0

@[wu_unfold] theorem concyclic_def (A B C D : Pt) :
    Concyclic A B C D ↔
      ((A.1 ^ 2 + A.2 ^ 2) * ((B.1 - C.1) * (C.2 - D.2) - (C.1 - D.1) * (B.2 - C.2))
        - (B.1 ^ 2 + B.2 ^ 2) * ((A.1 - C.1) * (C.2 - D.2) - (C.1 - D.1) * (A.2 - C.2))
        + (C.1 ^ 2 + C.2 ^ 2) * ((A.1 - B.1) * (B.2 - D.2) - (B.1 - D.1) * (A.2 - B.2))
        - (D.1 ^ 2 + D.2 ^ 2) * ((A.1 - B.1) * (B.2 - C.2) - (B.1 - C.1) * (A.2 - B.2))) = 0 :=
  Iff.rfl

/-- The image of `P` under the homothety of ratio `t` centred at the origin.

Used to state perspectivity from a point: two triangles are perspective from the origin
exactly when corresponding vertices are related by homotheties. Parametrising by the ratios
instead of giving the second triangle three free vertices plus three collinearity
constraints is what brings Desargues' theorem into range — it removes three hypotheses and
six variables, and Wu's method is very sensitive to both. -/
def homothety (t : ℝ) (P : Pt) : Pt := (t * P.1, t * P.2)

@[wu_unfold] theorem homothety_fst (t : ℝ) (P : Pt) : (homothety t P).1 = t * P.1 := rfl

@[wu_unfold] theorem homothety_snd (t : ℝ) (P : Pt) : (homothety t P).2 = t * P.2 := rfl

end WuGeometry
