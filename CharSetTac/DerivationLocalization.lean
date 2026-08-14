/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic.LinearCombination

/-!
# A derivation extends to a localization

`d(a/s) = (s · d a - a · d s) / s²`. Classical, and **absent from Mathlib** — there is no
`Derivation` × `Localization` interaction anywhere in the library, and the only lifting
results (`Derivation.liftOfRightInverse`, `liftOfSurjective`) do not apply.

This is the linchpin for a differential structure sheaf: `Spec^Δ(R)` needs `𝒪(D(f)) = R_f`
to carry a derivation, and `restrict_deriv` — which `CharSetTac/DiffSheaf.lean` currently
*assumes* — is exactly the statement that these extensions commute with restriction.

## Why via dual numbers

Defining `D` on `B` directly means choosing a representative `a/s` and proving independence
of the choice, which in a general localization (zero divisors, the `∃ t ∈ S` in the equality
test) is unpleasant.

The dual numbers make well-definedness someone else's problem. A derivation is the same
thing as a ring homomorphism `a ↦ a + (d a)ε` into `A[ε]`, because the multiplication in a
square-zero extension *is* the Leibniz rule. Push that into `B[ε]`, observe that every
`s ∈ S` lands on a unit there (a dual number is a unit exactly when its real part is), and
`IsLocalization.lift` produces the extension with no representative-chasing at all. The
derivation is then read off the `ε`-component.

## Mathlib candidates

Three of the pieces below are general-purpose and belong upstream rather than here:
`TrivSqZeroExt.isUnit_of_isUnit_fst`, `Derivation.toDualHom`, and `Derivation.localization`
itself.
-/

open TrivSqZeroExt

-- These live in root namespaces on purpose: they are general-purpose statements about
-- Mathlib types, and the intent is to upstream them.

section Units

variable {A : Type*} [CommRing A]

/-- **A dual number is a unit exactly when its real part is.**

`(u, v)⁻¹ = (u⁻¹, -u⁻²v)`, which is the usual expansion of `1/(u + vε)` truncated at `ε²`.
Stated for a general square-zero extension, where it is no harder. -/
theorem TrivSqZeroExt.isUnit_of_isUnit_fst {x : TrivSqZeroExt A A} (h : IsUnit x.fst) :
    IsUnit x := by
  obtain ⟨u, hu⟩ := h
  -- the only fact `ring` cannot supply: `u⁻¹ · u⁻¹ · u = u⁻¹`
  have key : (↑u⁻¹ : A) * (↑u⁻¹ : A) * (↑u : A) = (↑u⁻¹ : A) := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  refine ⟨⟨x, inl (↑u⁻¹ : A) - inr (((↑u⁻¹ : A) * (↑u⁻¹ : A)) * x.snd), ?_, ?_⟩, rfl⟩ <;>
    refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [← hu, smul_eq_mul, Units.mul_inv, Units.inv_mul] <;>
      first
        | linear_combination (-x.snd) * key
        | linear_combination x.snd * key

end Units

section ToDual

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

namespace Derivation

/-- **A derivation, as a ring homomorphism into the dual numbers.** `a ↦ a + (d a)ε`.

This is a homomorphism precisely because multiplication in a square-zero extension is the
Leibniz rule; nothing else is going on. -/
def toDualHom (d : Derivation R A A) : A →+* TrivSqZeroExt A A where
  toFun a := inl a + inr (d a)
  map_one' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' a b := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [Derivation.leibniz, smul_eq_mul] <;> ring

@[simp] theorem toDualHom_fst (d : Derivation R A A) (a : A) :
    (d.toDualHom a).fst = a := by simp [toDualHom]

@[simp] theorem toDualHom_snd (d : Derivation R A A) (a : A) :
    (d.toDualHom a).snd = d a := by simp [toDualHom]

end Derivation

end ToDual

section Functorial

variable {A B : Type*} [CommRing A] [CommRing B]

namespace TrivSqZeroExt

/-- A ring homomorphism induces one on dual numbers, componentwise. -/
def dualMap (f : A →+* B) : TrivSqZeroExt A A →+* TrivSqZeroExt B B where
  toFun x := inl (f x.fst) + inr (f x.snd)
  map_one' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_zero' := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_add' x y := by refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [smul_eq_mul] <;> ring

@[simp] theorem dualMap_fst (f : A →+* B) (x : TrivSqZeroExt A A) :
    (dualMap f x).fst = f x.fst := by simp [dualMap]

@[simp] theorem dualMap_snd (f : A →+* B) (x : TrivSqZeroExt A A) :
    (dualMap f x).snd = f x.snd := by simp [dualMap]

end TrivSqZeroExt

end Functorial

section Localization

namespace Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {B : Type*} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- The composite `A →+* B[ε]`, `a ↦ a + (d a)ε` followed by localization. -/
noncomputable def toDualLift (d : Derivation R A A) (B : Type*) [CommRing B] [Algebra A B] :
    A →+* TrivSqZeroExt B B :=
  (TrivSqZeroExt.dualMap (algebraMap A B)).comp d.toDualHom

/-- Every element of `S` lands on a unit, because its real part does. This is the whole
reason the dual-number route avoids well-definedness. -/
theorem toDualLift_isUnit (d : Derivation R A A) (S : Submonoid A) [IsLocalization S B]
    (s : S) : IsUnit (d.toDualLift B s) := by
  apply TrivSqZeroExt.isUnit_of_isUnit_fst
  simpa [toDualLift, TrivSqZeroExt.dualMap] using IsLocalization.map_units B s

/-- The lift to `B →+* B[ε]` supplied by the universal property. -/
noncomputable def dualLift (d : Derivation R A A) (S : Submonoid A) [IsLocalization S B] :
    B →+* TrivSqZeroExt B B :=
  IsLocalization.lift (d.toDualLift_isUnit S)

@[simp] theorem dualLift_algebraMap (d : Derivation R A A) (S : Submonoid A)
    [IsLocalization S B] (a : A) :
    d.dualLift S (algebraMap A B a) = d.toDualLift B a :=
  IsLocalization.lift_eq _ a

/-- The lift is a *section*: its real part is the identity. Both sides agree on the image
of `A`, so `IsLocalization.ringHom_ext` finishes it. -/
theorem dualLift_fst (d : Derivation R A A) (S : Submonoid A) [IsLocalization S B] (b : B) :
    (d.dualLift S b).fst = b := by
  have h : ((TrivSqZeroExt.fstHom B B B).toRingHom).comp (d.dualLift S) = RingHom.id B := by
    apply IsLocalization.ringHom_ext S
    ext a
    simp [toDualLift, TrivSqZeroExt.dualMap]
  exact congrArg (fun f => f b) h

/-- **A derivation extends to a localization.** The `ε`-component of the lift.

On representatives this is the quotient rule `d(a/s) = (s·da - a·ds)/s²`; here it arrives
without ever naming a representative. -/
noncomputable def localization (d : Derivation R A A) (S : Submonoid A)
    [IsLocalization S B] : Derivation R B B where
  toFun b := (d.dualLift S b).snd
  map_add' b c := by simp
  map_smul' r b := by
    have hr : (algebraMap R B r) = algebraMap A B (algebraMap R A r) := by
      simp [IsScalarTower.algebraMap_apply R A B]
    have hz : (d.dualLift S (algebraMap R B r)).snd = 0 := by
      rw [hr, dualLift_algebraMap]
      simp [toDualLift, TrivSqZeroExt.dualMap]
    rw [Algebra.smul_def, map_mul, TrivSqZeroExt.snd_mul, hz, dualLift_fst]
    simp [Algebra.smul_def, smul_eq_mul]
  map_one_eq_zero' := by simp
  leibniz' b c := by
    show (d.dualLift S (b * c)).snd
      = b • (d.dualLift S c).snd + c • (d.dualLift S b).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, dualLift_fst, dualLift_fst]
    -- `snd_mul` states the second summand with the opposite action; over a commutative
    -- ring that is ordinary multiplication
    simp [smul_eq_mul, mul_comm]

/-- **It extends `d`.** Without this the construction would be worthless: it says the new
derivation restricts to the old one along `A → B`. -/
@[simp] theorem localization_algebraMap (d : Derivation R A A) (S : Submonoid A)
    [IsLocalization S B] (a : A) :
    d.localization S (algebraMap A B a) = algebraMap A B (d a) := by
  show (d.dualLift S (algebraMap A B a)).snd = _
  rw [dualLift_algebraMap]
  simp [toDualLift, TrivSqZeroExt.dualMap, Algebra.smul_def,
    TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]

/-- **The quotient rule**, in cleared form: `s² · d(a/s) = s · da - a · ds`.

This is the formula one would have written down directly, recovered from a construction
that never mentioned a representative. Proof: apply Leibniz to `(a/s) · s = a` and multiply
through by `s`. -/
theorem localization_mk' (d : Derivation R A A) (S : Submonoid A) [IsLocalization S B]
    (a : A) (s : S) :
    (algebraMap A B (s : A)) ^ 2 * d.localization S (IsLocalization.mk' B a s)
      = algebraMap A B (s : A) * algebraMap A B (d a)
        - algebraMap A B a * algebraMap A B (d (s : A)) := by
  have hmk : IsLocalization.mk' B a s * algebraMap A B (s : A) = algebraMap A B a :=
    IsLocalization.mk'_spec B a s
  have hleib := congrArg (d.localization S) hmk
  rw [Derivation.leibniz, localization_algebraMap, localization_algebraMap] at hleib
  simp only [smul_eq_mul] at hleib
  -- multiply Leibniz through by `s`, then use `mk' · s = a` to replace `s · mk'`
  linear_combination (algebraMap A B (s : A)) * hleib
    - (algebraMap A B (d (s : A))) * hmk

end Derivation

end Localization
