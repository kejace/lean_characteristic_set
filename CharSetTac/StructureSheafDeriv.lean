/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DerivationLocalization
import CharSetTac.DiffSheaf
import Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# A derivation on the structure sheaf of `Spec A`

Item B step 3. `CharSetTac/DerivationLocalization.lean` extends a derivation to a single
localization; this puts one on `𝒪_{Spec A}`.

## Why it goes through pointwise

Mathlib builds the structure sheaf so that a section over `U` is a dependent function into
the localizations at the primes of `U`, subject to being *locally a fraction*:

```
IsFraction f ↔ ∃ r s, ∀ x : U, f x = LocalizedModule.mk r ⟨s, _⟩
```

So the derivation is applied stalkwise, and the only thing to prove is that the predicate
survives. It does, because **the quotient rule turns a fraction into a fraction**:
`d(r/s) = (s·dr - r·ds)/s²`. That is `Derivation.localization_mk'`, which was written as a
characterisation of the extension and turns out to be the load-bearing lemma here.

Restriction is then composition with an inclusion, so `restrict_deriv` — the axiom that
`CharSetTac/DiffSheaf.lean` assumes — is almost definitional: both sides apply the same
stalk derivation at the same primes.
-/

open AlgebraicGeometry StructureSheaf TopologicalSpace

namespace Wu

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]

/-! ### The stalk derivation

Over a general base ring `R`, not `ℤ`. That is forced rather than chosen: Mathlib's
`Differential` class fixes the base to `ℤ` and so takes `Module ℤ` from
`AddCommGroup.toIntModule`, whereas anything built from an `Algebra` structure — such as
everything produced by `Derivation.localization` — takes it from `Algebra.toModule`. The two
are not definitionally equal, and no amount of massaging makes a localized derivation fit
the `Differential` shape. `Wu.DiffPresheaf` was generalised over a base ring for the same
reason. -/

/-- The derivation induced on the localization at a prime. -/
noncomputable def stalkDeriv (d : Derivation R A A) (P : PrimeSpectrum A) :
    Derivation R (Localizations A P) (Localizations A P) :=
  d.localization (B := Localizations A P) P.asIdeal.primeCompl

/-- `LocalizedModule.mk` is `IsLocalization.mk'`. The structure sheaf is phrased with the
first, `Derivation.localization` with the second. -/
theorem localizedModule_mk_eq_mk' (P : PrimeSpectrum A) (r : A)
    (s : P.asIdeal.primeCompl) :
    (LocalizedModule.mk r s : Localizations A P)
      = IsLocalization.mk' (Localizations A P) r s := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalization.mk'_eq_mk']
  congr 1

/-- **The quotient rule at a stalk.** A fraction goes to a fraction — which is exactly the
predicate `isLocallyFraction` that the structure sheaf's sections satisfy, so this is what
will let the derivation act sectionwise. -/
theorem stalkDeriv_mk (d : Derivation R A A) (P : PrimeSpectrum A) (r : A)
    (s : P.asIdeal.primeCompl) :
    stalkDeriv d P (LocalizedModule.mk r s)
      = LocalizedModule.mk (s * d r - r * d s) (s * s) := by
  rw [localizedModule_mk_eq_mk', localizedModule_mk_eq_mk', eq_comm,
    IsLocalization.mk'_eq_iff_eq_mul]
  have h := Derivation.localization_mk' (B := Localizations A P) d P.asIdeal.primeCompl r s
  simp only [stalkDeriv, Submonoid.coe_mul, map_mul, map_sub] at h ⊢
  linear_combination -h

/-! ### Sections

A section over `U` is a dependent function into the stalks that is *locally a fraction*.
The derivation acts pointwise, and `stalkDeriv_mk` is exactly what keeps the predicate. -/

/-- The pointwise action on dependent functions into the stalks. -/
noncomputable def sectionDeriv (d : Derivation R A A)
    {U : Opens (PrimeSpectrum.Top A)} (f : ∀ x : U, Localizations A x.1) :
    ∀ x : U, Localizations A x.1 :=
  fun x => stalkDeriv d x.1 (f x)

/-- **The predicate survives.** If `f` is locally `r/s`, then `D f` is locally
`(s·dr - r·ds)/s²` — on the *same* neighbourhood, with no shrinking. -/
theorem sectionDeriv_mem (d : Derivation R A A) {U : Opens (PrimeSpectrum.Top A)}
    {f : ∀ x : U, Localizations A x.1}
    (hf : f ∈ StructureSheaf.sectionsSubalgebra (R := A) A U) :
    sectionDeriv d f ∈ StructureSheaf.sectionsSubalgebra (R := A) A U := by
  intro x
  obtain ⟨V, m, i, r, s, w⟩ := hf x
  refine ⟨V, m, i, s * d r - r * d s, s * s, fun y => ?_⟩
  obtain ⟨hs, hw⟩ := w y
  have hp : (y : PrimeSpectrum.Top A).asIdeal.IsPrime := (y : PrimeSpectrum.Top A).isPrime
  refine ⟨fun hmem => (hp.mem_or_mem hmem).elim hs hs, ?_⟩
  -- `hw` is stated about the composite; beta-reduce it to talk about `f (i y)`
  have hw' : f (i y) = LocalizedModule.mk r ⟨s, hs⟩ := hw
  change stalkDeriv d _ (f (i y)) = _
  rw [hw']
  exact stalkDeriv_mk d _ r ⟨s, hs⟩

/-! ### Sections as a ring, pointwise

Every ring operation on sections is inherited from the product, hence pointwise, hence
`rfl`. Establishing that *first* is what makes the rest cheap: the derivation's proof
obligations then reduce to facts about a single stalk, and nothing ever has to unfold the
sheafification. Proving them the other way round runs `whnf` into the ground. -/

section Presheaf

open CategoryTheory Opposite

variable {U : Opens (PrimeSpectrum.Top A)}

/-- Sections of the structure sheaf over `U`. -/
noncomputable abbrev Sections (A : Type*) [CommRing A] (U : Opens (PrimeSpectrum.Top A)) :
    Type _ :=
  (AlgebraicGeometry.structureSheafInType A A).1.obj (op U)

@[simp] theorem sections_mul_apply (f g : Sections A U) (x : (op U).unop) :
    (f * g).1 x = f.1 x * g.1 x := rfl

@[simp] theorem sections_add_apply (f g : Sections A U) (x : (op U).unop) :
    (f + g).1 x = f.1 x + g.1 x := rfl

@[simp] theorem sections_one_apply (x : (op U).unop) : (1 : Sections A U).1 x = 1 := rfl

@[simp] theorem sections_algebraMap_apply (a : A) (x : (op U).unop) :
    (algebraMap A (Sections A U) a).1 x = algebraMap A (Localizations A x.1) a := rfl

/-- The `R`-algebra structure on sections, as the composite `R → A → 𝒪(U)`.

Deliberately not an instance: sections already carry an `A`-algebra structure and a second
global one would be a diamond. `DiffPresheaf` bundles the algebra as a field for exactly
this reason. -/
noncomputable def sectionsAlgebra (R : Type*) [CommRing R] (A : Type*) [CommRing A]
    [Algebra R A] (U : Opens (PrimeSpectrum.Top A)) : Algebra R (Sections A U) :=
  ((algebraMap A (Sections A U)).comp (algebraMap R A)).toAlgebra

/-- **The derivation on sections of `𝒪_{Spec A}`.** `stalkDeriv` applied pointwise, landing
back in the sections by `sectionDeriv_mem`.

Every proof obligation is discharged at a single stalk, via the pointwise lemmas above. -/
noncomputable def sheafDeriv (d : Derivation R A A) (U : Opens (PrimeSpectrum.Top A)) :
    letI := sectionsAlgebra R A U
    Derivation R (Sections A U) (Sections A U) :=
  letI := sectionsAlgebra R A U
  { toFun := fun f => ⟨sectionDeriv d f.1, sectionDeriv_mem d f.2⟩
    map_add' := fun f g => Subtype.ext (funext fun x => map_add (stalkDeriv d x.1) _ _)
    map_smul' := fun r f => Subtype.ext (funext fun x => by
      -- the `R`-action is by a constant from `A`, which the derivation annihilates
      have hc : ((algebraMap R (Sections A U)) r).1 x
          = algebraMap A (Localizations A x.1) (algebraMap R A r) := rfl
      change stalkDeriv d x.1 (((algebraMap R (Sections A U)) r).1 x * f.1 x)
        = ((algebraMap R (Sections A U)) r).1 x * stalkDeriv d x.1 (f.1 x)
      rw [Derivation.leibniz, hc]
      simp [stalkDeriv, Derivation.localization_algebraMap, Derivation.map_algebraMap,
        smul_eq_mul])
    map_one_eq_zero' := Subtype.ext (funext fun x => (stalkDeriv d x.1).map_one_eq_zero)
    leibniz' := fun f g => Subtype.ext (funext fun x => by
      change stalkDeriv d x.1 (f.1 x * g.1 x) = _
      rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      rfl) }

/-- Restriction of sections along an inclusion of opens. Every ring-hom field is `rfl`,
because restriction is precomposition with an inclusion of primes. -/
noncomputable def sectionsRestrict {U V : Opens (PrimeSpectrum.Top A)} (h : V ≤ U) :
    Sections A U →+* Sections A V where
  toFun := (AlgebraicGeometry.structureSheafInType A A).1.map (homOfLE h).op
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_one' := rfl
  map_zero' := rfl

/-- **The differential structure presheaf on `Spec A`.**

This is the gate for Item B: `restrict_deriv` — which `CharSetTac/DiffSheaf.lean` states as
an *axiom* — is here a theorem, and its proof is `rfl`.

That it is `rfl` is the whole design paying off. Restriction is precomposition with an
inclusion of primes, and the derivation acts stalkwise, so both sides of the condition apply
the same stalk derivation at the same prime. Nothing has to commute; it is the same
computation written twice. -/
noncomputable def specDiffPresheaf (d : Derivation R A A) :
    DiffPresheaf R (PrimeSpectrum A) where
  sections U := Sections A U
  commRing U := inferInstance
  algebra U := sectionsAlgebra R A U
  deriv U := sheafDeriv d U
  restrict h := sectionsRestrict h
  restrict_deriv _ _ := rfl

end Presheaf

end Wu
