/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DerivationLocalization
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

end Wu
