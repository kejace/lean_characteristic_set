/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Basic

/-!
# Extending a derivation of the coefficients to a multivariate polynomial ring

`MvPolynomial.mkDerivation` builds the derivations that are **linear over the coefficient
ring**, so they annihilate it. The complementary construction — take a derivation *of* the
coefficient ring and let it act coefficientwise, killing the indeterminates — is missing.

Mathlib has it for `Polynomial` (`Derivation.mapCoeffs`) and not for `MvPolynomial`; that
construction goes through `PolynomialModule` and does not transfer.

## Why this is needed

`Wu.DiffPolynomial` is `R{y}` with `D` built by `mkDerivation`, hence `R`-linear, hence
annihilating `R`. Kolchin's `R{Y}` is over a *differential* ring, and the difference is not
cosmetic: with `R` a ring of constants there is no `x` with `D x = 1`, and the variational
complex is genuinely not exact at the Lagrangian slot —
`Wu.Variational.range_deriv_lt_ker_E` is that failure, formalized.

Adding this to the shift gives the general total derivative, `D (C r) = C (d r)` and
`D (y^(k)) = y^(k+1)`.

## Note on the base

Over a general commutative base `S` rather than `ℤ`, for the reason recorded throughout this
project: Mathlib's `Differential` class fixes the base to `ℤ` and so takes `Module ℤ` from
`AddCommGroup.toIntModule`, while anything built from an `Algebra` structure takes it from
`Algebra.toModule`, and the two are not definitionally equal.
-/

open Finset

namespace MvPolynomial

variable {S R σ : Type*} [CommRing S] [CommRing R] [Algebra S R] (d : Derivation S R R)

/-- Apply `d` to every coefficient. Defined by an explicit sum over the support; the lemma
that makes it usable is `mapCoeffsFun_eq_sum`, which lets the sum run over *any* finite
superset of the support. -/
noncomputable def mapCoeffsFun (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ m ∈ p.support, monomial m (d (coeff m p))

/-- **The sum may be taken over any superset of the support.** Everything below is a
corollary: additivity, homogeneity and the monomial formula all come from choosing a common
superset for the polynomials involved. -/
theorem mapCoeffsFun_eq_sum {p : MvPolynomial σ R} {s : Finset (σ →₀ ℕ)}
    (hs : p.support ⊆ s) :
    mapCoeffsFun d p = ∑ m ∈ s, monomial m (d (coeff m p)) := by
  rw [mapCoeffsFun]
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [notMem_support_iff] at hm
  rw [hm, map_zero, monomial_zero]

theorem mapCoeffsFun_add (p q : MvPolynomial σ R) :
    mapCoeffsFun d (p + q) = mapCoeffsFun d p + mapCoeffsFun d q := by
  classical
  set s : Finset (σ →₀ ℕ) := (p + q).support ∪ (p.support ∪ q.support) with hs
  rw [mapCoeffsFun_eq_sum d (s := s) (by exact subset_union_left),
    mapCoeffsFun_eq_sum d (s := s) (by exact (subset_union_left).trans subset_union_right),
    mapCoeffsFun_eq_sum d (s := s) (by exact (subset_union_right).trans subset_union_right),
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => by simp [coeff_add]

theorem mapCoeffsFun_smul (c : S) (p : MvPolynomial σ R) :
    mapCoeffsFun d (c • p) = c • mapCoeffsFun d p := by
  classical
  set s : Finset (σ →₀ ℕ) := (c • p).support ∪ p.support with hs
  rw [mapCoeffsFun_eq_sum d (s := s) (by exact subset_union_left),
    mapCoeffsFun_eq_sum d (s := s) (by exact subset_union_right), Finset.smul_sum]
  exact Finset.sum_congr rfl fun m _ => by
    rw [coeff_smul, Derivation.map_smul, smul_monomial]

/-- Apply `d` to every coefficient, as an `S`-linear map. -/
noncomputable def mapCoeffsₗ : MvPolynomial σ R →ₗ[S] MvPolynomial σ R where
  toFun := mapCoeffsFun d
  map_add' := mapCoeffsFun_add d
  map_smul' c p := mapCoeffsFun_smul d c p

theorem mapCoeffsₗ_monomial (m : σ →₀ ℕ) (a : R) :
    mapCoeffsₗ d (monomial m a) = monomial m (d a) := by
  classical
  change mapCoeffsFun d _ = _
  rw [mapCoeffsFun_eq_sum d (s := {m}) support_monomial_subset, Finset.sum_singleton,
    coeff_monomial]
  simp

theorem mapCoeffsₗ_C (a : R) : mapCoeffsₗ (σ := σ) d (C a) = C (d a) := by
  rw [C_apply, mapCoeffsₗ_monomial, C_apply]

/-- **A derivation of the coefficients, extended to the polynomial ring.**

`D (C r) = C (d r)` and `D (X i) = 0`: the indeterminates are constants for it. This is the
`MvPolynomial` counterpart of Mathlib's `Derivation.mapCoeffs`. -/
noncomputable def mapCoeffsDeriv : Derivation S (MvPolynomial σ R) (MvPolynomial σ R) where
  toLinearMap := mapCoeffsₗ d
  map_one_eq_zero' := by
    change mapCoeffsₗ d (1 : MvPolynomial σ R) = 0
    rw [← C_1, mapCoeffsₗ_C]
    simp
  leibniz' p q := by
    change mapCoeffsₗ d (p * q) = _
    induction p using MvPolynomial.induction_on' with
    | add p₁ p₂ h₁ h₂ =>
        simp only [add_mul, map_add, smul_add, add_smul, h₁, h₂]
        abel
    | monomial m a =>
        induction q using MvPolynomial.induction_on' with
        | add q₁ q₂ k₁ k₂ =>
            simp only [mul_add, map_add, smul_add, add_smul, k₁, k₂]
            abel
        | monomial n b =>
            rw [monomial_mul, mapCoeffsₗ_monomial, mapCoeffsₗ_monomial, mapCoeffsₗ_monomial,
              Derivation.leibniz]
            simp only [smul_eq_mul, monomial_mul, map_add]
            rw [add_comm n m]

variable {d}

@[simp] theorem mapCoeffsDeriv_monomial (m : σ →₀ ℕ) (a : R) :
    mapCoeffsDeriv d (monomial m a) = monomial m (d a) :=
  mapCoeffsₗ_monomial d m a

@[simp] theorem mapCoeffsDeriv_C (a : R) :
    mapCoeffsDeriv (σ := σ) d (C a) = C (d a) :=
  mapCoeffsₗ_C d a

/-- **The indeterminates are constants** for the coefficient derivation. This is the half
`mkDerivation` cannot supply; adding the two gives a derivation that moves both. -/
@[simp] theorem mapCoeffsDeriv_X (i : σ) :
    mapCoeffsDeriv (σ := σ) d (X i) = 0 := by
  rw [X, mapCoeffsDeriv_monomial]
  simp

end MvPolynomial
