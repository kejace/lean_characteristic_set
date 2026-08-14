/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DiffPolynomialExamples
import CharSetTac.RadicalDiffIdeal
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# `R{y}` against real Mathlib

`CharSetTac/DiffPolynomialExamples.lean` shows `R{y}` working against a polynomial ring, which
keeps everything computable but proves little about whether the object connects to the rest of
the library. This file runs it against two pieces of genuine Mathlib machinery.

## 1. The Lie algebra of derivations

Mathlib makes `Derivation R A A` a Lie algebra (`Derivation.instLieAlgebra`), with
`⁅D₁, D₂⁆ a = D₁ (D₂ a) - D₂ (D₁ a)`. `R{y}` carries two natural derivations — the **shift**
`d`, which is the differential structure, and the **grading** `E : y^(k) ↦ k·y^(k)`, which
records differentiation order — and they do not commute:

`⁅E, d⁆ = d`

So they span a two-dimensional **non-abelian** Lie subalgebra of `Der(R{y})`: the affine
algebra, the unique non-abelian Lie algebra of dimension 2. This is the precise sense in which
"differentiating raises order by exactly one", and it is a statement Mathlib's Lie API can
express directly.

Note the contrast with the *partial* case (`CharSetTac/MathlibableEvidence.lean`): there the
several shift derivations `d_δ` commute with each other, i.e. they span an *abelian*
subalgebra. The grading is what breaks commutativity, not the shifts.

## 2. Power series, and `exp` as a differential-algebraic solution

`PowerSeries.derivative` is *literally* a `Derivation R R⟦X⟧ R⟦X⟧`, so `R{y}`'s universal
property applies to it with nothing to adapt. Substituting `y := exp` gives a differential
algebra map `ℚ{y} → ℚ⟦X⟧`, and the payoff is:

**every differential consequence of `y' = y` vanishes at `exp`** — the whole radical
differential ideal `{y' - y}`, not merely the generator and its prolongations.

That statement needs the kernel to be a *radical differential* ideal, which is exactly what
`evalDiff_deriv` (differential) and `RingHom.ker_isPrime` (radical, since `ℚ⟦X⟧` is a domain)
supply. It is the first place the whole stack — `R{y}`, its universal property, `IsDiffIdeal`
and `radicalDiffIdeal` — is used at once against an object nobody built for the purpose.

Finally the two uniqueness theorems meet: Mathlib's
`PowerSeries.exp_unique_of_derivative_eq_self` says `exp` is the only power series with
`f' = f` and `f(0) = 1`; our `evalDiff_unique` says the substitution sending `y` there is the
only differential map doing so.
-/

open MvPolynomial PowerSeries

namespace Wu.DiffPolynomialHeavy

open Wu.DiffPolynomialExamples (expOde)

/-- `y[k]` is `y^(k)`. -/
local notation "y[" k "]" => Wu.DiffPolynomial.Y (() : Unit) k

/-- `d` is the shift derivation of `ℚ{y}`. -/
local notation "d" => Wu.DiffPolynomial.deriv ℚ Unit

/-! ### 1. `⁅E, d⁆ = d` -/

/-- **The grading derivation** `E : y^(k) ↦ k · y^(k)`.

A derivation because it is `mkDerivation` of *something*; the content is only in what it does
to the generators. On a monomial it returns the total differentiation order, so `E` is the
Euler operator for the grading by order. -/
noncomputable def gradeDeriv :
    Derivation ℚ (Wu.DiffPolynomial ℚ Unit) (Wu.DiffPolynomial ℚ Unit) :=
  mkDerivation ℚ fun p => (p.2 : ℚ) • X p

@[simp] theorem gradeDeriv_X (p : Unit × ℕ) : gradeDeriv (X p) = (p.2 : ℚ) • X p :=
  mkDerivation_X _ _ _

/-- **The shift and the grading span the affine Lie algebra**: `⁅E, d⁆ = d`.

Two derivations agreeing on the generators are equal (`MvPolynomial.derivation_ext`), so the
whole statement reduces to `y^(k)`, where it is `(k+1) - k = 1`: applying `E` after `d` sees
order `k+1`, applying `d` after `E` still sees the `k` that `E` already read off.

In particular the bracket is *not* zero, so these two derivations generate a non-abelian
subalgebra of `Der(ℚ{y})`. -/
theorem lie_gradeDeriv_deriv : ⁅gradeDeriv, d⁆ = d := by
  apply MvPolynomial.derivation_ext
  rintro ⟨u, k⟩
  rw [Derivation.commutator_apply]
  simp only [Wu.DiffPolynomial.deriv_X, gradeDeriv_X, Derivation.map_smul]
  push_cast
  rw [add_smul, one_smul, add_sub_cancel_left]

/-- The bracket is genuinely nonzero, so the subalgebra really is non-abelian. -/
theorem lie_gradeDeriv_deriv_ne_zero : ⁅gradeDeriv, d⁆ ≠ 0 := by
  rw [lie_gradeDeriv_deriv]
  intro h
  have : d y[0] = 0 := by rw [h]; rfl
  rw [Wu.DiffPolynomial.deriv_Y] at this
  exact (MvPolynomial.X_ne_zero _) this

/-! ### 2. `exp` as a solution of `y' = y` -/

/-- **Substituting `y := exp`** into `ℚ{y}`, landing in formal power series with their formal
derivative. `PowerSeries.derivative` is already a `Derivation`, so the universal property
applies with nothing to adapt. -/
noncomputable def atExp : Wu.DiffPolynomial ℚ Unit →ₐ[ℚ] PowerSeries ℚ :=
  Wu.DiffPolynomial.evalDiff (PowerSeries.derivative ℚ) fun _ => PowerSeries.exp ℚ

/-- Differentiating `exp` any number of times gives `exp` back. -/
theorem iterate_derivative_exp (k : ℕ) :
    ((PowerSeries.derivative ℚ : PowerSeries ℚ → PowerSeries ℚ))^[k] (PowerSeries.exp ℚ)
      = PowerSeries.exp ℚ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, PowerSeries.derivative_exp]

/-- **Every** derivative of `y` goes to `exp` — which is what it means for `exp` to solve
`y' = y`. -/
@[simp] theorem atExp_Y (k : ℕ) : atExp y[k] = PowerSeries.exp ℚ := by
  rw [atExp, Wu.DiffPolynomial.evalDiff_Y, iterate_derivative_exp]

/-- `exp` is a zero of the ODE. -/
theorem atExp_ode : atExp (y[1] - y[0]) = 0 := by simp

/-- The substitution intertwines the two derivations — `evalDiff_deriv` at this instance. -/
theorem atExp_deriv (p : Wu.DiffPolynomial ℚ Unit) :
    atExp (d p) = PowerSeries.derivative ℚ (atExp p) :=
  Wu.DiffPolynomial.evalDiff_deriv _ _ p

/-- **The kernel is a differential ideal.** This is `evalDiff_deriv` doing the work: if `p`
dies then so does `d p`, because the substitution turns `d` into `d/dX` and `d/dX 0 = 0`. -/
theorem isDiffIdeal_ker : IsDiffIdeal d (RingHom.ker (atExp : _ →+* PowerSeries ℚ)) := by
  intro p hp
  rw [RingHom.mem_ker] at hp ⊢
  simp only [RingHom.coe_coe] at hp ⊢
  rw [atExp_deriv, hp, map_zero]

/-- The kernel is radical, because `ℚ⟦X⟧` is a domain and so the kernel is prime. -/
theorem isRadicalDiffIdeal_ker :
    IsRadicalDiffIdeal d (RingHom.ker (atExp : _ →+* PowerSeries ℚ)) :=
  ⟨(RingHom.ker_isPrime _).isRadical, isDiffIdeal_ker⟩

/-- **Every differential consequence of `y' = y` vanishes at `exp`.**

Not just the generator, and not just its prolongations: the entire *radical differential
ideal* `{y' - y}`, which is closed under differentiation, ideal operations, and taking roots.

The proof is one application of the closure operator's universal property. All the content is
in the two facts above — that the kernel is differential (from `evalDiff_deriv`) and radical
(from `ℚ⟦X⟧` being a domain). -/
theorem radicalDiffIdeal_le_ker :
    radicalDiffIdeal d {y[1] - y[0]} ≤ RingHom.ker (atExp : _ →+* PowerSeries ℚ) := by
  refine radicalDiffIdeal.le_of_subset ?_ isRadicalDiffIdeal_ker
  rintro _ rfl
  simp [RingHom.mem_ker]

/-- The same for the explicitly-prolonged generating set of
`CharSetTac/DiffPolynomialExamples.lean`: `exp` kills every prolongation `y^(k+1) - y^(k)`. -/
theorem span_expOde_le_ker :
    Ideal.span expOde ≤ RingHom.ker (atExp : _ →+* PowerSeries ℚ) := by
  rw [Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  simp [RingHom.mem_ker]

/-! ### The two uniqueness theorems meet -/

/-- **Mathlib's uniqueness and ours, composed.** `exp` is the only power series with `f' = f`
and `f(0) = 1` (`PowerSeries.exp_unique_of_derivative_eq_self`), and the substitution sending
`y` to it is the only differential algebra map doing so (`evalDiff_unique`). So any `f`
solving the ODE with the right constant term induces *the same* map out of `ℚ{y}`. -/
theorem evalDiff_eq_atExp_of_solution (f : PowerSeries ℚ)
    (hf : PowerSeries.derivative ℚ f = f) (hc : PowerSeries.constantCoeff f = 1) :
    Wu.DiffPolynomial.evalDiff (PowerSeries.derivative ℚ) (fun _ => f) = atExp := by
  have : f = PowerSeries.exp ℚ := PowerSeries.exp_unique_of_derivative_eq_self hf hc
  subst this
  rfl

end Wu.DiffPolynomialHeavy
