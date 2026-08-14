/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Basic

/-!
# Evidence for the upstreaming assessment

`MATHLIBABLE_REPORT.md` claims that two declarations in this project should be *restated*
before going to Mathlib. A claim of that kind is worth nothing unless the proposed
restatement actually elaborates — "this hypothesis looks droppable" is a guess, not a
finding. So each proposal is built here.

This file is imported by `CharSetTac.lean` on purpose: if a restatement stops compiling
against a future Mathlib, the report's claim should break loudly rather than rot quietly.

Nothing here is used by the tactic.
-/

open MvPolynomial

/-! ## Test 1 — `Wu.DiffPolynomial` generalised to the Ritt–Kolchin partial case

Literature standard is a *set* `Δ = {δ₁ … δ_m}` of commuting derivations, with
`k{Y} = k[ΘY]` for `Θ` the free commutative monoid on `Δ`. Our shipped form fixes `Θ = ℕ`
(the ordinary, `m = 1` case). Does the `Δ`-indexed form go through? -/

namespace WuTest

variable (R : Type*) [CommRing R] (σ : Type*) (Δ : Type*)

/-- `R{y_σ}` with derivation set `Δ`. -/
abbrev DiffPoly : Type _ := MvPolynomial (σ × (Δ →₀ ℕ)) R

namespace DiffPoly

variable {R σ Δ}

/-- `Y i θ` is `θ y_i`, the derivative of `y_i` along the multi-operator `θ`. -/
noncomputable def Y (i : σ) (θ : Δ →₀ ℕ) : DiffPoly R σ Δ := X (i, θ)

variable (R σ Δ) in
/-- The derivation `δ`, determined by `θ y_i ↦ (δθ) y_i`. -/
noncomputable def deriv (δ : Δ) : Derivation R (DiffPoly R σ Δ) (DiffPoly R σ Δ) :=
  mkDerivation R fun p => X (p.1, p.2 + Finsupp.single δ 1)

@[simp] theorem deriv_Y (δ : Δ) (i : σ) (θ : Δ →₀ ℕ) :
    deriv R σ Δ δ (Y i θ) = Y i (θ + Finsupp.single δ 1) :=
  mkDerivation_X _ _ _

@[simp] theorem deriv_X (δ : Δ) (p : σ × (Δ →₀ ℕ)) :
    deriv R σ Δ δ (X p) = X (p.1, p.2 + Finsupp.single δ 1) :=
  mkDerivation_X _ _ _

/-- **The derivations commute** — this is what makes `R{y}` a partial differential ring
rather than merely a ring carrying several unrelated derivations. -/
theorem deriv_comm (δ δ' : Δ) (p : DiffPoly R σ Δ) :
    deriv R σ Δ δ (deriv R σ Δ δ' p) = deriv R σ Δ δ' (deriv R σ Δ δ p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
      simp only [Derivation.leibniz, deriv_X, smul_eq_mul, map_add,
        add_right_comm n.2 (Finsupp.single δ' 1) (Finsupp.single δ 1)]
      rw [hp]
      ring

end DiffPoly

end WuTest

/-! ## Test 2 — `Derivation.map_ofNat` in Mathlib's own idiom

Mathlib ships `map_ofNat` next to `map_natCast` across the library
(`Nat.Cast.Basic`, `Polynomial.Eval.Defs`, `MvPolynomial.Eval`), and spells the numeral with
the `ofNat(n)` macro from `Mathlib/Tactic/OfNat.lean` rather than a raw `no_index`.
`Derivation` has `map_natCast` but no `map_ofNat`. Does the modernised spelling work, at
Mathlib's own `Derivation` binders? -/

namespace MathlibIdiomTest

variable {R : Type*} {A : Type*} {M : Type*}
variable [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A] [Module A M]
  [Module R M] (D : Derivation R A M)

/-- Proposed upstream form, using Mathlib's `ofNat(n)` macro. -/
@[simp] theorem map_ofNat (n : ℕ) [n.AtLeastTwo] : D ofNat(n) = 0 := by
  rw [← Nat.cast_ofNat]; exact D.map_natCast _

/-- It fires on an actual literal — the reason the lemma exists. Without it, `simp` leaves
`D 2` standing, because `map_natCast` is about `Nat.cast` and a literal is `OfNat.ofNat`. -/
example : D (2 : A) = 0 := by simp

end MathlibIdiomTest
