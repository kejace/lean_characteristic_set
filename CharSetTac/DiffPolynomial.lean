/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Basic

/-!
# The differential polynomial ring `R{y}`

The free differential `R`-algebra on a set of indeterminates: polynomials in the symbols
`y_i^(k)` for `i : σ` and `k : ℕ`, with the derivation that sends `y_i^(k)` to `y_i^(k+1)`.

This is the object Ritt–Raudenbush is *about*, and its absence is what blocks that theorem:
the statement "every radical differential ideal is finitely generated" is a statement about
`R{y₁,…,yₙ}`, and the proof runs through characteristic sets computed inside it. Neither
Mathlib nor TauCeti has it — checked, including sixteen spellings and a `Ritt` grep that
returns 209 hits, all of them the word "written".

## The construction is short, and that is the point

`R{y}` is just `MvPolynomial (σ × ℕ) R` — one indeterminate per (unknown, order) pair — and
the derivation is `MvPolynomial.mkDerivation` applied to `(i, k) ↦ X (i, k+1)`. Everything
else in the file is the *characterisation*: that this really is the free differential
algebra, in the sense that a differential map out of it is exactly a choice of images for
the `y_i`.

Without that characterisation the definition would be a suggestive name attached to a
polynomial ring; with it, `R{y}` is determined up to unique isomorphism and the name is
earned.

## Note on the base

Stated over a general `CommRing R` with `Derivation R`, not Mathlib's `Differential` class,
which fixes the base to `ℤ` and puts `Module ℤ` on the wrong side of the
`Algebra`/`AddCommGroup` diamond. Every other differential file in this project made the
same choice for the same reason.
-/

open MvPolynomial

namespace Wu

variable (R : Type*) [CommRing R] (σ : Type*)

/-- **The differential polynomial ring** `R{y_σ}` in one derivation: polynomials in the
indeterminates `y_i^(k)`, one for each unknown `i : σ` and each order `k : ℕ`. -/
abbrev DiffPolynomial : Type _ := MvPolynomial (σ × ℕ) R

namespace DiffPolynomial

variable {R σ}

/-- `Y i k` is `y_i^(k)`, the `k`-th derivative of the `i`-th unknown. -/
noncomputable def Y (i : σ) (k : ℕ) : DiffPolynomial R σ := X (i, k)

variable (R σ) in
/-- **The derivation**, determined by `y_i^(k) ↦ y_i^(k+1)`. -/
noncomputable def deriv : Derivation R (DiffPolynomial R σ) (DiffPolynomial R σ) :=
  mkDerivation R fun p => X (p.1, p.2 + 1)

@[simp] theorem deriv_Y (i : σ) (k : ℕ) : deriv R σ (Y i k) = Y i (k + 1) :=
  mkDerivation_X _ _ _

@[simp] theorem deriv_X (p : σ × ℕ) : deriv R σ (X p) = X (p.1, p.2 + 1) :=
  mkDerivation_X _ _ _

/-! ### The universal property

`R{y}` is free: to give a differential `R`-algebra map out of it is exactly to give the
images of the `y_i`. The `k`-th derivative then has nowhere to go but `d^k` of that image,
which is what `evalDiff` records, and the content is that the resulting map really does
commute with the derivations. -/

section Universal

variable {A : Type*} [CommRing A] [Algebra R A] (dA : Derivation R A A) (f : σ → A)

/-- The evaluation determined by `y_i ↦ f i`: the only possible choice, since `y_i^(k)` must
go to `d^k (f i)`. -/
noncomputable def evalDiff : DiffPolynomial R σ →ₐ[R] A :=
  aeval fun p => (dA : A → A)^[p.2] (f p.1)

@[simp] theorem evalDiff_Y (i : σ) (k : ℕ) :
    evalDiff dA f (Y i k) = (dA : A → A)^[k] (f i) := by
  simp [evalDiff, Y]

/-- **`evalDiff` is a differential homomorphism.**

This is the whole content of the universal property: the map defined by "send `y^(k)` to
`d^k` of the image" automatically intertwines the two derivations. Proved by induction over
the polynomial — constants die on both sides, sums are additive, and the product case is
Leibniz applied twice. -/
theorem evalDiff_deriv (p : DiffPolynomial R σ) :
    evalDiff dA f (deriv R σ p) = dA (evalDiff dA f p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [evalDiff]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
      rw [Derivation.leibniz, map_add, map_mul, deriv_X, Derivation.leibniz]
      simp only [smul_eq_mul, map_mul, evalDiff]
      simp [Function.iterate_succ_apply']
      ring

/-- **Uniqueness.** Any `R`-algebra map that intertwines the derivations and agrees with `f`
on the `y_i` is `evalDiff`. Together with `evalDiff_deriv` this pins `R{y}` down. -/
theorem evalDiff_unique (g : DiffPolynomial R σ →ₐ[R] A)
    (hg : ∀ p, g (deriv R σ p) = dA (g p)) (hf : ∀ i, g (Y i 0) = f i) :
    g = evalDiff dA f := by
  refine MvPolynomial.algHom_ext fun p => ?_
  obtain ⟨i, k⟩ := p
  have key : ∀ k : ℕ, g (Y i k) = (dA : A → A)^[k] (f i) := by
    intro k
    induction k with
    | zero => simpa using hf i
    | succ k ih => rw [← deriv_Y, hg, ih, Function.iterate_succ_apply']
  rw [show (X (i, k) : DiffPolynomial R σ) = Y i k from rfl, key k, evalDiff_Y]

end Universal

end DiffPolynomial

end Wu
