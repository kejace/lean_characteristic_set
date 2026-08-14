/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuDifferential.PDE

/-!
# The PDE examples without `wu`

Counterparts to `WuDifferential/PDE.lean`.

Same verdict as elsewhere: once the prolongations are written out these close by
substitution, and the value of the tactic is in *finding* the combination rather than in
shortening it. `zero_curvature` is the one where the hand proof stops being obvious — the
cancellation between the `[U,V]` terms is exactly what the elimination discovers.

Note again the asymmetry in nondegeneracy. `wu` needs `A ≠ 0` for `schwarzschild_AB_const`
and `r ≠ 0` for `schwarzschild_potential`; the hand proofs need neither. In this case the
conditions happen to be physically meaningful anyway — the horizon and the origin — but
they are still artefacts of pseudo-division rather than of the mathematics.
-/

namespace WuPDE.ByHand

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- Compare: `WuPDE.frobenius`. -/
theorem frobenius (d₁ d₂ : Derivation ℤ R R) (u a b : R)
    (comm : d₁ (d₂ u) = d₂ (d₁ u)) (h₁ : d₁ u = a) (h₂ : d₂ u = b) :
    d₂ a = d₁ b := by
  rw [← h₁, ← h₂, comm]

/-- Compare: `WuPDE.frobenius_general`. -/
theorem frobenius_general (d₁ d₂ : Derivation ℤ R R) (u a b ay au bx bu : R)
    (comm : d₁ (d₂ u) = d₂ (d₁ u)) (h₁ : d₁ u = a) (h₂ : d₂ u = b)
    (ha : d₂ a = ay + au * b) (hb : d₁ b = bx + bu * a) :
    ay + au * b = bx + bu * a := by
  rw [← ha, ← hb, ← h₁, ← h₂, comm]

/-- Compare: `WuPDE.zero_curvature`.

The one that is genuinely awkward by hand: the `[U,V]` terms have to be seen to cancel
against the substituted first derivatives. -/
theorem zero_curvature (d₁ d₂ : Derivation ℤ R R)
    (ψ₁ ψ₂ u₁₁ u₁₂ u₂₁ u₂₂ v₁₁ v₁₂ v₂₁ v₂₂ : R)
    (comm : d₂ (d₁ ψ₁) = d₁ (d₂ ψ₁))
    (hx₁ : d₁ ψ₁ = u₁₁ * ψ₁ + u₁₂ * ψ₂) (hx₂ : d₁ ψ₂ = u₂₁ * ψ₁ + u₂₂ * ψ₂)
    (hy₁ : d₂ ψ₁ = v₁₁ * ψ₁ + v₁₂ * ψ₂) (hy₂ : d₂ ψ₂ = v₂₁ * ψ₁ + v₂₂ * ψ₂)
    (p₁ : d₂ (u₁₁ * ψ₁ + u₁₂ * ψ₂)
        = d₂ u₁₁ * ψ₁ + u₁₁ * d₂ ψ₁ + d₂ u₁₂ * ψ₂ + u₁₂ * d₂ ψ₂)
    (p₂ : d₁ (v₁₁ * ψ₁ + v₁₂ * ψ₂)
        = d₁ v₁₁ * ψ₁ + v₁₁ * d₁ ψ₁ + d₁ v₁₂ * ψ₂ + v₁₂ * d₁ ψ₂) :
    (d₂ u₁₁ - d₁ v₁₁ + u₁₂ * v₂₁ - v₁₂ * u₂₁) * ψ₁
      + (d₂ u₁₂ - d₁ v₁₂ + u₁₁ * v₁₂ + u₁₂ * v₂₂ - v₁₁ * u₁₂ - v₁₂ * u₂₂) * ψ₂ = 0 := by
  have e₁ : d₂ (d₁ ψ₁) = d₂ (u₁₁ * ψ₁ + u₁₂ * ψ₂) := by rw [hx₁]
  have e₂ : d₁ (d₂ ψ₁) = d₁ (v₁₁ * ψ₁ + v₁₂ * ψ₂) := by rw [hy₁]
  -- G = (comm - e₁ + e₂ - p₁ + p₂) with the first derivatives substituted out
  linear_combination comm - e₁ + e₂ - p₁ + p₂
    - u₁₁ * hy₁ - u₁₂ * hy₂ + v₁₁ * hx₁ + v₁₂ * hx₂

/-- Compare: `WuPDE.codazzi_eliminate`. -/
theorem codazzi_eliminate (d₁ d₂ : Derivation ℤ R R) (E G L N : R)
    (cod₁ : 2 * E * G * d₂ L = d₂ E * (G * L + E * N))
    (cod₂ : 2 * E * G * d₁ N = d₁ G * (G * L + E * N)) :
    d₁ G * (2 * E * G * d₂ L) = d₂ E * (2 * E * G * d₁ N) := by
  linear_combination d₁ G * cod₁ - d₂ E * cod₂

/-- Compare: `WuPDE.schwarzschild_AB_const`. Needs no `A ≠ 0`. -/
theorem schwarzschild_AB_const (d : Derivation ℤ R R) (A B : R)
    (vac : B * d A + A * d B = 0) (leib : d (A * B) = A * d B + B * d A) :
    d (A * B) = 0 := by
  rw [leib]; linear_combination vac

/-- Compare: `WuPDE.schwarzschild_potential`. Needs no `r ≠ 0`. -/
theorem schwarzschild_potential (d : Derivation ℤ R R) (A B r : R)
    (hnorm : A * B = 1) (hr : r * d A + A - 1 = 0) :
    r * d A = 1 - A := by
  linear_combination hr

end WuPDE.ByHand
