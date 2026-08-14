/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuDifferential.Basic

/-!
# The same theorems without `wu`

Every theorem of `WuDifferential/Theorems.lean`, proved by hand. Read side by side to see
what the tactic is and is not buying.

## What the comparison shows

For these systems, **`wu` is not buying brevity**. Once the prolongation is written out,
most of these close with `rw [...]; ring` — the differential systems here are small, and
substitution does the job.

What `wu` buys is that it **finds** the combination. The hand proofs below each encode a
specific elimination order that a human chose: which hypothesis to substitute into which,
and in what sequence. For `lotka_volterra_io` that sequence is not obvious, and for a
system with more state variables it stops being findable by inspection at all. That is the
real claim — not shorter proofs, but not having to know the answer first.

## Where the hand proof is genuinely better

`unit_speed_profile` is the honest counterexample, and it is instructive.
`wu` needs `g′ ≠ 0` there; the hand proof needs no such thing. The tactic's condition is an
artefact of pseudo-division having to divide by *some* initial, and a human sees
immediately that dividing by `2` suffices. Worth knowing that the nondegeneracy conditions
`wu` reports are the ones *its method* needs, which can be strictly stronger than the ones
the theorem needs.
-/

open scoped Differential

namespace WuDiff.ByHand

/-- Differentiating an equation. Stated locally rather than imported from `Wu`, so that
nothing in this file depends on the tactic's library. -/
private theorem dcongr {R : Type*} [CommRing R] [Differential R] {a b : R} (h : a = b) :
    a′ = b′ := by rw [h]

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [Differential R]

/-! ### Elementary ODE consequences -/

/-- Compare: `WuDiff.exp_second`. -/
theorem exp_second (y : R) (h : y′ = y) : (y′)′ = y := by
  have h' : (y′)′ = y′ := dcongr h
  exact h'.trans h

/-- Compare: `WuDiff.sq_second`. -/
theorem sq_second (y : R) (h : y′ = y ^ 2) : (y′)′ = 2 * y ^ 3 := by
  have h' : (y′)′ = 2 * y * y′ := by
    rw [dcongr h, pow_two, deriv_mul]; ring
  rw [h', h]; ring

/-- Compare: `WuDiff.logistic_second`. -/
theorem logistic_second (y : R) (h : y′ = y * (1 - y)) :
    (y′)′ = y * (1 - y) * (1 - 2 * y) := by
  have h' : (y′)′ = y′ - 2 * y * y′ := by
    rw [dcongr h]
    simp only [mul_sub, mul_one, map_sub, deriv_mul]
    ring
  rw [h', h]; ring

/-! ### Conserved quantities -/

/-- Compare: `WuDiff.harmonic_energy`. -/
theorem harmonic_energy (u v : R) (h₁ : u′ = v) (h₂ : v′ = -u) :
    (u * u + v * v)′ = 0 := by
  have hL : (u * u + v * v)′ = 2 * u * u′ + 2 * v * v′ := by
    rw [map_add, deriv_sq, deriv_sq]
  rw [hL, h₁, h₂]; ring

/-- Compare: `WuDiff.sir_population`. -/
theorem sir_population (S I Rc β γ : R) (hβ : β′ = 0) (hγ : γ′ = 0)
    (hS : S′ = -(β * S * I)) (hI : I′ = β * S * I - γ * I) (hR : Rc′ = γ * I) :
    (S + I + Rc)′ = 0 := by
  have hL : (S + I + Rc)′ = S′ + I′ + Rc′ := by rw [map_add, map_add]
  rw [hL, hS, hI, hR]; ring

/-! ### Differential geometry: curves -/

/-- Compare: `WuDiff.frenet_plane_unit`. -/
theorem frenet_plane_unit (T₁ T₂ κ : R) (hκ : κ′ = 0)
    (h₁ : T₁′ = -(κ * T₂)) (h₂ : T₂′ = κ * T₁) :
    (T₁ * T₁ + T₂ * T₂)′ = 0 := by
  have hL : (T₁ * T₁ + T₂ * T₂)′ = 2 * T₁ * T₁′ + 2 * T₂ * T₂′ := by
    rw [map_add, deriv_sq, deriv_sq]
  rw [hL, h₁, h₂]; ring

/-- Compare: `WuDiff.frenet_space_orthogonal`. -/
theorem frenet_space_orthogonal (a b d e κ τ : R)
    (ha : a = 1) (hb : b = 1) (he : e = 0)
    (hd : d′ = κ * b - κ * a + τ * e) :
    d′ = 0 := by
  rw [hd, ha, hb, he]; ring

/-- Compare: `WuDiff.unit_speed_profile`.

**This one is strictly better than the `wu` proof.** `wu` requires `g′ ≠ 0`; this does not.
Dividing by the constant `2` is enough, and a human sees that immediately, whereas
pseudo-division reaches for the initial of the main variable. -/
theorem unit_speed_profile (f g : R) (h : f′ * f′ + g′ * g′ = 1) :
    f′ * (f′)′ + g′ * (g′)′ = 0 := by
  have hL : (f′ * f′ + g′ * g′)′ = 2 * f′ * (f′)′ + 2 * g′ * (g′)′ := by
    rw [map_add, deriv_sq, deriv_sq]
  have h0 : (f′ * f′ + g′ * g′)′ = 0 := by rw [h]; simp
  have key : (2 : R) * (f′ * (f′)′ + g′ * (g′)′) = 0 := by
    rw [← h0, hL]; ring
  exact (mul_eq_zero.mp key).resolve_left two_ne_zero

/-! ### Elimination -/

/-- Compare: `WuDiff.lotka_volterra_io`.

This is where the tactic earns its place. The hand proof needs the substitution order
`x″ → y′ → x′` to be chosen correctly; get it wrong and `ring` will not close. Note also
that the hand proof needs *none* of the nondegeneracy hypotheses `wu` reports — those are
what its elimination needs to divide by, not what the identity needs. -/
theorem lotka_volterra_io (x y α β γ δ : R)
    (hα : α′ = 0) (hβ : β′ = 0) (hγ : γ′ = 0) (hδ : δ′ = 0)
    (hx : x′ = x * (α - β * y)) (hy : y′ = y * (δ * x - γ)) :
    x * (x′)′ - x′ * x′ + x * (α * x - x′) * (δ * x - γ) = 0 := by
  have hx' : (x′)′ = x′ * (α - β * y) - x * (β * y′) := by
    rw [dcongr hx, deriv_mul, map_sub, deriv_mul, hα, hβ]
    ring
  rw [hx', hy, hx]; ring

end WuDiff.ByHand
