/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuDifferential.Basic
import WuGeometry.Bench

/-!
# Differential benchmark

The differential counterpart of `WuGeometry/Benchmark.lean`, using the same `#wu_bench`
harness: each entry is a real theorem, elaborated and timed, so a broken row breaks the
build rather than being silently dropped.

Timings here include the prolongation `have`s, which is the honest cost of the current
workflow: those are the steps `wu_diff` will absorb.
-/

open scoped Differential

namespace WuDiff

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [Differential R]

/-! ### Order reduction -/

#wu_bench theorem bench_exp_third (y : R) (h : y′ = y) : ((y′)′)′ = y := by
  have h₁ : (y′)′ = y′ := Wu.deriv_congr h
  have h₂ : ((y′)′)′ = (y′)′ := Wu.deriv_congr h₁
  wu

#wu_bench theorem bench_airy_like (y x : R) (hx : x′ = 1) (h : (y′)′ = x * y) :
    ((y′)′)′ = y + x * y′ := by
  have h' : ((y′)′)′ = x * y′ + y * x′ := by rw [Wu.deriv_congr h, deriv_mul]
  wu (vars := [x, y, x′, y′, (y′)′, ((y′)′)′])

/-! ### Conserved quantities -/

#wu_bench theorem bench_kepler_angular (x y vx vy : R)
    (h₁ : x′ = vx) (h₂ : y′ = vy) (h₃ : vx′ = -x) (h₄ : vy′ = -y) :
    (x * vy - y * vx)′ = 0 := by
  have hL : (x * vy - y * vx)′ = x * vy′ + vy * x′ - (y * vx′ + vx * y′) := by
    rw [map_sub, deriv_mul, deriv_mul]
  wu (vars := [x, y, vx, vy, x′, y′, vx′, vy′, (x * vy - y * vx)′])

#wu_bench theorem bench_sir_conserved (S I Rc β γ : R) (hβ : β′ = 0) (hγ : γ′ = 0)
    (hS : S′ = -(β * S * I)) (hI : I′ = β * S * I - γ * I) (hR : Rc′ = γ * I) :
    (S + I + Rc)′ = 0 := by
  have hL : (S + I + Rc)′ = S′ + I′ + Rc′ := by rw [map_add, map_add]
  wu (vars := [β, γ, S, I, Rc, S′, I′, Rc′, (S + I + Rc)′])

/-! ### Differential geometry -/

#wu_bench theorem bench_frenet_plane (T₁ T₂ κ : R) (hκ : κ′ = 0)
    (h₁ : T₁′ = -(κ * T₂)) (h₂ : T₂′ = κ * T₁) :
    (T₁ * T₁ + T₂ * T₂)′ = 0 := by
  have hL : (T₁ * T₁ + T₂ * T₂)′ = 2 * T₁ * T₁′ + 2 * T₂ * T₂′ := by
    rw [map_add, deriv_sq, deriv_sq]
  wu (vars := [κ, T₁, T₂, T₁′, T₂′, (T₁ * T₁ + T₂ * T₂)′])

/-! ### Elimination -/

#wu_bench theorem bench_lotka_volterra (x y α β γ δ : R)
    (hx0 : x ≠ 0) (hβ0 : β ≠ 0) (hy0 : x * α - x′ ≠ 0)
    (hα : α′ = 0) (hβ : β′ = 0) (hγ : γ′ = 0) (hδ : δ′ = 0)
    (hx : x′ = x * (α - β * y)) (hy : y′ = y * (δ * x - γ)) :
    x * (x′)′ - x′ * x′ + x * (α * x - x′) * (δ * x - γ) = 0 := by
  have hx' : (x′)′ = x′ * (α - β * y) - x * (β * y′) := by
    rw [Wu.deriv_congr hx, deriv_mul, map_sub, deriv_mul, hα, hβ]
    ring
  wu

/-! ### Not proved, and why

**Gauss–Codazzi.** Two derivations (the surface parameters `u`, `v`), so critical pairs
and coherence enter. Out of reach until `DiffAtom` carries a multi-index and the engine
computes Δ-polynomials. See the discussion in `WuDifferential/Theorems.lean`.

**Non-identifiability.** Showing a model is *not* structurally identifiable requires the
input–output relations to be *complete*, which is a non-membership claim and the one thing
certificates cannot deliver. `bench_lotka_volterra` proves a relation holds; it does not
prove it is the only one.

**Invariants that are not polynomial.** The Lotka–Volterra first integral
`δx - γ log x + βy - α log y` involves logarithms and so is not a differential polynomial
at all; no amount of engine work reaches it.
-/

end WuDiff
