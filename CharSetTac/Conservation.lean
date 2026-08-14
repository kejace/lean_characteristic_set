/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Variational

/-!
# Evolution equations and conservation laws

`CharSetTac/Variational.lean` builds `E` and `Functionals = ℚ{y}/im D`. This file puts them to
work on named PDEs: KdV, Burgers, the heat equation.

## The trick that makes one derivation enough

An evolution equation `y_t = Q` looks like it needs a second derivation `D_t`. It does not.
The standard move is to keep one derivation `D = D_x` in the ring and realise time evolution
as the **evolutionary vector field** `v_Q` — the unique derivation with

```
  v_Q (y^(k)) = D^k Q
```

which commutes with `D` by construction (`lie_evo_deriv`). "`∂/∂t`" *is* `v_Q`. The equation
is not an element of the ring; it is the choice of `Q`. So KdV, Burgers, mKdV and the heat
equation all live in `ℚ{y}` with a single derivation. (KP genuinely needs two spatial
variables and is out of reach — see `SCOPE.md` §2.1.)

## Conservation laws

`ρ` is a **conserved density** for `Q` when `v_Q ρ` is a total derivative; the witness is the
**flux**. Physically: `∂_t ρ + ∂_x(−σ) = 0`, so `∫ρ` is constant in time.

The right home for this is `Functionals`: `ρ` is conserved exactly when the class of `v_Q ρ`
vanishes there (`isConservedDensity_iff`), and two densities differing by a total derivative
are the same conservation law. That is the payoff from `E ∘ D = 0` — the quotient is
well-defined and `E` descends to it.

Note what is *not* claimed. The textbook criterion "ρ is conserved iff `E(v_Q ρ) = 0`" is the
converse to `E ∘ D = 0`, and over a base of constants that converse is **false** (`E(1) = 0`
while `1 ∉ im D` — `Wu.Variational.range_deriv_lt_ker_E`). So the fluxes below are exhibited
explicitly rather than inferred from `E`.
-/

open MvPolynomial

namespace Wu.Conservation

open Wu.Variational (P Dtot Functionals)

/-- `y[k]` is `y^(k)`. -/
local notation "y[" k "]" => Wu.DiffPolynomial.Y (() : Unit) k

/-! ### Evolutionary vector fields -/

/-- **The evolutionary vector field with characteristic `Q`**: the unique derivation sending
`y^(k)` to `D^k Q`. This is `∂/∂t` for the evolution equation `y_t = Q`. -/
noncomputable def evo (Q : P) : Derivation ℚ P P :=
  mkDerivation ℚ fun p => (Dtot : P → P)^[p.2] Q

@[simp] theorem evo_X (Q : P) (p : Unit × ℕ) :
    evo Q (X p) = (Dtot : P → P)^[p.2] Q :=
  mkDerivation_X _ _ _

@[simp] theorem evo_Y (Q : P) (k : ℕ) : evo Q y[k] = (Dtot : P → P)^[k] Q :=
  mkDerivation_X _ _ _

/-- **`⁅v_Q, D⁆ = 0`** — time evolution commutes with the space derivative, by construction
rather than by hypothesis. This is exactly why one derivation suffices to express an
evolution equation, and it is what makes `v_Q` descend to functionals. -/
theorem lie_evo_deriv (Q : P) : ⁅evo Q, Dtot⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  rintro ⟨u, k⟩
  rw [Derivation.commutator_apply, Wu.DiffPolynomial.deriv_X, evo_X, evo_X]
  dsimp only
  rw [Function.iterate_succ_apply' (f := (Dtot : P → P))]
  simp

/-! ### Conservation laws -/

/-- **`ρ` is a conserved density for `Q`**: its evolution is a total derivative. The witness
`σ` is the flux, and `∂_t ρ = ∂_x σ` is the conservation law in the usual form. -/
def IsConservedDensity (Q ρ : P) : Prop := ∃ σ : P, evo Q ρ = Dtot σ

/-- **A conservation law is a statement about functionals.** `ρ` is conserved exactly when the
class of `v_Q ρ` dies in `ℚ{y}/im D` — so two densities differing by a total derivative give
the same conservation law, which is the standard equivalence. -/
theorem isConservedDensity_iff (Q ρ : P) :
    IsConservedDensity Q ρ ↔
      Submodule.Quotient.mk (evo Q ρ) = (0 : Functionals) := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨fun ⟨σ, hσ⟩ => ⟨σ, hσ.symm⟩, fun ⟨σ, hσ⟩ => ⟨σ, hσ.symm⟩⟩

/-- Total derivatives are trivially conserved, for any evolution. The content of a
conservation law is always modulo these. -/
theorem isConservedDensity_deriv (Q ρ : P) : IsConservedDensity Q (Dtot ρ) := by
  refine ⟨evo Q ρ, ?_⟩
  have h := Derivation.congr_fun (lie_evo_deriv Q) ρ
  rw [Derivation.commutator_apply] at h
  simpa [sub_eq_zero] using h

/-! ### The heat equation, `y_t = y''` -/

/-- `y` is conserved for the heat equation, with flux `y'`. -/
example : IsConservedDensity y[2] y[0] := ⟨y[1], by simp⟩

/-! ### Burgers, `y_t = y'' + y y'` -/

/-- Burgers' equation as a characteristic. -/
noncomputable def burgers : P := y[2] + y[0] * y[1]

/-- `y` is conserved for Burgers, with flux `y' + y²/2`. The nonlinear term integrates
because `y y' = D(y²/2)` — the null Lagrangian of `Variational.lean` reappearing as a flux. -/
theorem conserved_burgers : IsConservedDensity burgers y[0] := by
  have h2 : (C (2⁻¹ : ℚ) : P) * 2 = 1 := by
    rw [show (2 : P) = C (2 : ℚ) from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  refine ⟨y[1] + C (2⁻¹ : ℚ) * y[0] ^ 2, ?_⟩
  simp [burgers, Wu.DiffPolynomial.Y, Derivation.leibniz, Derivation.leibniz_pow,
    ← mul_assoc, h2]

/-! ### KdV, `y_t = 6 y y' − y'''`

The two lowest conservation laws, with their fluxes written out. These are the start of the
infinite hierarchy that makes KdV integrable. -/

/-- The KdV characteristic. -/
noncomputable def kdv : P := 6 * (y[0] * y[1]) - y[3]

/-- **First KdV conservation law**: `ρ = y`, flux `3y² − y''`. This is conservation of mass. -/
theorem conserved_kdv_one : IsConservedDensity kdv y[0] := by
  refine ⟨3 * y[0] ^ 2 - y[2], ?_⟩
  simp [kdv, Wu.DiffPolynomial.Y, Derivation.leibniz, Derivation.leibniz_pow]
  ring

/-- **Second KdV conservation law**: `ρ = y²`, flux `4y³ − 2y·y'' + (y')²`.

This one is not obvious. The evolution is `2y(6yy' − y''')  =  12y²y' − 2y·y'''`, and the
`y·y'''` term only integrates after producing and cancelling a `y'y''`:
`D(−2y·y'') = −2y'y'' − 2y·y'''` and `D((y')²) = 2y'y''`. -/
theorem conserved_kdv_two : IsConservedDensity kdv (y[0] ^ 2) := by
  refine ⟨4 * y[0] ^ 3 - 2 * (y[0] * y[2]) + y[1] ^ 2, ?_⟩
  simp [kdv, Wu.DiffPolynomial.Y, Derivation.leibniz, Derivation.leibniz_pow]
  ring

/-- **Third KdV conservation law**: `ρ = 2y³ + (y')²`, with flux

```
  9y⁴ − 2y'y''' + (y'')² − 6y²y'' + 12y(y')²
```

This is the energy, and it is where the hierarchy stops being guessable. Its evolution is

```
  36y³y' − 6y²y''' + 12(y')³ + 12y·y'y'' − 2y'y⁗
```

and each term needs a different integration: `−2y'y⁗ = D(−2y'y''' + (y'')²)`,
`−6y²y''' = D(−6y²y'') + 12y·y'y''`, and the `12(y')³ + 24y·y'y''` left over is
`D(12y(y')²)`. That an infinite sequence of these exists is what integrability means. -/
theorem conserved_kdv_three : IsConservedDensity kdv (2 * y[0] ^ 3 + y[1] ^ 2) := by
  refine ⟨9 * y[0] ^ 4 - 2 * (y[1] * y[3]) + y[2] ^ 2 - 6 * (y[0] ^ 2 * y[2])
    + 12 * (y[0] * y[1] ^ 2), ?_⟩
  simp [kdv, Wu.DiffPolynomial.Y, Derivation.leibniz, Derivation.leibniz_pow]
  ring

/-! ### Conservation laws form a space

Which is what makes "the space of conservation laws of `Q`" — a subspace of `Functionals` —
the right object, and the reason the hierarchy above is a sequence of independent elements
rather than a list of coincidences. -/

theorem IsConservedDensity.add {Q ρ₁ ρ₂ : P} (h₁ : IsConservedDensity Q ρ₁)
    (h₂ : IsConservedDensity Q ρ₂) : IsConservedDensity Q (ρ₁ + ρ₂) := by
  obtain ⟨σ₁, hσ₁⟩ := h₁
  obtain ⟨σ₂, hσ₂⟩ := h₂
  exact ⟨σ₁ + σ₂, by rw [map_add, map_add, hσ₁, hσ₂]⟩

theorem IsConservedDensity.smul {Q ρ : P} (c : ℚ) (h : IsConservedDensity Q ρ) :
    IsConservedDensity Q (c • ρ) := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨c • σ, by rw [Derivation.map_smul, Derivation.map_smul, hσ]⟩

/-- Anything in the ℚ-span of `y`, `y²` and `2y³ + (y')²` — modulo total derivatives — is
conserved for KdV. The first three rungs of the hierarchy, closed up. -/
example (a b c : ℚ) (f : P) :
    IsConservedDensity kdv
      (a • y[0] + b • y[0] ^ 2 + c • (2 * y[0] ^ 3 + y[1] ^ 2) + Dtot f) :=
  ((conserved_kdv_one.smul a).add (conserved_kdv_two.smul b)
    |>.add (conserved_kdv_three.smul c)).add (isConservedDensity_deriv kdv f)

end Wu.Conservation
