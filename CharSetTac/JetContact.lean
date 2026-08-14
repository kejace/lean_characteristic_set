/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DerivationOfNat
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# The jet ring with an independent variable, and the contact structure

## The gap this fills

`Wu.DiffPolynomial` is `R{y}` with `D y^(k) = y^(k+1)`, built by `MvPolynomial.mkDerivation`,
which produces an `R`-*linear* derivation. So `D` annihilates `R`: our `R{y}` is a
differential algebra over its ring of **constants**. Kolchin's `R{Y}` is over a differential
ring, whose derivation is extended.

That is not a cosmetic difference. It means there is no element `x` with `D x = 1` — no
independent variable — and without one you cannot write an explicitly `x`-dependent
Lagrangian, and you cannot write a contact form `dy^(k) − y^(k+1) dx` at all, because the
`dx` has nothing to refer to.

Mathlib has no jet spaces, no contact structures and no variational calculus (checked: zero
files for each), so there is nothing to import. This file therefore just *defines* what is
needed: one extra indeterminate, and a total derivative that sends it to `1`.

## The contact structure

On the infinite jet space, a 1-form is **contact** if it vanishes on holonomic sections —
those coming from an actual function `y(x)`. The contact forms are spanned by

```
  θ_{i,k} = dy_i^(k) − y_i^(k+1) dx
```

and the point of the whole apparatus is `dd_eq_Dtot_mod_contact` below:

**modulo contact forms, the exterior derivative is the total derivative.**

```
  df ≡ (D f) dx      (mod contact)
```

That single congruence is what "total derivative" *means* geometrically, and it is the
horizontal edge of the variational bicomplex — `d_H`. It is proved here with no manifolds,
no sections and no sums: both sides are derivations into the quotient module, so they need
only be compared on the generators, where the difference is a contact form by definition.

## Forms, concretely

Rather than fight `Ω[·⁄·]`, 1-forms are taken in the basis presentation
`JetVar σ →₀ JetPoly R σ`, i.e. formal combinations of `dx` and the `dy_i^(k)`. That is not a
shortcut: `KaehlerDifferential.mvPolynomialEquiv` says this module *is* `Ω[R[σ]⁄R]`, and
`dd` below is the same `mkDerivation` that the equivalence is built from.
-/

open MvPolynomial

namespace Wu

/-- **Coordinates on the infinite jet space** of maps `x ↦ (y_i)`: the independent variable,
and one indeterminate for each unknown and each order. -/
inductive JetVar (σ : Type*) where
  /-- The independent variable `x`. -/
  | base : JetVar σ
  /-- `y_i^(k)`. -/
  | jet (i : σ) (k : ℕ) : JetVar σ

/-- **The jet ring** `R[x, y_i^(k)]`. Unlike `Wu.DiffPolynomial`, this one contains its own
independent variable. -/
abbrev JetPoly (R : Type*) [CommRing R] (σ : Type*) : Type _ := MvPolynomial (JetVar σ) R

namespace JetPoly

variable (R : Type*) [CommRing R] (σ : Type*)

/-- The independent variable. -/
noncomputable def xx : JetPoly R σ := X .base

/-- `y_i^(k)`. -/
noncomputable def yy (i : σ) (k : ℕ) : JetPoly R σ := X (.jet i k)

/-- **The total derivative** `D`, determined by `D x = 1` and `D y^(k) = y^(k+1)`.

The `D x = 1` clause is the whole difference from `Wu.DiffPolynomial.deriv`, and it is what
makes `x` an independent variable rather than a constant. -/
noncomputable def Dtot : Derivation R (JetPoly R σ) (JetPoly R σ) :=
  mkDerivation R fun
    | .base => 1
    | .jet i k => X (.jet i (k + 1))

variable {R σ}

@[simp] theorem Dtot_X_base : Dtot R σ (X (JetVar.base : JetVar σ)) = 1 :=
  mkDerivation_X _ _ _

@[simp] theorem Dtot_X_jet (i : σ) (k : ℕ) :
    Dtot R σ (X (JetVar.jet i k)) = X (JetVar.jet i (k + 1)) :=
  mkDerivation_X _ _ _

@[simp] theorem Dtot_xx : Dtot R σ (xx R σ) = 1 := mkDerivation_X _ _ _

@[simp] theorem Dtot_yy (i : σ) (k : ℕ) : Dtot R σ (yy R σ i k) = yy R σ i (k + 1) :=
  mkDerivation_X _ _ _

/-- The independent variable is genuinely not a constant — contrast
`Wu.DiffPolynomial`, where the derivation annihilates the whole base ring. -/
theorem Dtot_xx_ne_zero [Nontrivial R] : Dtot R σ (xx R σ) ≠ 0 := by
  rw [Dtot_xx]; exact one_ne_zero

/-! ### 1-forms -/

variable (R σ)

/-- **1-forms** on the jet ring, in the basis `{dx} ∪ {dy_i^(k)}`.

This is `Ω[JetPoly R σ⁄R]` in its basis presentation — see
`KaehlerDifferential.mvPolynomialEquiv`. -/
abbrev Form : Type _ := JetVar σ →₀ JetPoly R σ

/-- `dv` for a coordinate `v`. -/
noncomputable def dCoord (v : JetVar σ) : Form R σ := Finsupp.single v 1

/-- **The exterior derivative** on functions, `f ↦ Σ_v (∂f/∂v) dv`, as a derivation. -/
noncomputable def dd : Derivation R (JetPoly R σ) (Form R σ) :=
  mkDerivation R fun v => dCoord R σ v

variable {R σ}

@[simp] theorem dd_X (v : JetVar σ) : dd R σ (X v) = dCoord R σ v := mkDerivation_X _ _ _

/-! ### Contact forms -/

variable (R σ)

/-- **The contact form** `θ_{i,k} = dy_i^(k) − y_i^(k+1) dx`.

It vanishes precisely on holonomic sections: along an actual function `y(x)` one has
`dy^(k) = y^(k+1) dx`, which is the chain rule. -/
noncomputable def theta (i : σ) (k : ℕ) : Form R σ :=
  dCoord R σ (.jet i k) - yy R σ i (k + 1) • dCoord R σ .base

/-- **The contact submodule**, spanned by all the `θ_{i,k}`. This is the algebraic form of the
Cartan distribution. -/
noncomputable def contactSubmodule : Submodule (JetPoly R σ) (Form R σ) :=
  Submodule.span _ (Set.range fun p : σ × ℕ => theta R σ p.1 p.2)

theorem theta_mem_contact (i : σ) (k : ℕ) : theta R σ i k ∈ contactSubmodule R σ :=
  Submodule.subset_span ⟨(i, k), rfl⟩

/-! ### The theorem

Modulo contact forms, `d` is `D · dx`. Both sides are derivations into the quotient, so they
are compared on generators only. -/

/-- `d`, pushed into the quotient by the contact submodule. -/
noncomputable def ddQuot :
    Derivation R (JetPoly R σ) (Form R σ ⧸ contactSubmodule R σ) :=
  (contactSubmodule R σ).mkQ.compDer (dd R σ)

/-- `f ↦ (D f) dx`, pushed into the same quotient. A derivation because `D` is one and
multiplying a fixed form by a scalar is linear. -/
noncomputable def DtotQuot :
    Derivation R (JetPoly R σ) (Form R σ ⧸ contactSubmodule R σ) :=
  (LinearMap.toSpanSingleton (JetPoly R σ) _
    ((contactSubmodule R σ).mkQ (dCoord R σ .base))).compDer (Dtot R σ)

/-- **Modulo contact forms, the exterior derivative is the total derivative.**

On generators: at `x` both sides are `dx`, since `D x = 1`. At `y^(k)` the left side is
`dy^(k)` and the right is `y^(k+1) dx`, and their difference is exactly `θ_{i,k}` — which is
zero in the quotient by fiat. Everything else follows because both sides are derivations.

This is the horizontal differential `d_H` of the variational bicomplex, and it is the precise
sense in which `D` deserves the name "total derivative". -/
theorem ddQuot_eq_DtotQuot : ddQuot R σ = DtotQuot R σ := by
  apply MvPolynomial.derivation_ext
  rintro (_ | ⟨i, k⟩)
  · change (contactSubmodule R σ).mkQ (dd R σ (X JetVar.base))
        = Dtot R σ (X JetVar.base) • (contactSubmodule R σ).mkQ (dCoord R σ .base)
    rw [dd_X, Dtot_X_base, one_smul]
  · change (contactSubmodule R σ).mkQ (dd R σ (X (JetVar.jet i k)))
        = Dtot R σ (X (JetVar.jet i k)) • (contactSubmodule R σ).mkQ (dCoord R σ .base)
    rw [dd_X, Dtot_X_jet, Submodule.mkQ_apply, Submodule.mkQ_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    simpa [theta, yy] using theta_mem_contact R σ i k

/-- The same statement without the quotient: `df − (Df) dx` is a contact form. -/
theorem dd_sub_Dtot_smul_mem_contact (f : JetPoly R σ) :
    dd R σ f - Dtot R σ f • dCoord R σ .base ∈ contactSubmodule R σ := by
  have h := Derivation.congr_fun (ddQuot_eq_DtotQuot R σ) f
  change (contactSubmodule R σ).mkQ (dd R σ f)
      = Dtot R σ f • (contactSubmodule R σ).mkQ (dCoord R σ .base) at h
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.eq] at h
  exact h

/-! ### What the independent variable buys

Every statement here mentions `x` essentially, and none of them can even be *written* in
`Wu.DiffPolynomial`, where the base ring is annihilated by the derivation. -/

section Examples

/-- The product rule against the independent variable: `D(x·y) = y + x·y'`. In `R{y}` the
left-hand side would collapse, because `x` would be a constant. -/
example : Dtot ℚ Unit (xx ℚ Unit * yy ℚ Unit () 0)
    = yy ℚ Unit () 0 + xx ℚ Unit * yy ℚ Unit () 1 := by
  rw [Derivation.leibniz]
  simp [smul_eq_mul]
  ring

/-- `D(x²) = 2x`. -/
example : Dtot ℚ Unit (xx ℚ Unit ^ 2) = 2 * xx ℚ Unit := by
  rw [Derivation.leibniz_pow]
  simp [smul_eq_mul]

/-- The lowest contact form is `θ₀ = dy − y' dx`, and it is exactly the discrepancy between
the exterior derivative of `y` and its total derivative — the theorem, instantiated. -/
example : dd ℚ Unit (yy ℚ Unit () 0) - Dtot ℚ Unit (yy ℚ Unit () 0) • dCoord ℚ Unit .base
    = theta ℚ Unit () 0 := by
  rw [yy, dd_X, Dtot_X_jet, theta, yy]

end Examples

end JetPoly

end Wu
