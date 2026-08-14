/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DerivationOfNat
import CharSetTac.DiffPolynomial
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie

/-!
# The Euler operator on `ℚ{y}`, and the bottom of the variational complex

The calculus of variations has an algebraic core that lives entirely inside `R{y}`, and this
file formalizes it: the Euler operator (the variational derivative), the commutator identity
that drives it, and the theorem that **total derivatives are variationally trivial**.

## What this is, in context

The *variational bicomplex* is the double complex of differential forms on the infinite jet
space, with a horizontal differential `d_H` (total derivative) and a vertical one `d_V`. Its
edge complex — obtained by quotienting rows by horizontally exact forms — is the *variational
complex*, and the bottom of that complex is

```
  R{y} --D--> R{y} --E--> (Euler–Lagrange expressions)
```

where `D` is the total derivative and `E` the Euler operator. The statement `E ∘ D = 0` is
exactly "this is a complex at that spot", and it is the theorem proved below
(`E_deriv`). Everything here is the `0`-form corner of the bicomplex: no differential forms
are involved, which is precisely why it is reachable from a differential polynomial ring.

## The identity that does the work

```
  ⁅∂/∂y^(k+1), D⁆ = ∂/∂y^(k)        and        ⁅∂/∂y^(0), D⁆ = 0
```

The partial derivatives and the total derivative do not commute; the commutator shifts the
order down by one. That is the whole reason the alternating sum in `E` telescopes, and it is
another Lie-bracket statement in `Der(ℚ{y})`, alongside `⁅E_grading, D⁆ = D` in
`CharSetTac/DiffPolynomialHeavy.lean`.

## The boundary term is kept, not hidden

`E` is an infinite alternating sum, made finite by the fact that a polynomial has finite
order. Rather than hide that, `euler N` is the sum truncated at `N`, and the central
computation is exact:

```
  euler (N+1) (D L) = (-1)^N • D^(N+1) (∂L/∂y^(N))
```

The right-hand side is the boundary term of the integration by parts. It vanishes exactly
when `L` has order below `N`, which is what turns the identity into `E ∘ D = 0`.

## Scope

One unknown and one derivation, over `ℚ` — see `SCOPE.md` for what that rules out. The two
limitations that bite here are that several independent variables would need the `Δ`-indexed
ring, and that there is no independent variable `x` in the ring at all, since `ℚ{y}` is an
algebra over its *constants*. Neither is needed for anything below.
-/

open MvPolynomial

namespace Wu.Variational

/-- `ℚ{y}`, one unknown. -/
abbrev P : Type := Wu.DiffPolynomial ℚ Unit

/-- The total derivative `D`. -/
noncomputable abbrev Dtot : Derivation ℚ P P := Wu.DiffPolynomial.deriv ℚ Unit

/-- `∂/∂y^(k)`, the partial derivative in the `k`-th derivative coordinate. Unlike `D`, this
sees `y^(k)` as just one more indeterminate. -/
noncomputable def pd (k : ℕ) : Derivation ℚ P P := pderiv ((), k)

/-- `y[k]` is `y^(k)`. -/
local notation "y[" k "]" => Wu.DiffPolynomial.Y (() : Unit) k

@[simp] theorem pd_Y (j k : ℕ) : pd j y[k] = if k = j then 1 else 0 := by
  rcases eq_or_ne k j with rfl | h
  · simp [pd, Wu.DiffPolynomial.Y]
  · have hne : (((), k) : Unit × ℕ) ≠ ((), j) := by simp [Prod.ext_iff, h]
    simp [pd, Wu.DiffPolynomial.Y, h, MvPolynomial.pderiv_X_of_ne hne]

/-- A partial derivative of a generator is `0` or `1`, so the total derivative kills it. -/
private theorem deriv_pd_X (j : ℕ) (p : Unit × ℕ) : Dtot (pd j (X p)) = 0 := by
  rcases eq_or_ne p ((), j) with rfl | h
  · simp [pd]
  · simp [pd, MvPolynomial.pderiv_X_of_ne h]

/-- Iterating the total derivative stays additive. `map_add` is about a single application;
the alternating sum below needs it under an iterate. -/
private theorem iterate_deriv_add (n : ℕ) (a b : P) :
    (Dtot : P → P)^[n] (a + b) = (Dtot : P → P)^[n] a + (Dtot : P → P)^[n] b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        map_add, ih]

/-! ### The commutator identity -/

/-- **`⁅∂/∂y^(k+1), D⁆ = ∂/∂y^(k)`.**

Differentiating totally and then taking `∂/∂y^(k+1)` is not the same as doing it the other
way round: the total derivative feeds `y^(k)` into `y^(k+1)`, so the commutator drops the
order by one. This is the identity that makes the Euler operator's alternating sum telescope.

Both sides are derivations, so it suffices to check the generators, where it is
`δ_{m,k} = δ_{m+1,k+1}`. -/
theorem lie_pd_succ_deriv (k : ℕ) : ⁅pd (k + 1), Dtot⁆ = pd k := by
  apply MvPolynomial.derivation_ext
  rintro ⟨u, m⟩
  rw [Derivation.commutator_apply, Wu.DiffPolynomial.deriv_X, deriv_pd_X, sub_zero]
  dsimp only
  rcases eq_or_ne m k with rfl | h
  · simp [pd]
  · have h1 : ((u, m + 1) : Unit × ℕ) ≠ ((), k + 1) := by simp [Prod.ext_iff, h]
    have h2 : ((u, m) : Unit × ℕ) ≠ ((), k) := by simp [Prod.ext_iff, h]
    rw [pd, pd, MvPolynomial.pderiv_X_of_ne h1, MvPolynomial.pderiv_X_of_ne h2]

/-- **`⁅∂/∂y^(0), D⁆ = 0`.** There is no `y^(-1)` for the commutator to land on, so at the
bottom of the tower the two operators do commute. This is the base case of the telescope. -/
theorem lie_pd_zero_deriv : ⁅pd 0, Dtot⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  rintro ⟨u, m⟩
  rw [Derivation.commutator_apply, Wu.DiffPolynomial.deriv_X, deriv_pd_X, sub_zero]
  dsimp only
  have hne : ((u, m + 1) : Unit × ℕ) ≠ ((), 0) := by simp
  rw [pd, MvPolynomial.pderiv_X_of_ne hne]
  simp

/-- The commutator identity, applied: `∂(D L)/∂y^(k+1) = D(∂L/∂y^(k+1)) + ∂L/∂y^(k)`. This is
the "integration by parts" step in coordinates. -/
theorem pd_succ_deriv (k : ℕ) (L : P) :
    pd (k + 1) (Dtot L) = Dtot (pd (k + 1) L) + pd k L := by
  have h := Derivation.congr_fun (lie_pd_succ_deriv k) L
  rw [Derivation.commutator_apply] at h
  rw [← h]; ring

/-- `∂(D L)/∂y^(0) = D(∂L/∂y^(0))`. -/
theorem pd_zero_deriv (L : P) : pd 0 (Dtot L) = Dtot (pd 0 L) := by
  have h := Derivation.congr_fun lie_pd_zero_deriv L
  rw [Derivation.commutator_apply] at h
  simpa [sub_eq_zero] using h

/-! ### Order -/

/-- The **order** of a differential polynomial: the highest `k` with `y^(k)` occurring. A
constant has order `0`, as does anything in `y` alone — the convention costs nothing, since
every statement below is guarded by `order L < N` rather than by an exact value. -/
noncomputable def order (L : P) : ℕ := (L.vars.image Prod.snd).sup id

/-- Above the order, the partial derivatives vanish. This is what makes the Euler operator's
infinite sum finite. -/
theorem pd_eq_zero_of_order_lt {L : P} {k : ℕ} (h : order L < k) : pd k L = 0 := by
  refine MvPolynomial.pderiv_eq_zero_of_notMem_vars fun hmem => ?_
  have : k ≤ order L :=
    Finset.le_sup (f := id) (Finset.mem_image_of_mem Prod.snd hmem)
  omega

/-! ### The Euler operator -/

/-- The **Euler operator truncated at order `N`**:
`∑_{k<N} (-1)^k D^k (∂L/∂y^(k))`.

Truncated rather than infinite so that the boundary term of the integration by parts stays
visible; `E` below picks `N` large enough that it vanishes. -/
noncomputable def euler (N : ℕ) (L : P) : P :=
  ∑ k ∈ Finset.range N, (-1 : ℚ) ^ k • (Dtot : P → P)^[k] (pd k L)

theorem euler_succ (N : ℕ) (L : P) :
    euler (N + 1) L = euler N L + (-1 : ℚ) ^ N • (Dtot : P → P)^[N] (pd N L) :=
  Finset.sum_range_succ _ _

/-- **The exact integration-by-parts identity.**

```
  euler (N+1) (D L) = (-1)^N • D^(N+1) (∂L/∂y^(N))
```

Everything cancels except the boundary term. The proof is induction on `N`: the commutator
identity splits `∂(DL)/∂y^(k+1)` into two pieces, one of which is the next summand with the
opposite sign, and they annihilate in pairs. -/
theorem euler_deriv (N : ℕ) (L : P) :
    euler (N + 1) (Dtot L) = (-1 : ℚ) ^ N • (Dtot : P → P)^[N + 1] (pd N L) := by
  induction N with
  | zero => simp [euler, pd_zero_deriv]
  | succ N ih =>
      rw [euler_succ, ih, pd_succ_deriv, iterate_deriv_add, smul_add,
        ← Function.iterate_succ_apply (f := (Dtot : P → P)), pow_succ]
      -- the surviving term from the induction hypothesis cancels the new one
      module

/-- **The Euler operator.** `euler` run past the order, where it has stabilised. -/
noncomputable def E (L : P) : P := euler (order L + 1) L

/-- Past the order, lengthening the truncation changes nothing. -/
theorem euler_eq_of_order_lt {L : P} {N M : ℕ} (hN : order L < N) (hNM : N ≤ M) :
    euler M L = euler N L := by
  induction M with
  | zero => omega
  | succ M ih =>
      rcases Nat.lt_or_ge N (M + 1) with h | h
      · rw [euler_succ, ih (by omega), pd_eq_zero_of_order_lt (by omega)]
        simp
      · have : N = M + 1 := by omega
        rw [this]

theorem E_eq_euler {L : P} {N : ℕ} (h : order L < N) : E L = euler N L :=
  (euler_eq_of_order_lt (L := L) (N := order L + 1) (M := N) (by omega) (by omega)).symm

/-- **Total derivatives are variationally trivial**: `E ∘ D = 0`.

A Lagrangian that is a total derivative contributes nothing to the Euler–Lagrange equations —
the classical statement that adding a total derivative to a Lagrangian does not change the
dynamics. Formally it is exactness of the variational complex at that spot, one of the two
inclusions; the converse (`E L = 0 ⟹ L = D f`) needs a homotopy operator and is not proved
here.

The proof takes a truncation long enough for *both* `L` and `D L`, so that
`euler_deriv`'s boundary term `∂L/∂y^(N)` is already past the order of `L`. -/
theorem E_deriv (L : P) : E (Dtot L) = 0 := by
  set M := max (order (Dtot L) + 1) (order L + 2) with hM
  obtain ⟨N, hN⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  have h1 : E (Dtot L) = euler M (Dtot L) := E_eq_euler (by omega)
  rw [h1, hN, euler_deriv, pd_eq_zero_of_order_lt (L := L) (k := N) (by omega)]
  simp

/-! ### `E` as a linear map, and functionals

`E` is defined by a truncation that depends on its argument, so linearity is not free: it
comes from choosing one truncation long enough for every polynomial involved. -/

theorem euler_add (N : ℕ) (L M : P) : euler N (L + M) = euler N L + euler N M := by
  simp only [euler, ← Finset.sum_add_distrib, map_add, iterate_deriv_add, smul_add]

/-- The iterated total derivative is `ℚ`-homogeneous. As with `iterate_deriv_add`, `map_smul`
handles one application and the induction lifts it under the iterate. -/
private theorem iterate_deriv_smul (n : ℕ) (c : ℚ) (a : P) :
    (Dtot : P → P)^[n] (c • a) = c • (Dtot : P → P)^[n] a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Derivation.map_smul, ih]

theorem euler_smul (N : ℕ) (c : ℚ) (L : P) : euler N (c • L) = c • euler N L := by
  simp only [euler, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.map_smul, iterate_deriv_smul, smul_comm]

theorem E_add (L M : P) : E (L + M) = E L + E M := by
  set N := max (order (L + M)) (max (order L) (order M)) + 1 with hN
  rw [E_eq_euler (L := L + M) (N := N) (by omega), E_eq_euler (L := L) (N := N) (by omega),
    E_eq_euler (L := M) (N := N) (by omega), euler_add]

theorem E_smul (c : ℚ) (L : P) : E (c • L) = c • E L := by
  set N := max (order (c • L)) (order L) + 1 with hN
  rw [E_eq_euler (L := c • L) (N := N) (by omega), E_eq_euler (L := L) (N := N) (by omega),
    euler_smul]

/-- **The Euler operator**, bundled. -/
noncomputable def Elin : P →ₗ[ℚ] P where
  toFun := E
  map_add' := E_add
  map_smul' := E_smul

/-- **Functionals**: differential polynomials modulo total derivatives.

The algebraic stand-in for `∫ L dx`. Two Lagrangians differing by a total derivative have the
same integral (up to boundary terms) and must define the same variational problem, so the
functional is the class, not the representative. -/
noncomputable abbrev Functionals : Type :=
  P ⧸ LinearMap.range (Dtot.toLinearMap : P →ₗ[ℚ] P)

/-- **The variational derivative is well defined on functionals.**

This is `E ∘ D = 0` doing its structural job: because `E` kills total derivatives, it factors
through the quotient, so "the Euler–Lagrange equations of a functional" is a legitimate
notion rather than an artefact of the chosen Lagrangian. -/
noncomputable def EFunctional : Functionals →ₗ[ℚ] P :=
  Submodule.liftQ _ Elin (by
    rintro _ ⟨f, rfl⟩
    exact E_deriv f)

@[simp] theorem EFunctional_mk (L : P) :
    EFunctional (Submodule.Quotient.mk L) = E L := rfl

/-! ### Worked Lagrangians

Each of these has order `1`, so `euler 3` is already the full Euler operator on it. The
conventional factor of `½` is dropped; it changes the Euler–Lagrange expression by a scalar
and nothing else. -/

section Examples

/-- **The free particle**, `L = (y')²`. The Euler–Lagrange expression is `-2y''`, i.e. the
equation of motion is `y'' = 0`. -/
example : euler 3 (y[1] ^ 2) = -2 * y[2] := by
  simp [euler, Finset.sum_range_succ, Derivation.leibniz_pow]

/-- **The harmonic oscillator**, `L = (y')² − y²`. The Euler–Lagrange expression is
`-2(y + y'')`, i.e. the equation of motion is `y'' + y = 0`. -/
example : euler 3 (y[1] ^ 2 - y[0] ^ 2) = -2 * (y[0] + y[2]) := by
  simp [euler, Finset.sum_range_succ, Derivation.leibniz_pow]
  ring

/-- **A null Lagrangian**, `L = 2y·y'`. Its Euler–Lagrange expression vanishes identically,
so it imposes no equation of motion at all. -/
example : euler 3 (2 * (y[0] * y[1])) = 0 := by
  simp [euler, Finset.sum_range_succ, Derivation.leibniz]

/-- …and the reason it is null: `2y·y'` is the total derivative of `y²`. -/
theorem deriv_y_sq : Dtot (y[0] ^ 2) = 2 * (y[0] * y[1]) := by
  rw [Derivation.leibniz_pow]
  simp [Wu.DiffPolynomial.Y]

/-- So its triviality is also an instance of the general theorem, with no computation at all:
`E` kills it because it *is* a total derivative. Two independent routes to one fact — the
concrete alternating sum above, and `E ∘ D = 0`. -/
example : E (2 * (y[0] * y[1])) = 0 := by
  rw [← deriv_y_sq, E_deriv]

end Examples

end Wu.Variational
