/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DerivationOfNat
import CharSetTac.DiffPolynomial
import CharSetTac.EulerIdentity
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

/-! ### Integration by parts

The identity underneath everything in this subject:

```
  (D^k a)·b = (-1)^k a·(D^k b) + D(B_k(a,b))
```

"Moving `k` derivatives across a product costs `(-1)^k` plus a total derivative." Every
statement about the Euler operator is a corollary of it applied with `a = y`, and it is what
the classical `∫ u^(k) v = (-1)^k ∫ u v^(k)` becomes once the integral is discarded and only
the boundary term is kept.

`B_k` is defined by the recursion that the induction actually needs, rather than as
`∑_{j<k} (-1)^j (D^{k-1-j} a)(D^j b)` — the closed form has a truncated subtraction in the
exponent, and the recursion does not. -/

/-- The boundary term of integrating by parts `k` times. -/
noncomputable def boundary : ℕ → P → P → P
  | 0, _, _ => 0
  | (k + 1), a, b => (-1 : ℚ) ^ k • (a * (Dtot : P → P)^[k] b) + boundary k (Dtot a) b

/-- **Integration by parts, `k` times.** No hypothesis on the characteristic, and none on the
base: this holds over any commutative ring. -/
theorem ibp (k : ℕ) (a b : P) :
    (Dtot : P → P)^[k] a * b
      = (-1 : ℚ) ^ k • (a * (Dtot : P → P)^[k] b) + Dtot (boundary k a b) := by
  induction k generalizing a with
  | zero => simp [boundary]
  | succ k ih =>
      have hb : boundary (k + 1) a b
          = (-1 : ℚ) ^ k • (a * (Dtot : P → P)^[k] b) + boundary k (Dtot a) b := rfl
      have hleib : Dtot (a * (Dtot : P → P)^[k] b)
          = a * (Dtot : P → P)^[k + 1] b + (Dtot : P → P)^[k] b * Dtot a := by
        rw [Derivation.leibniz, Function.iterate_succ_apply' (f := (Dtot : P → P))]
        simp [smul_eq_mul]
      rw [Function.iterate_succ_apply, ih (Dtot a), hb, map_add, Derivation.map_smul, hleib,
        pow_succ, mul_comm (Dtot a) ((Dtot : P → P)^[k] b)]
      module

/-- The Euler operator is `y` integrated by parts out of `∑_k y^(k) ∂_k`. Stated at a single
`k`, which is the reusable form. -/
theorem yy_pd_eq (k : ℕ) (L : P) :
    y[k] * pd k L
      = (-1 : ℚ) ^ k • (y[0] * (Dtot : P → P)^[k] (pd k L))
        + Dtot (boundary k y[0] (pd k L)) := by
  have hy : (Dtot : P → P)^[k] y[0] = y[k] := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply' (f := (Dtot : P → P)), ih,
        Wu.DiffPolynomial.deriv_Y]
  rw [← hy, ibp]

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

/-! ### The converse, for homogeneous Lagrangians

`E ∘ D = 0` gives `im D ⊆ ker E`. The other inclusion is the substantial half, and this is
it for a homogeneous `L` of positive degree.

The mechanism is the **graded homotopy**. Euler's identity says the total-degree operator
`Δ = ∑_k y^(k) ∂/∂y^(k)` acts on a degree-`n` polynomial as multiplication by `n`. Feeding
each term of `Δ L` through integration by parts moves every derivative onto `y` itself,
leaving `y · E(L)` plus a total derivative. So

```
  n · L  =  y · E(L)  +  D(I(L))
```

and if `E(L) = 0` then `L = D(I(L)/n)` — the division by `n` being exactly why the theorem
is false in characteristic `p`. -/

section Converse

/-- The accumulated boundary term of integrating `∑_{k<N} y^(k) ∂_k L` by parts. -/
noncomputable def ibpSum (N : ℕ) (L : P) : P :=
  ∑ k ∈ Finset.range N, boundary k y[0] (pd k L)

/-- **Integration by parts, summed.** `∑_{k<N} y^(k) ∂_k L = y · euler N L + D(I_N L)`.

Each summand is `yy_pd_eq`; the sum just collects them. -/
theorem sum_yy_pd (N : ℕ) (L : P) :
    ∑ k ∈ Finset.range N, y[k] * pd k L = y[0] * euler N L + Dtot (ibpSum N L) := by
  rw [euler, ibpSum, Finset.mul_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [yy_pd_eq, mul_smul_comm]

/-- A bound on the orders occurring in `L` bounds `order L`. This is what makes `order`
usable on a concrete polynomial, where `vars` is computed from the syntax. -/
theorem order_lt_of_vars_lt {L : P} {N : ℕ} (hN : 0 < N) (h : ∀ p ∈ L.vars, p.2 < N) :
    order L < N := by
  rw [order]
  refine (Finset.sup_lt_iff hN).mpr fun b hb => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
  exact h p hp

/-- Every variable of `L` has order at most `order L`. -/
theorem snd_le_order {L : P} {p : Unit × ℕ} (hp : p ∈ L.vars) : p.2 ≤ order L :=
  Finset.le_sup (f := id) (Finset.mem_image_of_mem Prod.snd hp)

/-- **Euler's identity in `ℚ{y}`.** The `Fintype`-free form from
`CharSetTac/EulerIdentity.lean` applied at the index type `Unit × ℕ`, with the sum running
over orders `< N`. -/
theorem sum_yy_pd_eq_nsmul {L : P} {n N : ℕ} (h : L.IsHomogeneous n) (hN : order L < N) :
    ∑ k ∈ Finset.range N, y[k] * pd k L = n • L := by
  classical
  have hinj : Set.InjOn (fun k : ℕ => ((), k)) (Finset.range N) := by
    intro a _ b _ hab
    exact congrArg Prod.snd hab
  have himg : ∑ i ∈ (Finset.range N).image (fun k : ℕ => ((), k)),
      MvPolynomial.X i * MvPolynomial.pderiv i L
      = ∑ k ∈ Finset.range N, y[k] * pd k L := by
    rw [Finset.sum_image (fun a ha b hb => hinj ha hb)]
    rfl
  rw [← himg]
  refine MvPolynomial.IsHomogeneous.sum_X_mul_pderiv_of_vars_subset ?_ h
  intro p hp
  refine Finset.mem_image.mpr ⟨p.2, Finset.mem_range.mpr ?_, ?_⟩
  · exact lt_of_le_of_lt (snd_le_order hp) hN
  · exact Prod.ext rfl rfl

/-- **The graded homotopy.** `n · L = y · E(L) + D(I(L))` for `L` homogeneous of degree `n`.

This is the identity the whole converse rests on. Note it is unconditional — no hypothesis
on `E(L)` — and holds in any characteristic. -/
theorem nsmul_eq_yy_mul_euler_add {L : P} {n N : ℕ} (h : L.IsHomogeneous n)
    (hN : order L < N) :
    (n : ℚ) • L = y[0] * euler N L + Dtot (ibpSum N L) := by
  rw [← sum_yy_pd N L, sum_yy_pd_eq_nsmul h hN, ← Nat.cast_smul_eq_nsmul ℚ]

/-- **A variationally trivial homogeneous Lagrangian of positive degree is a total
derivative.**

The converse to `E ∘ D = 0`, in the homogeneous case. Dividing by `n` is where
characteristic zero is used, and `Wu.Variational.deriv_sq_eq_zero` is the counterexample
showing it cannot be avoided. -/
theorem exists_deriv_eq_of_euler_eq_zero {L : P} {n : ℕ} (hn : n ≠ 0)
    (h : L.IsHomogeneous n) (hE : E L = 0) :
    ∃ f : P, Dtot f = L := by
  set N := order L + 1 with hNdef
  have hN : order L < N := by omega
  have hEN : euler N L = 0 := by rw [← E_eq_euler hN]; exact hE
  have key := nsmul_eq_yy_mul_euler_add h hN
  rw [hEN, mul_zero, zero_add] at key
  refine ⟨((n : ℚ)⁻¹) • ibpSum N L, ?_⟩
  rw [Derivation.map_smul, ← key, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]

/-- **The characterisation, for homogeneous Lagrangians of positive degree.**

`L` is variationally trivial if and only if it is a total derivative — both halves of
exactness at the Lagrangian slot of the variational complex, in the graded case. The forward
direction is the converse proved above; the reverse is `E ∘ D = 0`. -/
theorem euler_eq_zero_iff_mem_range {L : P} {n : ℕ} (hn : n ≠ 0) (h : L.IsHomogeneous n) :
    E L = 0 ↔ ∃ f : P, Dtot f = L :=
  ⟨fun hE => exists_deriv_eq_of_euler_eq_zero hn h hE, fun ⟨f, hf⟩ => hf ▸ E_deriv f⟩

/-- The null Lagrangian `2y·y'` is homogeneous of degree `2`, so the characterisation applies
and *produces* a potential rather than requiring one to be guessed. -/
example : ∃ f : P, Dtot f = 2 * (y[0] * y[1]) := by
  refine (euler_eq_zero_iff_mem_range (n := 2) (by norm_num) ?_).mp ?_
  · have h1 : (y[0] : P).IsHomogeneous 1 := by
      rw [Wu.DiffPolynomial.Y]; exact MvPolynomial.isHomogeneous_X _ _
    have h2 : (y[1] : P).IsHomogeneous 1 := by
      rw [Wu.DiffPolynomial.Y]; exact MvPolynomial.isHomogeneous_X _ _
    rw [show (2 : P) = MvPolynomial.C (2 : ℚ) from (map_ofNat _ 2).symm]
    simpa using ((MvPolynomial.isHomogeneous_C _ (2 : ℚ)).mul (h1.mul h2))
  · rw [← deriv_y_sq, E_deriv]

end Converse

/-! ### Where the complex is *not* exact, and why

`E ∘ D = 0` says `im D ⊆ ker E`. The converse — every variationally trivial Lagrangian is a
total derivative — is the substantial half, and over a base of **constants** it is *false as
usually stated*. The correct statement (Barakat–De Sole–Kac, Prop. 1.5) is

```
  ker E = R ⊕ D(R{y})
```

with the `R` summand genuinely there: a constant is variationally trivial, but it is not a
total derivative, because every `D f` has zero constant term. Geometrically one has
`1 = D_x(x)` and the summand disappears — but `ℚ{y}` has no `x`, which is exactly the gap
`WuDifferential/JetContact.lean` fills.

This matters practically: Olver–Shakiban's *A resolution of the Euler operator I* (Proc. AMS
69 (1978) 223–229) prints the complex `0 → R → R{u} → R{u} → …` as exact, and at the
`E`-slot in degree `0` that over-claims by exactly this one summand. The two theorems below
are that correction, formalized. -/

section NotExact

/-- **A total derivative has zero constant term.** Each term of `D f` carries a factor
`y^(k+1)`. -/
theorem constantCoeff_deriv (f : P) : MvPolynomial.constantCoeff (Dtot f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
      rw [Derivation.leibniz, Wu.DiffPolynomial.deriv_X]
      simp [smul_eq_mul]

/-- **Constants are variationally trivial.** Every `∂/∂y^(k)` kills them, so every term of the
alternating sum vanishes — at any truncation. -/
theorem euler_C (N : ℕ) (c : ℚ) : euler N (C c) = 0 := by
  simp [euler, pd]

theorem E_C (c : ℚ) : E (C c) = 0 := euler_C _ c

/-- **…but a nonzero constant is not a total derivative.** So `ker E ⊋ im D`, and the
variational complex is *not* exact at the Lagrangian slot over a base of constants. -/
theorem C_notMem_range_deriv {c : ℚ} (hc : c ≠ 0) :
    (C c : P) ∉ LinearMap.range (Dtot.toLinearMap : P →ₗ[ℚ] P) := by
  rintro ⟨f, hf⟩
  have hf' : Dtot f = C c := hf
  have h := congrArg MvPolynomial.constantCoeff hf'
  rw [constantCoeff_deriv] at h
  simp only [MvPolynomial.constantCoeff_C] at h
  exact hc h.symm

/-- The gap, stated outright: the kernel of the Euler operator strictly contains the image of
the total derivative. -/
theorem range_deriv_lt_ker_E :
    ∃ L : P, E L = 0 ∧ L ∉ LinearMap.range (Dtot.toLinearMap : P →ₗ[ℚ] P) :=
  ⟨C 1, E_C 1, C_notMem_range_deriv one_ne_zero⟩

end NotExact

/-! ### Where it stops: characteristic `p`

Ritt's lemma needs a `ℚ`-algebra, and so does the converse to `E ∘ D = 0` — the homotopy
divides by the polynomial degree. That is not an artefact of the proofs. In characteristic
`p` the total derivative acquires a large kernel: every `p`-th power is a nonconstant element
that `D` annihilates, so `ker D` is much bigger than `R` and the whole exactness story fails
at the first step. -/

section CharP

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
instance : Fact (1 < 2) := ⟨one_lt_two⟩

/-- `ℚ{y}`'s counterpart over `𝔽₂`. -/
abbrev P₂ : Type := Wu.DiffPolynomial (ZMod 2) Unit

private theorem two_eq_zero : (2 : P₂) = 0 := by
  have h : (MvPolynomial.C (2 : ZMod 2) : P₂) = 0 := by
    rw [show (2 : ZMod 2) = 0 from by decide, map_zero]
  rwa [map_ofNat] at h

/-- **In characteristic 2, `D(y²) = 0`.** Over `ℚ` the same computation gives `2yy'`, which is
`deriv_y_sq` above and is nonzero. -/
theorem deriv_sq_eq_zero :
    Wu.DiffPolynomial.deriv (ZMod 2) Unit (Wu.DiffPolynomial.Y (() : Unit) 0 ^ 2) = 0 := by
  rw [Derivation.leibniz_pow]
  simp only [Wu.DiffPolynomial.deriv_Y, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    two_eq_zero, zero_mul]

/-- …and `y²` is not zero, nor a constant. So in characteristic `p` the kernel of `D` is much
larger than the constants, and the exactness story collapses at the first step. This is the
same obstruction that makes Ritt's lemma a `ℚ`-algebra theorem. -/
theorem sq_ne_zero : (Wu.DiffPolynomial.Y (() : Unit) 0 ^ 2 : P₂) ≠ 0 := by
  intro h
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single (((), 0) : Unit × ℕ) 2)) h
  rw [Wu.DiffPolynomial.Y, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_zero, if_pos rfl] at hc
  exact absurd hc (by decide)

end CharP

end Wu.Variational
