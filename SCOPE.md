# Scope: what this differential-algebra layer can reach, and what it cannot

Written 2026-08-14 after a literature sweep across the variational bicomplex, jet/contact/
symplectic geometry, and the Ritt–Kolchin / symbolic-computation strand. Sources at the end.

The organising fact is a clean one, and all three strands of the sweep converge on it:

> **The entire `E₁`-page of Vinogradov's C-spectral sequence — the Lagrangian formalism, the
> Euler operator, the Helmholtz conditions, the one-line and two-line theorems — is a theorem
> about modules over a differential ring.** Only the identification of the *abutment* with de
> Rham cohomology, and the global inverse problem, need geometry.

So the question is not "can algebra reach the calculus of variations" — it can, essentially
all of it. The question is which algebra we have.

---

## 1. What is built and building

Verified: full `lake build` clean, 8788 jobs, no `sorry` in any file below, axioms
`propext / Classical.choice / Quot.sound` throughout.

| Area | Files | Status |
|---|---|---|
| `R{y}` = `MvPolynomial (σ × ℕ) R`, universal property | `DiffPolynomial.lean` | ✅ |
| Differential ideals, radical closure `{S}`, Ritt's lemma, product lemma | `DiffSpec.lean`, `RadicalDiffIdeal.lean` | ✅ |
| Ritt–Raudenbush **reduction to primes** | `RittRaudenbush.lean` | ✅ (second half open — §3) |
| `⁅∂/∂y^(k+1), D⁆ = ∂/∂y^(k)`; Euler operator; `E ∘ D = 0`; functionals `P/im D`; integration by parts | `Variational.lean` | ✅ |
| Jet ring **with** independent variable; contact submodule; `df ≡ (Df) dx (mod contact)` | `JetContact.lean` | ✅ |
| `Derivation.localization`, differential `Spec`, structure-sheaf derivation | `DerivationLocalization.lean`, `StructureSheafDeriv.lean` | ✅ |
| `wu` / `wu_pde` tactics; Gauss–Codazzi–Ricci from `fderiv` | `Frontend.lean`, `WuDifferential/` | ✅ |

Two of these turn out to be positioned exactly where the literature says the algebraic core
lives. `[∂/∂u_i^(n), ∂] = ∂/∂u_i^(n−1)` is Barakat–De Sole–Kac eq. (1.2), which they take as
an *axiom* defining an "algebra of differential functions" — our `lie_pd_succ_deriv`. And
`⁅gradeDeriv, D⁆ = D` in `DiffPolynomialHeavy.lean` is the degree evolutionary field that
drives their Theorem 3.5 homotopy.

---

## 2. The three structural limits

Everything that is out of reach traces to one of these.

### 2.1 One derivation

`R{y}` is Ritt–Kolchin's **ordinary** case. The standard object is `k{Y} = k[ΘY]` with `Θ`
the free commutative monoid on `Δ = {δ₁,…,δ_m}`, i.e. index type `σ × (Δ →₀ ℕ)`.

**Verified**: the *ring*, its derivations, and their commutation generalise mechanically —
`MathlibableEvidence.lean` builds `DiffPoly R σ Δ` with `deriv_comm` and it compiles. The
*universal property* does not: `evalDiff` must send `θ y_i` to an order-independent product
of iterated derivations over `θ.support`, and `Finset.prod` cannot express it because
`Module.End R A` is not commutative. Routes: `Finset.noncommProd`, or
`Submonoid.closureCommMonoidOfComm` on the commuting family. Moderate, not mechanical.

What this costs: PDEs, conservation-law theory proper, and everything in the middle of the
horizontal complex (for `m = 1` the bicomplex degenerates to one column). Also
**multidimensional Poisson vertex algebras are a genuinely harder theory, not a
generalisation** — Carlet–Casati–Shadrin show the deformation theory is non-trivial for
`D > 1`, with non-vanishing 2nd and 3rd Poisson cohomology. Do not assume `m = 1` results lift.

### 2.2 Base of constants

`MvPolynomial.mkDerivation` produces an `R`-*linear* derivation, so `D` annihilates `R`.
Kolchin's `R{Y}` is over a differential ring. Without an `x` satisfying `Dx = 1` there is no
independent variable, hence no `x`-dependent Lagrangian and **no contact forms at all** — the
`dx` has nothing to refer to.

Sharp algebraic statement of the obstruction: under `Derivation R A A ≃ (Ω[A⁄R] →ₗ[A] A)` the
derivation is a contraction `ι_D`, the contact submodule is `ker ι_D`, and **`ι_D` is
surjective iff some `a` has `Da = 1`**. For `R{y}` the image is the proper ideal `(y',y'',…)`,
so there is no splitting and no horizontal line.

**Fixed, for the jet ring**: `JetContact.lean` adjoins `x` with `Dx = 1` and gets the
splitting and `df ≡ (Df) dx (mod contact)`. `DiffPolynomial` itself remains over constants,
which is correct for the ideal theory and for §1's variational results — neither needs `x`.

### 2.3 Characteristic zero

Not incidental. Every homotopy operator in the subject divides by an integer. Formalized as a
boundary case: over `𝔽₂`, `D(y²) = 0` with `y² ≠ 0`, so `ker D` is far larger than the
constants and exactness fails at step one. This is the same reason Ritt's lemma carries
`[Algebra ℚ A]`.

---

## 3. Reachable next, in order

All three research strands independently rank the same theorem first.

**(a) `ker E = R ⊕ D(R{y})` — the converse to `E ∘ D = 0`.** Olver Thm 4.7 (1st ed. p. 252);
Barnich–Brandt–Henneaux Thm 4.1(i); Barakat–De Sole–Kac Prop. 1.5.

Note the `R` summand — it is *not* `ker E = im D`. We have already formalized why
(`range_deriv_lt_ker_E`), and it is worth knowing that Olver–Shakiban's *A resolution of the
Euler operator I* prints the complex as exact and over-claims by exactly this summand.

Route: the graded homotopy. With `Δ = ∑ y^(k) ∂/∂y^(k)` the *total-degree* operator (note:
**not** our `gradeDeriv`, which weights by order `k`),

```
  Δ L = y · E(L) + D(I(L)),    I(L) = ∑_{k≥1} ∑_{i<k} y^(i) (−D)^{k−1−i} (∂L/∂y^(k))
```

so a homogeneous `L` of degree `n ≥ 1` with `E(L) = 0` is `D(I(L)/n)`. Our `ibp` is exactly
the lemma this needs.

**Blocker, verified**: Mathlib's Euler identity `IsHomogeneous.sum_X_mul_pderiv` requires
`[Fintype σ]`, and ours is `Unit × ℕ`. A version summing over a finite superset of `vars` has
to be proved. That is the real work, and it is *also* a clean Mathlib contribution.

**(b) `ker D = R`.** Short: if `p` has top order `N`, `Dp` contains `(∂p/∂y^(N)) y^(N+1)`,
which cannot cancel. Gives `H⁰` of the horizontal complex.

**(c) Helmholtz — take the graded shortcut.** Olver Thm 5.92 (2nd ed.) needs the Fréchet
derivative and formal adjoint. But Olver–Shakiban Corollary 2 gives, for our exact setting,
`P = E(L) ⟺ F(P) = N(P)` with `L = y·P/(n+1)` — self-adjointness tested on the single element
`y`, one scalar condition instead of the infinite Helmholtz system. Cheapest route by far.

**(d) The variational complex proper.** `Ω̃ = Λ•_A Ω[A⁄R]` with `δ` the Kähler differential,
`Ω = Ω̃ / L_D Ω̃`. Target Barakat–De Sole–Kac Thm 3.5 (graded homotopy, reuses `gradeDeriv`)
before Thm 3.2 (needs a `Normal` typeclass carrying antiderivatives `∫du_i^(n)` as data —
note a bare differential algebra is *not* normal, so the partials must be data, not derived).

**(e) Ritt–Raudenbush, second half — much cheaper than I first wrote.** I originally recorded
this as "the characteristic-set argument". That was wrong, and wrong in the expensive
direction. Kaplansky's proof needs **no** rankings, characteristic sets, Rosenfeld lemma, or
DCC on autoreduced sets. It works with one differential indeterminate at a time, rank
`(ord, deg) ∈ ℕ ×ₗ ℕ` (so `Prod.Lex` gives well-foundedness free), and rests on one lemma:

> **Ritt reduction.** For `α ∈ A{x}` and any `f`, there are `m, n` and `g` of strictly smaller
> rank with `lc(α)^m · sep(α)^n · f − g ∈ [α]`. *(Double induction: on `ord f`, then `deg f`,
> using `α^{(k)} = sep(α)·x^{(r+k)} + T_k`.)*

Then: `I` maximal non-finite-type is prime (**have it**); pick `α ∈ I ∖ J` of minimal rank;
`lc(α), sep(α) ∉ I`; Ritt-reduce to get `a·I ⊆ ⟨α, J⟩`; and the product lemma (**have it**)
closes it via `I² ⊆ ⟨α, J, e₁,…,e_r⟩ ⊆ I`. Char 0 enters once, at `α − (1/d)·x^{(r)}·sep(α)`.

Cost: Ritt reduction ~200–400 lines, main argument ~150, plus the reindexing
`R{y₁,…,y_n} ≅ (R{y₁,…,y_{n−1}}){y_n}` with transported derivation. Note the definitions must
live on `MvPolynomial (σ × ℕ) R`, **not** on the reflected `Wu.Poly` the tactic uses.

Characteristic sets belong to Rosenfeld–Gröbner decomposition, which is a different theorem —
and one whose load-bearing step, **Lazard's lemma**, is the genuinely hard and historically
fragile item in this area (BLOP's 1995 proof carried an unstated no-embedded-primes
hypothesis, flagged by Morrison; six proofs exist and Boulier–Lemaire–Poteaux–Moreno Maza
(2019) note that no one has yet audited which avoids it). Do not conflate the two.

---

## 4. What is outside, and why

| Item | Why it is out |
|---|---|
| **Cartan–Kähler** | An `n`-fold stack of Cauchy–Kovalevskaya. Majorant series; **false in `C^∞`** (Lewy 1957). Formal integrability is algebraic; *convergence* is not. |
| **Darboux / Gray stability / Moser** | Flows with smooth parameter dependence and a genuine integral. Not algebraic. (No loss for multisymplectic work — there is *no* multisymplectic Darboux theorem; Ryvkin builds 3-forms on `ℝ⁶` with non-constant linear type.) |
| **Frobenius leaves of the Cartan distribution** | Involutivity is free algebraically (`[D_i,D_j] = 0` is an identity), but Frobenius fails in infinite dimensions. Replaced by the universal property: differential ring maps out of `R{y}` *are* the "integral manifolds". |
| **The variational principle as a statement about `∫`** | Needs orientation, measure, function space, Stokes to kill the boundary term. Sidestepped the way BBH do — define functionals as `V/∂V`, which is what `Functionals` is. |
| **Abutment `≅ H•_dR`, Takens acyclicity, global inverse problem** | Partitions of unity, Mayer–Vietoris. Genuinely topological. |
| **C-spectral sequence line theorems** | They *compute* manifold de Rham cohomology. The `E₁` page is algebra; the convergence is not. |

---

## 5. What we would have to add

**On our side:** the Δ-indexed ring's universal property (§2.1); an Euler identity for
infinitely many variables (§3a); a `Normal` typeclass carrying antiderivatives (§3d).

**In Mathlib** — none of this exists (all checked against our pin, `db584cd6`, v4.33.0):

- **No graded wedge on alternating maps.** `domCoprod` lands in `⊗`, not `Λ`. This is the
  single missing primitive blocking any forms work, including §3d.
- **No algebraic de Rham complex** `Ω^p_{A/R}` with `d` — only `Ω¹` (`KaehlerDifferential`).
- **No Koszul complex** by name — and Krasil'shchik–Verbovetsky's entire engine (Thm 1.19,
  hence Thm 2.8, hence the one-line theorem) *is* Koszul exactness.
- **No Ore extension with a derivation.** `Algebra/SkewPolynomial/Basic.lean` implements only
  the endomorphism twist `Xa = φ(a)X`; the file says so. Needed for Hamiltonian operators.
- **No jets, no contact geometry, no symplectic manifolds, no variational calculus.** Zero
  files for each. `LinearAlgebra/SymplecticGroup.lean` is matrices; `extDeriv` is normed
  spaces only, with its own TODO saying manifolds are not defined yet.

What *is* usable today and worth leaning on: `KaehlerDifferential.mvPolynomialBasis` (so
`Ω[R{y}⁄R]` is free on `dy^(k)`, with `mvPolynomialBasis_repr_apply = pderiv`), the cotangent
exact sequence `exact_mapBaseChange_map` (which *is* the horizontal/vertical splitting),
`Derivation.Lie`, and `Module.Basis.exteriorPower`.

**Two traps worth recording.**

*Do not try to make a ranking a `MonomialOrder`.* Mathlib's only instance,
`MonomialOrder.lex`, needs `WellFoundedGT` on the variable index. A differential ranking has
`y < y' < y'' < ⋯` — order type ω, with infinite *ascending* chains — so `WellFoundedGT (σ × ℕ)`
is false. The right object is Kolchin rank, the pair (leader, degree), which *is* well-ordered.
Build `IsRanking` from scratch.

*Do not try to state anything Noetherian about `R{y}`.* It genuinely isn't — `[x², (x')², …]`
strictly increases. The literature's discipline is to reduce every question to
`F[Θ_{≤v}Y]`, a polynomial ring in **finitely many** derivatives, which is Noetherian and
where `MvPolynomial.isNoetherianRing` applies. Rosenfeld's lemma is precisely the theorem that
licenses the reduction.

**The single highest-leverage edit in this repo** is §2.2: generalise `DiffPolynomial.deriv`
from an `R`-linear derivation to one extending a given derivation on `R`. It unblocks the
variational converse, conservation laws with `x`-dependent densities, and Picard–Vessiot, all
at once.

---

## 6. Adjacent territory: Picard–Vessiot

Worth scoping because our differential-ideal stack pays into it directly, and because the
cliff is unusually sharp.

**Reachable.** van der Put–Singer Prop. 1.20 — a Picard–Vessiot ring exists, is unique up to
differential isomorphism, and adds no constants. The construction is `k[X_ij, 1/det]` with
`(X_ij)' = A·(X_ij)`, quotiented by a **maximal differential ideal** (Zorn). Prerequisites we
already have or nearly have: `Derivation.localization` (vdPS Ex. 1.5(1d) — and Mathlib has no
such thing, which is candidate 2 of `MATHLIBABLE_REPORT.md`); and vdPS Lemma 1.17(1), *a
simple differential ring over ℚ has no zero divisors*, which is ~50 lines from our existing
API. There is also a route to "maximal differential ideal ⟹ prime" that runs through **Ritt's
lemma plus our reduction to primes** — a genuine payoff from the Ritt–Raudenbush stack.

**Not reachable.** Everything past Prop. 1.20. Theorems 1.27/1.28/1.34 (the Galois group is an
algebraic group; the torsor; the Galois correspondence) need linear algebraic groups, `G°`,
`dim G`, `Lie(G)`, Lie–Kolchin, Rosenlicht invariants, and neutral Tannakian categories.
Mathlib has none of these — `RepresentationTheory/Tannaka.lean` is finite groups only. That is
a multi-year project belonging to Mathlib's algebraic-geometry effort, not to us.

**Structural mismatch, stated plainly.** PV theory runs on a finitely generated *localized*
polynomial ring with a twisted derivation, where `D` does **not** send a generator to another
generator. So the `y^(k) ↦ y^(k+1)` combinatorics underlying Wu/Ritt/characteristic sets
transfers essentially not at all. The one place our exact ring is the natural home is vdPS
Exercise 1.35.4: `Frac(k{{y₁,…,y_n}})` is a PV extension with Galois group `GL_n(C)`.

## 7. An orthogonal track worth noting

Exterior differential systems have a core that is **finite-dimensional linear algebra**:
tableaux `A ⊂ W ⊗ V*`, prolongation `A^(1) = ker(δ|_{A⊗V*})`, Cartan characters, and Cartan's
test as an equality of dimensions. Seiler's symbolic-system form (Prop. 3.2 + Thm 3.4) proves
it by summing `n` short exact sequences and needs no Spencer cohomology computed explicitly.
Serre's 1963 letter (printed in Guillemin–Sternberg, Bull. AMS 70 (1964), App. pp. 43–46)
gives finiteness, and Malgrange's *Cartan involutiveness = Mumford regularity* identifies
involutivity with Castelnuovo–Mumford regularity.

This is adjacent to our engine rather than downstream of it: involutive bases were introduced
by Gerdt–Blinkov generalising Janet, *"a special case was slightly earlier discovered by Wu"*,
and Seiler shows the Cartan test and the Pommaret-basis inequality are the same inequality.

---

## Sources

Anderson, *The Variational Bicomplex* ([PDF](https://ncatlab.org/nlab/files/AndersonVariationalBicomplex.pdf)) ·
Olver, *Applications of Lie Groups to Differential Equations*, GTM 107 ([free notes](https://www-users.cse.umn.edu/~olver/sm_/v.pdf)) ·
Olver & Shakiban, *A resolution of the Euler operator I*, Proc. AMS 69 (1978) 223–229 ([PDF](https://www.ams.org/journals/proc/1978-069-02/S0002-9939-1978-0486822-8/S0002-9939-1978-0486822-8.pdf)) ·
Barakat, De Sole & Kac, *Poisson vertex algebras in the theory of Hamiltonian equations* ([arXiv:0907.1275](https://arxiv.org/abs/0907.1275)) ·
De Sole & Kac, *Lie conformal algebra cohomology and the variational complex* ([arXiv:0812.4897](https://arxiv.org/abs/0812.4897)) ·
Barnich, Brandt & Henneaux, *Local BRST cohomology* ([arXiv:hep-th/0002245](https://arxiv.org/abs/hep-th/0002245)) ·
Krasil'shchik & Verbovetsky, *Homological Methods in Equations of Mathematical Physics* ([arXiv:math/9808130](https://arxiv.org/abs/math/9808130)) ·
Vinogradov, *Introduction to Secondary Calculus* ([PDF](https://diffiety.mccme.ru/preprint/98/05_98.pdf)) ·
Bryant, *Notes on Exterior Differential Systems* ([arXiv:1405.3116](https://arxiv.org/abs/1405.3116)) ·
Seiler, *Spencer Cohomology, Differential Equations, and Pommaret Bases* ([PDF](https://www.mathematik.uni-kassel.de/~seiler/Papers/PDF/Spencer2.pdf)) ·
Hydon, *Partial Euler operators and the efficient inversion of Div* ([arXiv:2212.08455](https://arxiv.org/abs/2212.08455)) ·
Ritt, *Differential Algebra*, AMS Colloq. 33 (1950) · Kolchin, *Differential Algebra and Algebraic Groups* (1973).

## Coordination

Upstream's own paper — Xiao, Shen, Guo, Wang, Zhi, *Formalizing Wu-Ritt Method in Lean 4*,
[arXiv:2604.14912](https://arxiv.org/abs/2604.14912) (Apr 2026), which is
`WuProver/lean_characteristic_set`, i.e. this fork's upstream — closes with future work:
*"executable code extraction and extensions to differential polynomials."* That is this
project. The overlap is total and the field is small; the differential scope here is worth
raising with them directly rather than discovering the collision later.

Their stated obstruction is worth knowing: their well-foundedness instance is
`[Finite σ] : WellFoundedLT (TriangularSet σ R)`, and `σ × ℕ` is infinite. In the **ordinary**
case that is recoverable — a weak differential triangular set has at most `|σ|` elements, one
per differential indeterminate — but it needs the *differential* triangular-set predicate, not
the raw one. In the partial case it needs the genuine Kolchin minimal-bad-sequence argument.

---

**One claim I am relaying rather than asserting.** The research agents searched for prior
formalization of the variational bicomplex, the Euler operator on a differential algebra, jet
bundles or the Helmholtz conditions in Lean, Coq, Isabelle, Agda and Mizar, and found none —
the nearest being Physlib's *analytic* Euler–Lagrange operator over `Time → X`, which cannot
state `E ∘ D = 0`. That is a search result, not a proof of absence.
