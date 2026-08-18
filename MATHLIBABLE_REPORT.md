# `/mathlibable` — upstreaming assessment

Eight candidates, assessed 2026-08-14 against Mathlib `db584cd6d4` (2026-08-10, toolchain
v4.33.0). Build clean at 8793 jobs; every declaration below elaborates.

Candidates 7 and 8 were added later: they came out of the base-ring generalisation and the
variational converse, and each fills a gap that was *verified* by building against Mathlib
rather than inferred from a search.

Two proposed restatements are **verified compiling** in
[CharSetTac/MathlibableEvidence.lean](CharSetTac/MathlibableEvidence.lean), which the root
module imports so the claims break loudly rather than rot. One verdict has already been
executed (candidate 5, deleted).

| # | Declaration | Verdict |
|---|---|---|
| 1 | `Wu.DiffPolynomial` + universal property | **YES — but generalise first** (literature-weakening) |
| 2 | `Derivation.localization` (+ 2 lemmas) | **YES — add as is** *(strongest candidate)* |
| 3 | `Derivation.map_ofNat` | **YES — add as is** (restate with `ofNat(n)`) |
| 4 | `Wu.IsDiffIdeal` + `IsDiffIdeal.radical` (Ritt's lemma) | **YES — add as is**, with one open question |
| 5 | `TrivSqZeroExt.isUnit_of_isUnit_fst` | **NO — Mathlib has it** ✅ *deleted* |
| 6 | `Derivation.toDualHom`, `TrivSqZeroExt.dualMap` | **BORDERLINE — needs a human** |
| 7 | `MvPolynomial.mapCoeffsDeriv` | **YES — add as is** (Mathlib has only the univariate case) |
| 8 | `MvPolynomial.IsHomogeneous.sum_X_mul_pderiv_of_vars_subset` | **YES — add as is** (drops a `[Fintype σ]`) |

---

## The literature anchor (shared Phase 3)

Channels run: WebSearch ×3 at different generality levels; nLab; Stacks Project (n/a — not an
algebraic-geometry concept, checked); arXiv; MathOverflow/lecture-notes corpus. **ChatGPT MCP:
n/a — `ask_chatgpt_math` is not configured in this session.** Local references: n/a — no
`.mathlib-quality/references/` directory in this project.

The literature is unanimous and it **disagrees with the shipped form of candidate 1**:

> A differential ring is a commutative ring with a **set** of derivations Δ = {δ₁, …, δ_m};
> the case Δ = {δ} is called *ordinary*. The ring of differential polynomials is
> `k{Y} = k[ΘY]`, polynomials in the infinite set `{θy_i}` where Θ is the free commutative
> monoid on Δ. A homomorphism of differential rings out of `R{x₁,…,x_n}` is uniquely
> determined by the images of the generators, with no restriction on those images.

That last sentence is exactly `evalDiff_deriv` + `evalDiff_unique`, so the *universal property
is the right one*. The **index type is not**: ours is `ℕ`, i.e. Θ for the ordinary case only.

nLab's `differential algebra` page does not define the Ritt algebra at all (checked — it
covers only "algebra with a derivation, typically `d ∘ d = 0`"), so it neither confirms nor
contradicts.

Sources: [Ritt–Raudenbush notes (Sam, UCSD)](https://mathweb.ucsd.edu/~ssam/notes/diffalg.pdf),
[Differential algebra lecture notes (Li)](http://www.mmrc.iss.ac.cn/~weili/DA2022/Lecturenotes/DA-1.pdf),
[An Introduction to Differential Algebra (Boulier)](https://www.matem.unam.mx/~lara/cimpa23/francois/An-Introduction-to-Differential-Algebra.pdf),
[Notes on differential algebra (Dale, Berkeley)](https://math.berkeley.edu/~reiddale/differential_algebra_notes.pdf),
[Canonical characteristic sets of characterizable differential ideals](https://arxiv.org/pdf/math/0702130),
[nLab: differential algebra](https://ncatlab.org/nlab/show/differential+algebra).

---

## 1. `Wu.DiffPolynomial` — YES, but generalise first

`CharSetTac/DiffPolynomial.lean` · kind: `abbrev` (+ `deriv`, `evalDiff`, `evalDiff_deriv`,
`evalDiff_unique`) · BIG (introduces a named mathematical structure).

**One-line check (2b).** `abbrev DiffPolynomial := MvPolynomial (σ × ℕ) R` is a one-liner.
Exemption: *semantic intent / API name* — **yes**. `R{y}` is the object Ritt–Raudenbush is
stated about; the name plus the universal property is the API surface. Being an `abbrev`
(reducible) is deliberate, so the whole `MvPolynomial` API applies without transport.
→ ONE-LINER WITH-EXEMPTION.

**Generality (4b): STRICTLY NARROWER THAN STANDARD.** `ℕ` is Θ for the ordinary case;
literature standard is `Δ →₀ ℕ`.

**Verified weakening.** The generalisation compiles — `DiffPoly R σ Δ := MvPolynomial (σ × (Δ →₀ ℕ)) R`,
`deriv δ := mkDerivation R fun p => X (p.1, p.2 + Finsupp.single δ 1)`, `deriv_Y`, `deriv_X`,
**and `deriv_comm`** (the derivations commute, which is what makes it a *partial* differential
ring rather than a ring carrying several unrelated derivations). See
`MathlibableEvidence.lean`. Ordinary case is `Δ = Unit`.

**Diamond risk (4.5): LOW.** `deriv` is a plain `def`, not an `instance`, and deliberately not
an instance of Mathlib's `Differential` — see candidate 4's open question. Being an `abbrev`,
`DiffPolynomial` introduces no new instances at all; typeclass search sees `MvPolynomial`.

**Mathlib search (5): not present.** grep for `differential polynomial` / `DifferentialPolynomial`
/ `Ritt` / `Kolchin` / `Raudenbush` / `Picard-Vessiot` / `differential Galois` / `jet space` /
`prolongation` → zero. Loogle `Derivation, IsLocalization` and the `Derivation` numeral family
→ nothing adjacent. Mathlib's differential-algebra surface is exactly three files:
`RingTheory/Derivation/DifferentialRing.lean` (the `Differential` class),
`FieldTheory/Differential/Basic.lean`, `FieldTheory/Differential/Liouville.lean`.

*Encoding precedent:* `MvPolynomial (idx × ℕ) ℤ` is already the Witt-vector idiom
(`RingTheory/WittVector/StructurePolynomial.lean`), so the `σ × ℕ` shape is Mathlib-native —
different object, same encoding.

**Call sites (6.0): K = 0 non-example consumers; 12 uses in
[CharSetTac/DiffPolynomialExamples.lean](CharSetTac/DiffPolynomialExamples.lean).**

Recorded honestly, because the distinction matters to a reviewer. The examples exercise
`DiffPolynomial`, `deriv`, `Y`, `evalDiff`, `evalDiff_deriv` and `evalDiff_unique` — including
`isDiffIdeal_expOde`, where `R{y}` and `IsDiffIdeal` meet, and
[CharSetTac/DiffPolynomialHeavy.lean](CharSetTac/DiffPolynomialHeavy.lean), where the whole
stack lands on `PowerSeries` (`exp` kills the radical differential ideal `{y' - y}`).

But demonstrations are not consumers. Ritt–Raudenbush's *reduction* half is now proved
(candidate 4) — and it is stated abstractly over any `Derivation R A A`, so it does not
mention `R{y}` either. What would make `R{y}` load-bearing is the *second* half, that primes
in `R{y}` have finite bases, and that is the characteristic-set argument, still unwritten.

So this remains the soft spot in candidate 1's case, and it is why candidate 1 should ship
alongside candidate 4 rather than alone.

**Cost.** Def + derivations + commutation: **CHEAP** (done, compiles). The universal property:
**MODERATE** and *not* mechanical — `evalDiff` currently sends `y^(k) ↦ d^[k] (f i)`, and in
the Δ-case the image of `θ y_i` is a product of iterated derivations over `θ.support`, which
needs an order-independent product. `Finset.prod` will not do (`Module.End R A` is not
commutative); the routes are `Finset.noncommProd`, or `Submonoid.closureCommMonoidOfComm` on
the commuting family followed by `Finsupp.prod` inside that submonoid. Per the skill,
**EXPENSIVE/MODERATE does not downgrade the verdict** — getting the right form is the work.

**Next action:** `/generalise Wu.DiffPolynomial` against the Δ-target. Proposed location
`Mathlib/RingTheory/Derivation/DifferentialPolynomial.lean`; PR title
`feat(RingTheory/Derivation): the differential polynomial ring R{y}`. Ship as one PR with
candidate 4 (`IsDiffIdeal`) — they are the same API layer, and `R{y}` with no differential
ideals to put in it is half a contribution.

---

## 2. `Derivation.localization` — YES, add as is *(ship this first)*

`CharSetTac/DerivationLocalization.lean:165` (+ `localization_algebraMap`, `localization_mk'`).

**The gap, named.** Mathlib can localize **Kähler differentials** — `Ω[Aₚ/Rₚ]` is the
localization of `Ω[A/R]` (`RingTheory/Kaehler/TensorProduct.lean:233`, `isLocalizedModule`) —
but it cannot extend a plain `d : Derivation R A A` to `Derivation R S⁻¹A S⁻¹A`. Confirmed by
five methods: grep over `Mathlib/RingTheory/Derivation/*` (zero occurrences of "localization"
in the entire directory), grep over all of `Mathlib/`, Loogle `Derivation, IsLocalization`
(one hit, `KaehlerDifferential.span_range_map_derivation_of_isLocalization` — unrelated),
name-pattern search, and the `Derivation.lift*` family (`liftOfSurjective`,
`liftOfRightInverse`), which does not apply.

This is the quotient rule `d(a/s) = (s·da − a·ds)/s²`. It is in every commutative-algebra text
(Matsumura, Eisenbud) and it is *missing*.

**Composition check (6): NOT-COMPOSABLE.** The Kähler route would need
`Derivation R A A ≃ (Ω[A/R] →ₗ[A] A)`, then `IsLocalizedModule.map`, then back — but Mathlib's
localization statement moves the *base* to `Rₚ` as well, while this keeps `R` fixed. That is
not a ≤3-line composition; it is a different theorem.

**Call sites (6.0): K = 10 across 3 files**, all outside the declaring file.

| Caller | Usage |
|---|---|
| `StructureSheafDeriv.lean:53` | `stalkDeriv` is defined as `d.localization … primeCompl` |
| `StructureSheafDeriv.lean:73` | `localization_mk'` — the load-bearing lemma for `sectionDeriv_mem` (the quotient rule is what keeps `isLocallyFraction` alive) |
| `StructureSheafDeriv.lean:161` | `localization_algebraMap` in `sheafDeriv`'s `map_smul'` |
| `DiffSpec.lean:124` | `localization_algebraMap` in `isDiffIdeal_map_of_diffPrime` |
| `DerivationLocalizationExamples.lean:30,35,38,51,68,72` | six uses across the worked examples (`Localization.Away`, `FractionRing`) |

No inline re-derivation anywhere. Real API with real consumers — the strongest composability
signal in this batch by a wide margin.

**Proof strategy (4.6): REFACTOR-RECOMMENDED — flagged, not resolved.** The proof goes via
dual numbers: a derivation is a ring hom `a ↦ a + (da)ε`, every `s ∈ S` lands on a unit
there, and `IsLocalization.lift` does the rest with no representative-chasing. That is
legitimate and Mathlib has the machinery (`RingTheory/Derivation/ToSquareZero.lean`,
`Algebra/DualNumber.lean`). But a reviewer may prefer it phrased through
`derivationToSquareZeroEquivLift` rather than a hand-rolled `toDualHom` — see candidate 6.

**Open generality question (routed to `/generalise`, not resolved here).** The literature form
is module-valued: `Derivation R A M ⟶ Derivation R S⁻¹A (S⁻¹M)`. I did **not** test that
weakening, so I am not claiming the current form is maximally general — I am claiming it is
correct, needed, and absent. The self-derivation case is what every application uses.

**Next action:** `/generalise Derivation.localization` (settle the module-valued question),
then `/cleanup`. Proposed location `Mathlib/RingTheory/Derivation/Localization.lean`; PR title
`feat(RingTheory/Derivation): extend a derivation along a localization`.

---

## 3. `Derivation.map_ofNat` — YES, add as is

`CharSetTac/DiffFrontend.lean:53`. SMALL. Kind: `theorem` → Phase 4.5 n/a.

**The gap, named.** `map_ofNat` is an established Mathlib convention shipped *alongside*
`map_natCast`: `Data/Nat/Cast/Basic.lean:148` (`RingHomClass`),
`Algebra/Polynomial/Eval/Defs.lean:551`, `Algebra/MvPolynomial/Eval.lean:341`,
`Data/ENat/Basic.lean:587`, `Data/Matrix/Diagonal.lean:178`. `Derivation` has
`map_zero`, `map_one_eq_zero`, `map_natCast`, `map_intCast`, `map_algebraMap` — and **no
`map_ofNat`**. Loogle's `Derivation, OfNat.ofNat` query returns all 124 neighbours and confirms
the family has exactly this hole.

**Why it matters concretely.** `map_natCast` is about `Nat.cast`; a numeric *literal* is
`OfNat.ofNat`. So `simp` leaves `D 2` standing. In this project that cost real time: it silently
broke the logistic-equation and second-order-harmonicity examples, because `D 2` survived as a
spurious atom and poisoned the characteristic set. That is the recurring manual reformulation
Mathlib is missing the canonical form for.

**Generality: MAXIMALLY GENERAL.** The binders match Mathlib's own `Derivation` structure
*exactly* (`[CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A] [Module A M]
[Module R M]`) — verified against `RingTheory/Derivation/Basic.lean:44`. Nothing to drop.

**Statement shape (5.5): RESTATE-BEFORE-SHIP.** Ours spells the numeral
`no_index (OfNat.ofNat n)`; Mathlib has a macro for precisely this,
`ofNat(n)` (`Mathlib/Tactic/OfNat.lean:22`). Cosmetic, not mathematical — so this does *not*
make it a generalise-first case, but the PR should use the macro. **The restatement is
verified compiling** (`MathlibableEvidence.lean`), including that the `@[simp]` lemma fires on
a literal.

**Next action:** ship the `ofNat(n)` form into
`Mathlib/RingTheory/Derivation/Basic.lean`, immediately after `map_natCast`. PR title
`feat(RingTheory/Derivation): add Derivation.map_ofNat`. This is a five-minute PR and the
lowest-risk item in the batch — a good first contact with the reviewers for the rest.

---

## 4. `Wu.IsDiffIdeal` and `IsDiffIdeal.radical` (Ritt's lemma) — YES, with one open question

`CharSetTac/DiffSpec.lean:41` and `CharSetTac/RadicalDiffIdeal.lean:172`, plus the closure
operator `radicalDiffIdeal` and the product lemma `radicalDiffIdeal_mul_le`. BIG — Ritt's
lemma is a named classical theorem.

**Gap.** Mathlib has **no notion of a differential ideal at all**: grep for
`differential ideal` returns nothing, and `radical.*differential` returns nothing. It has the
`Differential` class and Liouville's theorem on elementary integrals, and stops there.

**Generality: matches the literature exactly.** The `[Algebra ℚ A]` hypothesis is not a
convenience — the induction divides by `m+1` at every step. The literature calls a Δ-algebra
over ℚ a **Ritt algebra**, and it is precisely the hypothesis under which "the radical of a
differential ideal is differential" holds. (The strictly-more-general setting is a **Keigher
ring**, where the property is imposed as an axiom rather than proved; every Ritt algebra is a
Keigher ring. Generalising to Keigher rings would change the theorem into a definition, so it
is not a weakening.)

**Call sites: a real one.** [CharSetTac/RittRaudenbush.lean](CharSetTac/RittRaudenbush.lean)
proves the reduction half of Ritt–Raudenbush — every radical differential ideal has a finite
basis as soon as every prime one does — and it consumes `IsRadicalDiffIdeal`,
`radicalDiffIdeal`, `radicalDiffIdeal.le_of_subset`, `radicalDiffIdeal.isRadical` and
`radicalDiffIdeal_mul_le`. That is a named classical theorem depending on this API, not a
demonstration. It also shows the ℚ hypothesis is *not* needed for the reduction, only for
Ritt's lemma itself.

**⚠️ Open question — the one thing I could not settle.** This project states everything over
`Derivation R A A` rather than Mathlib's `Differential` class, because `Differential` fixes the
base to `ℤ` and therefore takes `Module ℤ` from `AddCommGroup.toIntModule`, while anything
built from an `Algebra` structure takes it from `Algebra.toModule` — **not definitionally
equal**. Everything produced by `Derivation.localization` lands on the wrong side of that
diamond, which is why `DiffPresheaf` was generalised over a base ring.

That reasoning is sound *for this project*. Whether Mathlib wants its differential-ideal API
phrased over `Derivation R A A` or over `Differential` is a maintainer's call, and it affects
candidates 1, 2 and 4 together. **Worth raising on Zulip before writing the PRs** — it is
cheaper than being asked to restate three files.

**Next action:** raise the `Derivation` vs `Differential` question on
`#mathlib4 > differential algebra`, then ship with candidate 1.

---

## 5. `TrivSqZeroExt.isUnit_of_isUnit_fst` — NO, Mathlib has it ✅ done

**Mathlib decl:** `TrivSqZeroExt.isUnit_iff_isUnit_fst`,
`Mathlib/Algebra/TrivSqZeroExt/Basic.lean`, sitting on a whole `Invertible` API
(`invertibleOfInvertibleFst`, `invertibleEquivInvertibleFst`, `isUnit_inl_iff`).

Mathlib's is **strictly more general** — arbitrary bimodule `[AddCommGroup M] [Semiring R]
[Module Rᵐᵒᵖ M] [Module R M] [SMulCommClass R Rᵐᵒᵖ M]` — where ours was only
`TrivSqZeroExt A A` over a `CommRing`. Ours is its `.mpr`.

*Why it was missed the first time:* the content lives in `Mathlib/Algebra/TrivSqZeroExt/Basic.lean`
(the directory), not the top-level `Mathlib/Algebra/TrivSqZeroExt.lean`, and a grep aimed at
the file rather than the directory comes back empty.

**Executed.** Deleted the 12-line lemma; the single call site
(`DerivationLocalization.lean`, `toDualLift_isUnit`) now reads
`TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr`. Full build clean.

---

## 6. `Derivation.toDualHom` / `TrivSqZeroExt.dualMap` — BORDERLINE

`CharSetTac/DerivationLocalization.lean:79` and `:104`. Both are `def`s used only as
scaffolding for candidate 2.

Mathlib has the machinery to express both, and I could not establish within this assessment
whether the composition is ≤3 lines or a genuine transport:
`derivationToSquareZeroEquivLift` (`Derivation R A I ≃ {lifts A →ₐ[R] B}` for square-zero
`I : Ideal B`), `TrivSqZeroExt.kerIdeal` + `kerIdeal_sq`, `TrivSqZeroExt.liftEquiv`, and
`DualNumber.lift`. Instantiating at `B = A[ε]`, `I = kerIdeal` should give `toDualHom` — but it
needs a `kerIdeal ≃ₗ A` transport that I did not verify compiles, so I am not claiming
NO-composable on a sketch I have not run.

Questions for you:

1. Should `toDualHom`/`dualMap` be upstreamed at all, or made `private` here and the
   `Derivation.localization` PR rewritten to go through `derivationToSquareZeroEquivLift`?
2. If the rewrite is wanted, is it worth doing *before* the PR (cleaner review, more work) or
   offering the dual-number proof and letting the reviewer decide?

My recommendation: make them `private`, ship candidate 2 with the dual-number proof, and let
the reviewer ask. The proof is short and the machinery is standard; pre-emptively rewriting it
through an equiv risks making it *less* readable for no mathematical gain.

---

## 7. `MvPolynomial.mapCoeffsDeriv` — YES, add as is

`CharSetTac/MapCoeffs.lean`. Kind: `def` (+ `mapCoeffsₗ`, `mapCoeffsFun`, four simp lemmas).

**The gap, named and verified.** Mathlib has exactly this for univariate polynomials —
`Derivation.mapCoeffs` in `Mathlib/RingTheory/Derivation/MapCoeffs.lean`, by Daniel Weber —
and nothing for `MvPolynomial`. Checked by reading the file: it is `Polynomial`-only, and its
construction routes through `PolynomialModule` (`PolynomialModule.map`,
`equivPolynomial.symm`), which has no multivariate counterpart.

So Mathlib currently has `MvPolynomial.mkDerivation` — the derivations *linear over the
coefficient ring*, which annihilate it — and no way to build the complementary ones. The two
together are what a derivation on a polynomial ring generally is.

**Why the construction is not a transliteration.** `MvPolynomial` does not unfold to `Finsupp`
at elaboration transparency (verified: `Finsupp.mapRange.linearMap` fails to unify even with
the index type supplied), so the obvious route is unavailable. It is built instead as a sum
over the support, with `mapCoeffsFun_eq_sum` — *the sum may be taken over any finite superset
of the support* — as the lemma the rest follows from. That lemma is arguably the reusable part.

**Consumers:** `Wu.DiffPolynomial.derivOver`, hence `ℚ[x]{y}` and every `x`-dependent example
in `WuDifferential/VariationalExamples.lean`.

**Proposed location** `Mathlib/RingTheory/Derivation/MapCoeffs.lean` (alongside the univariate
version) or a new `MvPolynomial` section there. PR title
`feat(RingTheory/Derivation): coefficientwise derivation on MvPolynomial`.

---

## 8. `MvPolynomial.IsHomogeneous.sum_X_mul_pderiv_of_vars_subset` — YES, add as is

`CharSetTac/EulerIdentity.lean`.

**The gap, named and verified.** Mathlib's Euler identity is

```lean
theorem IsHomogeneous.sum_X_mul_pderiv (h : φ.IsHomogeneous n) :
    ∑ i : σ, X i * pderiv i φ = n • φ
```

and `variable [Fintype σ]` is declared at `Mathlib/RingTheory/MvPolynomial/EulerIdentity.lean:55`,
immediately above it. `∑ i : σ` is `∑ i ∈ Finset.univ`, so the hypothesis is not incidental —
the statement cannot even be *written* without it.

That rules it out for any polynomial ring on an infinite index type, `R{y}` included. But the
mathematics does not need finiteness of `σ`: for a given `φ` only finitely many `pderiv i φ`
are nonzero, exactly the `i ∈ φ.vars`. The finiteness comes from the element, not the index.

The restatement sums over any `Finset` containing `vars`; **Mathlib's version is the special
case `s = univ`**, so this strictly generalises it and the existing lemma could be derived
from it in one line.

**Generality: maximally general.** No hypothesis to weaken — `[CommRing R]` could plausibly be
`[CommSemiring R]`, worth checking under `/generalise` before the PR.

**Consumers:** the graded homotopy `nsmul_eq_yy_mul_euler_add`, hence the converse to
`E ∘ D = 0`.

**Proposed location** `Mathlib/RingTheory/MvPolynomial/EulerIdentity.lean`, before the
`Fintype` section, with the existing result re-derived as a corollary. PR title
`feat(RingTheory/MvPolynomial): Euler's identity without Fintype`.

---

## Recommended order

1. **Candidate 3** (`map_ofNat`) — trivial, self-contained, establishes contact.
2. **Zulip question** on `Derivation` vs `Differential` (blocks 1, 2 and 4's framing).
3. **Candidate 2** (`Derivation.localization`) — the strongest: real gap, 3 consumers,
   classical statement.
4. **Candidates 1 + 4** together, after the Δ-generalisation — the differential-algebra layer.
5. **Candidates 7 + 8** — independent of the Zulip question, since neither mentions
   `Derivation` vs `Differential`, so they can go at any point. Candidate 8 is the smallest
   PR in the batch after candidate 3.
