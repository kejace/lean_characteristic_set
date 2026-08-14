# Plan: ranking-driven prolongation, differential Spec, Ritt–Raudenbush

A plan for the three gaps between where this repo is and differential schemes. It is
deliberately shaped against the failure mode of `NEXT_LEVEL.md`, which aimed at the right
target and assumed a substrate that does not exist. **Every prerequisite claim below was
checked against the pinned Mathlib (v4.33.0) and against this repo, and the checks are
recorded.**

## The shape of the argument

Three items, in dependency order. They are not equal:

| | risk | buys | needed for a working tactic? |
|---|---|---|---|
| **A. Ranking-driven prolongation** | low | PDE systems past first order | yes — the current limit is visible today |
| **B. Differential Spec** | medium | `DiffPresheaf` constructed, not assumed | no |
| **C. Ritt–Raudenbush** | high | unconditional termination; Spec well-behaved | no |

Item A is engine work with a falsifiable gate that exists *right now*. Item B is a bounded
build on one missing lemma. Item C is the research risk, and it is last because nothing
else depends on it and its practical benefit is smaller than it looks.

**The tactic is useful today without any of this.** This plan is about the D-scheme goal,
not about making `wu` work.

---

## Item A — Ranking-driven prolongation

### The problem, as observed

`wu_pde` proves both Cauchy–Riemann equations for `z ↦ z²`. It does **not** prove
harmonicity `∂₁∂₁u + ∂₂∂₂u = 0` for the same `u`, at `(order := 2)`, restricted or not.
See `CharSetTac/DiffPdeTest.lean`, where the failure is recorded rather than hidden.

The cause is structural. With one derivation, prolonging everything is cheap: derivatives
of a quantity are totally ordered, so each round adds one equation per hypothesis and the
chain stays triangular. With two derivations, uniform prolongation to order `k` generates
every mixed partial of everything — mostly irrelevant — and the *algebraic* basic set has
no way to tell which equations matter. Restricting the prolongation does not help either:
the coordinate facts then go unprolonged and `∂₁∂₁x` becomes a free atom.

Both failures are one failure: **which prolongations to take is a ranking decision, and the
current tactic does not make it.**

### What exists

- `Diff/Ranking.lean` — `DiffAtom`, `Ranking`, `AtomTable`
- `Diff/MultiIndex.lean` — `MDiffAtom`, `MRanking` (orderly / elimination), `MAtomTable`,
  `Poly.leaderM`, `derivInM`, `derivM`, `isCriticalPair`, `lcm`, `quotient?`, `deltaPoly`
- `Diff/Derivation.lean` — `separant`, `partiallyReduced`
- `Diff/Reduce.lean` — `DTracked`, `DReduction`, `drem`, `dremSet` (single derivation)
- `Diff/Coherence.lean` — `remBy`, `deltaRemainders`, `isCoherent`, `completeCoherent`

That is most of the parts. What is missing is the *strategy* that uses them.

### The work

1. **Demand-driven prolongation.** To reduce `g` by `f`, if `leader(g)` is a proper
   derivative `θ·leader(f)`, prolong `f` by exactly `θ` — not to a uniform order. This is
   the single change that fixes the observed failure: prolongations become a function of
   the goal instead of a fixed budget.
2. **Differential pseudo-division, multi-index.** `I^a S^b f = q·g + r`, multiplying by both
   initial and separant. `Diff/Reduce.lean` has this for one derivation; lift it to
   `MAtomTable`.
3. **Autoreduced differential chains.** A differential analogue of `basicSet`: minimal
   under the ranking, pairwise partially reduced.
4. **Wire in coherence.** `completeCoherent` already computes Δ-remainders; the chain
   algorithm should consume them, adding non-vanishing ones as new relations.
5. **Cofactor tracking throughout**, so the certificate architecture is preserved. This is
   non-negotiable: the oracle stays untrusted and `ring1` stays the checker.

### Gate — passed, but not for the reason predicted

**Status: done.** `wu_pde!` in `CharSetTac/DiffDemand.lean`, tests in `DiffDemandTest.lean`.

The gate was harmonicity at second order. It passes — but the diagnosis above was **wrong**,
and that is worth keeping rather than editing away. The blocker was not prolongation
strategy at all: it was two missing simp lemmas leaving `d 1` and `d 2` alive as spurious
atoms, quietly corrupting the characteristic set. With those fixed, *uniform* prolongation
proves harmonicity too — and so does the logistic equation, recorded much earlier in this
project as a limit of `wu_diff` and never actually one.

Demand-driven prolongation survives on measured merit instead:

```
wu_pde  (order := 2)   52027 heartbeats     30-odd equations generated
wu_pde!                 4208                six
```

12×, and the gap widens with derivations and order. So it decides what stays tractable,
even though it decided nothing on the gate it was built for.

**Still open:** `d₁(d₁(d₁ u)) = 0` for a quadratic `u` does not close; the closure saturates
at 18 hypotheses at any depth. Undiagnosed, and flagged as undiagnosed — the two previous
"limits" in this project both turned out to be bugs with confident wrong explanations
attached.

### Risk and abandon condition

Low risk — no new mathematics, no Mathlib dependency, and the pieces exist. The realistic
failure is expression swell, which is measurable.

**Abandon if:** demand-driven prolongation still cannot do harmonicity after the chain
algorithm lands. That would mean the problem is not prolongation choice but the algebraic
reduction itself, and the diagnosis above is wrong.

---

## Item B — Differential Spec

### The linchpin, and it is missing

`Spec^Δ(R)` needs the structure sheaf to carry a derivation, which needs:

> **A derivation on `R` extends uniquely to any localization `S⁻¹R`**, by the quotient rule
> `d(a/s) = (s·da − a·ds)/s²`.

**Mathlib does not have this.** Checked: no `Derivation` × `Localization` interaction
anywhere; `Mathlib/RingTheory/Derivation/` is five files and none mentions
`IsLocalization`; the only lifting results are `liftOfRightInverse` and `liftOfSurjective`
(`Derivation/Basic.lean:393,414`), neither of which applies. `Mathlib/RingTheory/Kaehler/`
touches localization but only through `TensorProduct`.

That single lemma is the whole difficulty of item B, and it is classical and bounded.

### The work

1. **`Derivation.localization`** — extend `d : Derivation R A A` to `Derivation R S⁻¹A S⁻¹A`,
   with uniqueness. Well-definedness is the real content: independence of the representative
   `a/s`. **This is the piece to attempt first, alone, before anything else in item B** —
   if it resists, the rest does not start.
2. **Prime differential ideals.** A differential ideal that is prime. Show the differential
   spectrum is a subspace of `Spec`, with the induced Zariski topology.
3. **Structure sheaf.** `Spec^Δ(R)` with `𝒪(D(f)) = R_f` carrying the localized derivation.
   `restrict_deriv` — the axiom our `DiffPresheaf` currently *assumes* — becomes a theorem,
   because localization maps commute with the extended derivation by construction.
4. **Discharge `DiffPresheaf`.** `CharSetTac/DiffSheaf.lean` currently postulates the
   structure. After (3) it has an instance, and `IsSeparated`, `glue_zero`, `glue_eq` apply
   to something real.

### Gate

**Step 1 is done.** `CharSetTac/DerivationLocalization.lean`. `Derivation.localization`
extends any `d : Derivation R A A` to `Derivation R B B` for `B` a localization of `A`,
with `localization_algebraMap` (it restricts to `d`) and `localization_mk'` (the quotient
rule `s²·d(a/s) = s·da - a·ds`, so it is demonstrably the intended map). Axioms clean.

The dual-number route worked as designed: no representative was ever named, and
`IsLocalization.lift` supplied well-definedness. The supporting pieces —
`TrivSqZeroExt.isUnit_of_isUnit_fst`, `Derivation.toDualHom`, `TrivSqZeroExt.dualMap` —
are all general-purpose and sit in root namespaces for upstreaming.

**Item B is done.** All four steps, in the reordered sequence 1 → 3 → 4 → 2:

| | |
|---|---|
| `Derivation.localization` | `d` extends to any localization, via dual numbers |
| `stalkDeriv`, `stalkDeriv_mk` | ... hence to every stalk; a fraction goes to a fraction |
| `sectionDeriv_mem` | `isLocallyFraction` survives |
| `sheafDeriv`, `specDiffPresheaf` | **`restrict_deriv` proved, by `rfl`** |
| `IsDiffIdeal`, `DiffPrimeSpectrum` | the differential spectrum as a subspace |

The gate — a concrete construction instantiating `DiffPresheaf` with `restrict_deriv` proved
rather than assumed — is met.

**The estimate in this plan was wrong about where the cost was.** It called B "medium risk,
one classical lemma". The lemma was the easy part; essentially all the effort went into
Mathlib's instance and defeq layer: the `LocalizedModule`/`IsLocalization` spelling gap, a
`Module ℤ` diamond that forced `DiffPresheaf` to be generalised over a base ring, `Algebra R`
missing on sections, and a `whnf` blowup that only cleared once the pointwise ring lemmas
were established *first*. The mathematical content of the whole item is about fifteen lines.

### Risk

Medium. Step 1 is classical but fiddly; steps 2–4 are routine once it lands. The honest
risk is that Mathlib's `Localization` API makes well-definedness more painful than the
mathematics suggests.

**Abandon if:** step 1 is not done in a bounded attempt. Everything downstream is
worthless without it, so it is a clean stop.

---

## Item C — Ritt–Raudenbush

### What it says, and what it actually buys

In a Ritt algebra (a ℚ-algebra with commuting derivations), every radical differential ideal
is generated as a radical differential ideal by a *finite* set. Equivalently: ACC on radical
differential ideals — the differential Hilbert basis theorem.

Be precise about the payoff, because it is smaller than it sounds:

- **Termination of `completeCoherent`.** Currently fuel-bounded. That is *sound* — exhausting
  fuel returns the set reached and `isCoherent` reports it as incomplete, so a caller cannot
  mistake a timeout for a result. Ritt–Raudenbush would make it unconditional. Nice, not
  load-bearing.
- **The differential spectrum being Noetherian-ish**, so decomposition into irreducible
  components is finite. *This* is the real reason to want it, and it is a property of item B
  rather than of the tactic.

Nothing in the tactic is unsound without it.

### What exists

Nothing, in either library. Checked: no radical or perfect differential ideals, no Ritt, no
Kolchin, anywhere in Mathlib — and the TauCeti survey earlier in this project found the same
(zero differential algebra of any kind). We have `diffIdeal`, `sat`, and
`sat_diffIdeal_deriv_mem` in `CharSetTac/DiffIdeal.lean`, which is the beginning of the
first bullet below and nothing more.

### The work, decomposed so partial progress is worth having

1. **The radical differential ideal `{S}` as a closure operator.** Definition, monotonicity,
   idempotence, `{S}` is radical and differential. Routine; extends `DiffIdeal.lean`.
2. **The product lemma — the mathematical heart.**
   `{S}·{T} ⊆ {S·T}`, where `S·T = {st | s ∈ S, t ∈ T}`. This is where the ℚ-algebra
   hypothesis is used (the induction needs to divide by integers) and it is the step that
   makes everything else go. **Attempt this second, on its own.**
3. **Ritt–Raudenbush proper**, by Noetherian induction on a maximal counterexample, using
   (2) to split a non-prime perfect ideal.
4. **Consequences:** ACC; `completeCoherent` termination unconditional; finite decomposition
   into characteristic-set components.

### Gate — steps 1 and 2 done, and step 2 turned out to be a different lemma

`CharSetTac/RadicalDiffIdeal.lean`.

**Step 1 done.** `radicalDiffIdeal` as an intersection, with the closure laws
(`subset`, `mono`, `idem`, the universal property) and `{S}` shown radical and differential.

**Step 2 done, but not the lemma the plan named.** The plan called the product lemma
`{S}·{T} ⊆ {S·T}` "the mathematical heart". On working through it, the more fundamental
statement is **Ritt's lemma** — the radical of a differential ideal is differential — which
is what makes `{S} = √([S])` and what the product lemma itself would be proved from. That is
what is formalised: `IsDiffIdeal.radical`, via `IsDiffIdeal.step` and `IsDiffIdeal.iterate`.

The indexing matters and is worth recording. The textbook induction produces
`a^(n-k)·(da)^(2k-1)` and divides by `n - k`, which needs a side condition at the top of the
range. Restating the step as

    a^(m+1) · (da)^k ∈ I  →  a^m · (da)^(k+2) ∈ I

divides by `m + 1`, which is *never* zero, so there is no case analysis at all. The
`ℚ`-algebra hypothesis is exactly this division, and in characteristic `p` the lemma is
false.

**Steps 3 and 4 remain**: the product lemma, then Ritt–Raudenbush by Noetherian induction,
then removing fuel from `completeCoherent`. Step 3 is now the only thing standing between
here and the basis theorem.

### Risk

High, and this is the item most likely to be abandoned. Step 2 is a genuine
research-formalisation task — the classical proofs are slick on paper and typically
unpleasant in a proof assistant.

**Abandon if:** step 2 does not land in a bounded attempt. Steps 1 and 4 are still worth
having on their own; step 3 without step 2 is not attemptable.

---

## What this plan deliberately does not do

- **No operads, dioperads, or props.** Mathlib has *zero* — two bibliography citations and
  no definitions. Building that substrate is three theses before any of it touches a goal.
- **No categorified Gröbner bases.** The efficiency claim motivating them was measured
  (`CharSetTac/BenchChecking.lean`): compact representation is worth ~2×, and cost still
  tracks the normal form regardless, because `ring1` must expand to verify. A constant
  factor is a poor return on new foundations. If someone wants to revisit it, the file
  records what would change the answer.
- **No Gröbner basis implementation.** Mathlib has no `GroebnerBasis`, no Buchberger, no
  termination proof. Wu's method does not need one, which is precisely why this repo works.
- **No factored-cofactor emission.** Measured at ~2×, but it does not compose with
  `cancelCommonFactors` (6.3× and 12× on our two hard cases), which needs cofactors
  expanded. Recorded, with the condition that would revive it.

## Verification discipline

The rules this project has actually been run under, and the reason the findings above are
trustworthy:

1. **Check the substrate before planning on it.** Every "Mathlib has X" claim here was
   grepped. NEXT_LEVEL's Phase A–D assumed operads, Gröbner bases and sheaf descent that do
   not exist in usable form.
2. **Measure before optimising.** Two assumptions died this way: coefficient swell was *not*
   the engine bottleneck (term count was), and the certificate-size fix that mattered was
   factor cancellation, not representation.
3. **Force synchronous elaboration when timing.** `Elab.async` makes `#wu_bench` and
   `#count_heartbeats` report the *signature* cost. It reported 15 ms for a 41-second proof.
4. **Record limits as limits.** The logistic equation, Desargues before the reformulation,
   harmonicity at order 2 — each is in the source as a documented failure. They are the
   evidence base for what to build next.
5. **Keep the oracle untrusted.** Every extension keeps cofactor tracking and `ring1` as the
   checker. A bug in new engine code must fail the tactic, never produce an unsound proof.

## Ordering, and the honest recommendation

**Do A. Then decide about B. Treat C as optional.**

A is low-risk engine work with a falsifiable gate that exists today, and it is the only one
of the three that improves the tactic. B is worth doing if differential schemes are the
actual goal, and its risk concentrates in one classical lemma that can be attempted in
isolation. C is a research project whose practical benefit is a termination proof for
something that is already sound under a fuel bound.

If only one gets done, it should be A — and the reason is that the gate for it is a test
that fails right now.
