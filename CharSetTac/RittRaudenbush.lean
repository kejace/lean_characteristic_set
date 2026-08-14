/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.RadicalDiffIdeal
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Order.Zorn

/-!
# Ritt–Raudenbush: the reduction to primes

`MATHLIBABLE_REPORT.md` records that `R{y}` has no consumer yet because "a theorem that isn't
written yet" is the one that needs it. This is the first half of that theorem.

## The statement

**Ritt–Raudenbush basis theorem.** If `R` is a Ritt algebra (a differential ring containing
`ℚ`) in which every radical differential ideal has a finite basis, then so does `R{y₁,…,yₙ}`.

Here "finite basis" means `I = {S}` for a finite `S` — generation as a *radical differential*
ideal, which is much weaker than generation as an ideal. `R{y}` is not Noetherian as a ring;
it has infinitely many indeterminates. The theorem is that it is Noetherian for this coarser
closure operator.

## What is proved here, and what is not

The classical proof has two halves:

1. **Reduction to primes** — every radical differential ideal has a finite basis as soon as
   every *prime* one does. This is `hasBasisProperty_of_prime` below, and it is proved.
2. **Primes have finite bases** — not proved here.

Half 1 is where the closure operator earns its keep, and it runs entirely on
`radicalDiffIdeal_mul_le` (`{S}·{T} ⊆ {S·T}`).

An earlier version of this docstring called half 2 "the characteristic-set argument", and
said the minimal-rank element is a characteristic set and the pseudo-division is `Wu.prem`.
**That was wrong**, and wrong in the expensive direction. Kaplansky's proof — the standard
one, reproduced in Sam's notes — needs no rankings, no characteristic sets, no Rosenfeld
lemma, and no descending-chain condition on autoreduced sets. It works with **one**
differential indeterminate at a time, using the rank `(ord, deg) ∈ ℕ ×ₗ ℕ`, and rests on a
single reduction lemma:

> **Ritt reduction.** For `α ∈ A{x}` and any `f`, there are `m, n` and a `g` of strictly
> smaller rank with `lc(α)^m · sep(α)^n · f − g ∈ [α]`.

plus the induction `R{y₁,…,y_n} ≅ (R{y₁,…,y_{n−1}}){y_n}`. The characteristic-set machinery
belongs to Rosenfeld–Gröbner decomposition, which is a different theorem. See `SCOPE.md` §3(e)
for the corrected route and cost.

## `ℚ` is not needed here

Ritt's lemma (the radical of a differential ideal is differential) needs a `ℚ`-algebra, and so
does the closure operator being computable as `√([S])`. But **the reduction to primes does
not** — it uses only that `{·}` is a radical-differential closure operator with
`{S}·{T} ⊆ {S·T}`, both of which hold over any commutative base. So the hypothesis is absent
from every statement below. Whether the *second* half survives without `ℚ` is a different
question, and the answer is no.
-/

open scoped Pointwise

namespace Wu

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d : Derivation R A A}

/-- A radical differential ideal **has a finite basis** when it is `{S}` for some finite `S`.

Deliberately *not* `Ideal.FG`: `R{y}` has infinitely many indeterminates and is not a
Noetherian ring, so ordinary finite generation is hopeless. Generation as a radical
differential ideal is the right finiteness notion, and it is the one Ritt–Raudenbush is
about. -/
def HasDiffBasis (d : Derivation R A A) (I : Ideal A) : Prop :=
  ∃ S : Set A, S.Finite ∧ I = radicalDiffIdeal d S

/-- The **basis property**: every radical differential ideal has a finite basis. This is the
conclusion of Ritt–Raudenbush, and also its hypothesis on the base ring. -/
def HasBasisProperty (d : Derivation R A A) : Prop :=
  ∀ I : Ideal A, IsRadicalDiffIdeal d I → HasDiffBasis d I

/-- `⊤` has a finite basis, namely `{1}`. Small, but it is what makes a maximal
counterexample proper, and hence eligible to be prime. -/
theorem hasDiffBasis_top : HasDiffBasis d (⊤ : Ideal A) := by
  refine ⟨{1}, Set.finite_singleton 1, ?_⟩
  symm
  rw [Ideal.eq_top_iff_one]
  exact radicalDiffIdeal.subset (Set.mem_singleton 1)

/-! ### Chains

Zorn needs an upper bound for every chain, and the bound is the supremum. Two facts make it
work: the supremum of a chain of radical differential ideals is again one, and a *finite* set
inside that supremum already fits inside a single member — which is what stops the supremum
from acquiring a finite basis that none of its members had. -/

section Chain

variable {c : Set (Ideal A)}

/-- **The supremum of a chain of radical differential ideals is a radical differential
ideal.** Both conditions are pointwise, and a chain is directed, so each witness can be found
in a single member. -/
theorem isRadicalDiffIdeal_sSup (hne : c.Nonempty) (hchain : IsChain (· ≤ ·) c)
    (h : ∀ I ∈ c, IsRadicalDiffIdeal d I) : IsRadicalDiffIdeal d (sSup c) := by
  have hdir : DirectedOn (· ≤ ·) c := hchain.directedOn
  constructor
  · rintro x ⟨n, hn⟩
    obtain ⟨I, hIc, hxI⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp hn
    exact le_sSup hIc ((h I hIc).1 ⟨n, hxI⟩)
  · intro x hx
    obtain ⟨I, hIc, hxI⟩ := (Submodule.mem_sSup_of_directed hne hdir).mp hx
    exact le_sSup hIc ((h I hIc).2 x hxI)

/-- **A finite subset of `sSup c` already sits inside one member of the chain.**

This is the crux of the Zorn step. Each element individually lands in some member; finiteness
plus the chain order lets those finitely many members be replaced by their largest. -/
theorem exists_mem_of_finite_subset_sSup (hne : c.Nonempty) (hchain : IsChain (· ≤ ·) c)
    {S : Set A} (hS : S.Finite) (hsub : S ⊆ ((sSup c : Ideal A) : Set A)) :
    ∃ I ∈ c, S ⊆ (I : Set A) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => obtain ⟨I, hI⟩ := hne; exact ⟨I, hI, by simp⟩
  | @insert a s ha _hs ih =>
      rw [Set.insert_subset_iff] at hsub
      obtain ⟨I₁, hI₁c, hsI₁⟩ := ih hsub.2
      obtain ⟨I₂, hI₂c, haI₂⟩ :=
        (Submodule.mem_sSup_of_directed hne hchain.directedOn).mp hsub.1
      -- replace the two members by whichever is larger
      rcases hchain.total hI₁c hI₂c with hle | hle
      · exact ⟨I₂, hI₂c, Set.insert_subset haI₂ (hsI₁.trans hle)⟩
      · exact ⟨I₁, hI₁c, Set.insert_subset (hle haI₂) hsI₁⟩

end Chain

/-! ### The maximal counterexample -/

/-- **Zorn.** If the basis property fails, there is a radical differential ideal that is
maximal among those without a finite basis.

The chain bound is the supremum, and the work is showing it is still a counterexample: if the
supremum had a finite basis `S`, then `S` would fit inside a single member `I` of the chain,
forcing `I = sSup c` and handing `I` the basis it was supposed to lack. -/
theorem exists_maximal_without_basis (h : ¬ HasBasisProperty d) :
    ∃ I, Maximal (fun J => IsRadicalDiffIdeal d J ∧ ¬ HasDiffBasis d J) I := by
  obtain ⟨I₀, hI₀rad, hI₀⟩ : ∃ I, IsRadicalDiffIdeal d I ∧ ¬ HasDiffBasis d I := by
    simpa [HasBasisProperty, not_forall] using h
  apply zorn_le₀
  intro c hcsub hchain
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨I₀, ⟨hI₀rad, hI₀⟩, by simp⟩
  refine ⟨sSup c, ⟨isRadicalDiffIdeal_sSup hne hchain fun I hI => (hcsub hI).1, ?_⟩,
    fun z hz => le_sSup hz⟩
  rintro ⟨S, hSfin, hEq⟩
  have hsub : S ⊆ ((sSup c : Ideal A) : Set A) := hEq ▸ radicalDiffIdeal.subset
  obtain ⟨I, hIc, hSI⟩ := exists_mem_of_finite_subset_sSup hne hchain hSfin hsub
  -- `I` contains the basis, hence contains the whole supremum, hence *is* it
  have hle : sSup c ≤ I := hEq ▸ radicalDiffIdeal.le_of_subset hSI (hcsub hIc).1
  exact (hcsub hIc).2 ⟨S, hSfin, le_antisymm (le_sSup hIc) hle |>.symm ▸ hEq⟩

/-- **A maximal radical differential ideal without a finite basis is prime.**

This is the heart of the reduction, and it is exactly where the product lemma is used. If
`ab ∈ I` with `a, b ∉ I`, then `{I, a}` and `{I, b}` both strictly contain `I`, so by
maximality both have finite bases `S₁, S₂`. Then

* `{S₁}·{S₂} ⊆ {(I ∪ {a})·(I ∪ {b})} ⊆ I`, since every one of those products is in `I` —
  the case `a·b` by hypothesis and the rest because `I` is an ideal; and
* conversely each `z ∈ I` lies in *both* `{I,a}` and `{I,b}`, so `z² ∈ {S₁}·{S₂} ⊆ {S₁S₂}`,
  and `{S₁S₂}` is radical, so `z ∈ {S₁S₂}`.

So `I = {S₁·S₂}` with `S₁·S₂` finite — the basis `I` was chosen not to have. -/
theorem isPrime_of_maximal_without_basis {I : Ideal A}
    (hmax : Maximal (fun J => IsRadicalDiffIdeal d J ∧ ¬ HasDiffBasis d J) I) :
    I.IsPrime := by
  obtain ⟨⟨hIrad, hInb⟩, hub⟩ := hmax
  constructor
  · rintro rfl; exact hInb hasDiffBasis_top
  intro x y hxy
  rcases Classical.em (x ∈ I) with hx | hx
  · exact Or.inl hx
  rcases Classical.em (y ∈ I) with hy | hy
  · exact Or.inr hy
  exfalso
  -- the two ideals obtained by adjoining `x` and `y`; both strictly contain `I`
  set J := radicalDiffIdeal d (insert x (I : Set A)) with hJ
  set K := radicalDiffIdeal d (insert y (I : Set A)) with hK
  have hIJ : I ≤ J := fun z hz => radicalDiffIdeal.subset (Set.mem_insert_of_mem _ hz)
  have hIK : I ≤ K := fun z hz => radicalDiffIdeal.subset (Set.mem_insert_of_mem _ hz)
  -- maximality: neither can be another counterexample, so both have finite bases
  have hJb : HasDiffBasis d J := by
    by_contra hb
    exact hx (hub ⟨radicalDiffIdeal.isRadicalDiffIdeal, hb⟩ hIJ
      (radicalDiffIdeal.subset (Set.mem_insert _ _)))
  have hKb : HasDiffBasis d K := by
    by_contra hb
    exact hy (hub ⟨radicalDiffIdeal.isRadicalDiffIdeal, hb⟩ hIK
      (radicalDiffIdeal.subset (Set.mem_insert _ _)))
  obtain ⟨S₁, hS₁fin, hS₁⟩ := hJb
  obtain ⟨S₂, hS₂fin, hS₂⟩ := hKb
  -- every product of a generator of `J` with one of `K` lands in `I`
  have hprod : J * K ≤ I := by
    refine le_trans radicalDiffIdeal_mul_le (radicalDiffIdeal.le_of_subset ?_ hIrad)
    rintro _ ⟨u, hu, v, hv, rfl⟩
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact hxy
      · exact Ideal.mul_mem_left _ _ hv
    · exact Ideal.mul_mem_right _ _ hu
  -- so `I` is generated by the finite set `S₁ * S₂`, which it was chosen not to be
  refine hInb ⟨S₁ * S₂, hS₁fin.mul hS₂fin, le_antisymm ?_ ?_⟩
  · intro z hz
    have hzz : z * z ∈ J * K := Ideal.mul_mem_mul (hIJ hz) (hIK hz)
    rw [hS₁, hS₂] at hzz
    exact radicalDiffIdeal.isRadical ⟨2, by rw [pow_two]; exact radicalDiffIdeal_mul_le hzz⟩
  · refine radicalDiffIdeal.le_of_subset ?_ hIrad
    rintro _ ⟨s, hs, t, ht, rfl⟩
    exact hprod (Ideal.mul_mem_mul (hS₁ ▸ radicalDiffIdeal.subset hs)
      (hS₂ ▸ radicalDiffIdeal.subset ht))

/-- **Ritt's reduction to primes.**

Every radical differential ideal has a finite basis as soon as every *prime* one does. This is
half of Ritt–Raudenbush; the other half — that primes in `R{y}` have finite bases — is the
characteristic-set argument, and is not proved here. -/
theorem hasBasisProperty_of_prime
    (hprime : ∀ P : Ideal A, IsRadicalDiffIdeal d P → P.IsPrime → HasDiffBasis d P) :
    HasBasisProperty d := by
  by_contra h
  obtain ⟨I, hmax⟩ := exists_maximal_without_basis h
  exact hmax.1.2 (hprime I hmax.1.1 (isPrime_of_maximal_without_basis hmax))

end Wu
