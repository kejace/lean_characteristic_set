/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DiffSpec

/-!
# Radical differential ideals

Item C step 1. The closure operator `{S}` — the smallest radical differential ideal
containing `S` — and its basic properties.

This is the object Ritt–Raudenbush is *about*: the theorem says every `{S}` is `{F}` for a
finite `F`. Nothing here proves that; this file only builds the operator and shows it
behaves like a closure, which is worth having on its own and is a prerequisite for anything
further.

Defined as an intersection rather than by an inductive construction. That makes the
universal property (`le_of_...`) free and the closure laws routine, at the cost of saying
nothing computational — which is the right trade here, since the computational content lives
in `Diff/Coherence.lean` and is fuel-bounded by design.
-/

namespace Wu

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {d : Derivation R A A}

/-- The radical differential ideals containing `S`. -/
def IsRadicalDiffIdeal (d : Derivation R A A) (I : Ideal A) : Prop :=
  I.IsRadical ∧ IsDiffIdeal d I

/-- **`{S}`**: the smallest radical differential ideal containing `S`. -/
def radicalDiffIdeal (d : Derivation R A A) (S : Set A) : Ideal A :=
  sInf {I : Ideal A | S ⊆ (I : Set A) ∧ IsRadicalDiffIdeal d I}

namespace radicalDiffIdeal

variable {S T : Set A}

theorem mem_iff {x : A} :
    x ∈ radicalDiffIdeal d S ↔
      ∀ I : Ideal A, S ⊆ (I : Set A) → IsRadicalDiffIdeal d I → x ∈ I := by
  simp [radicalDiffIdeal, Submodule.mem_sInf, IsRadicalDiffIdeal]

/-- The universal property: `{S}` is below any radical differential ideal containing `S`. -/
theorem le_of_subset {I : Ideal A} (hS : S ⊆ (I : Set A)) (hI : IsRadicalDiffIdeal d I) :
    radicalDiffIdeal d S ≤ I :=
  sInf_le ⟨hS, hI⟩

theorem subset : S ⊆ (radicalDiffIdeal d S : Set A) := fun _ hx =>
  mem_iff.mpr fun _ hI _ => hI hx

/-- `{S}` is differential: an intersection of differential ideals is differential. -/
theorem isDiffIdeal : IsDiffIdeal d (radicalDiffIdeal d S) := by
  intro x hx
  rw [mem_iff] at hx ⊢
  exact fun I hSI hI => hI.2 _ (hx I hSI hI)

/-- `{S}` is radical: an intersection of radical ideals is radical. -/
theorem isRadical : (radicalDiffIdeal d S).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [mem_iff] at hn ⊢
  exact fun I hSI hI => hI.1 ⟨n, hn I hSI hI⟩

theorem isRadicalDiffIdeal : IsRadicalDiffIdeal d (radicalDiffIdeal d S) :=
  ⟨isRadical, isDiffIdeal⟩

theorem mono (h : S ⊆ T) : radicalDiffIdeal d S ≤ radicalDiffIdeal d T :=
  le_of_subset (h.trans subset) isRadicalDiffIdeal

/-- Idempotence, the remaining closure law. -/
@[simp] theorem idem :
    radicalDiffIdeal d (radicalDiffIdeal d S : Set A) = radicalDiffIdeal d S :=
  le_antisymm (le_of_subset le_rfl isRadicalDiffIdeal) (mono subset)

/-- A radical differential ideal is its own closure. -/
theorem eq_self_of_isRadicalDiffIdeal {I : Ideal A} (hI : IsRadicalDiffIdeal d I) :
    radicalDiffIdeal d (I : Set A) = I :=
  le_antisymm (le_of_subset le_rfl hI) subset

end radicalDiffIdeal

/-! ### Ritt's lemma

**The radical of a differential ideal is differential**, in a `ℚ`-algebra. This is what makes
`{S}` computable as `√([S])`, and it is the step everything else in Item C rests on.

The classical proof is an induction that peels one power of `a` off while adding two powers
of `da`. Stated as `step` below, which is the whole content: the exponent `m+1` is *always*
nonzero, so there is no case analysis on whether the coefficient can be divided out — that
is why this indexing is preferable to the textbook `a^(n-k)(da)^(2k-1)`.

`ℚ` is not decoration. The induction divides by `m+1` at every stage, and in
characteristic `p` the lemma is false. -/

section Ritt

variable [Algebra ℚ A] {I : Ideal A}

/-- A natural number is invertible in a `ℚ`-algebra. -/
private theorem isUnit_natCast_succ (m : ℕ) : IsUnit ((m : A) + 1) := by
  have : ((m : A) + 1) = algebraMap ℚ A ((m : ℚ) + 1) := by push_cast; ring
  rw [this]
  exact (IsUnit.map _ (isUnit_iff_ne_zero.mpr (by positivity)))

/-- Cancel an invertible natural coefficient from an ideal membership. -/
private theorem mem_of_natCast_succ_mul {x : A} {m : ℕ}
    (h : ((m : A) + 1) * x ∈ I) : x ∈ I := by
  obtain ⟨u, hu⟩ := isUnit_natCast_succ (A := A) m
  have h2 : (↑u⁻¹ : A) * (((m : A) + 1) * x) ∈ I := Ideal.mul_mem_left I _ h
  rw [← hu, ← mul_assoc, u.inv_mul, one_mul] at h2
  exact h2

/-- **The inductive step.** One power of `a` traded for two of `da`.

The coefficient that has to be divided out is `m+1`, never zero — which is why this
indexing beats the textbook `a^(n-k)(da)^(2k-1)`, where the coefficient is `n-k` and the
top of the range needs separate treatment. -/
theorem IsDiffIdeal.step (hI : IsDiffIdeal d I) (a : A) (m k : ℕ)
    (h : a ^ (m + 1) * (d a) ^ k ∈ I) : a ^ m * (d a) ^ (k + 2) ∈ I := by
  have h1 : d (a ^ (m + 1) * (d a) ^ k) ∈ I := hI _ h
  rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow] at h1
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel] at h1
  have h2 := Ideal.mul_mem_right (d a) I h1
  -- the `d (d a)` term is a multiple of the hypothesis, so it can be subtracted off
  have hT : ((k : A) * d (d a)) * (a ^ (m + 1) * (d a) ^ k) ∈ I :=
    Ideal.mul_mem_left I _ h
  refine mem_of_natCast_succ_mul (m := m) ?_
  have hsub := Ideal.sub_mem I h2 hT
  convert hsub using 1
  -- the ring identity, which needs `(da)^(k-1) · da = (da)^k`; split on `k` to get it
  rcases k with _ | j
  · simp
    push_cast
    ring
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring
/-- Iterating the step: every `j` trades another power of `a` for two of `da`.

Stated for *all* `j`, with no bound. Past `j = n` the exponent `n - j` saturates at zero by
natural subtraction and the statement stays true for a different reason — the ideal absorbs
further powers of `da` — so no side condition is needed. -/
theorem IsDiffIdeal.iterate (hI : IsDiffIdeal d I) (a : A) (n : ℕ) (ha : a ^ n ∈ I) :
    ∀ j, a ^ (n - j) * (d a) ^ (2 * j) ∈ I := by
  intro j
  induction j with
  | zero => simpa using ha
  | succ j ih =>
      rcases Nat.eq_zero_or_pos (n - j) with h0 | hpos
      · -- past the top: absorb two more powers of `d a`
        have hnj : n - (j + 1) = 0 := by omega
        rw [h0, pow_zero, one_mul] at ih
        rw [hnj, pow_zero, one_mul, show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
        exact Ideal.mul_mem_right _ _ ih
      · obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
        rw [hm] at ih
        have key := hI.step a m (2 * j) ih
        rw [show n - (j + 1) = m by omega, show 2 * (j + 1) = 2 * j + 2 by ring]
        exact key

/-- **Ritt's lemma: the radical of a differential ideal is differential.**

Take `a` with `a ^ n ∈ I` and run the iteration to `j = n`: the powers of `a` are exhausted
and `(d a) ^ (2n) ∈ I`, so `d a` is in the radical.

False in characteristic `p` — the induction divides by `m + 1` at every stage. -/
theorem IsDiffIdeal.radical (hI : IsDiffIdeal d I) : IsDiffIdeal d I.radical := by
  intro a ha
  obtain ⟨n, hn⟩ := ha
  exact ⟨2 * n, by simpa using hI.iterate a n hn n⟩

/-- Consequently `{S}` is just the radical of the differential ideal generated by `S`. -/
theorem radicalDiffIdeal_eq_radical (S : Set A) (J : Ideal A)
    (hJ : IsDiffIdeal d J) (hSJ : S ⊆ (J : Set A))
    (hmin : ∀ K : Ideal A, S ⊆ (K : Set A) → IsDiffIdeal d K → J ≤ K) :
    radicalDiffIdeal d S = J.radical := by
  refine le_antisymm (radicalDiffIdeal.le_of_subset ?_ ⟨Ideal.radical_isRadical J, hJ.radical⟩) ?_
  · exact hSJ.trans Ideal.le_radical
  · have hJK : J ≤ radicalDiffIdeal d S :=
      hmin _ radicalDiffIdeal.subset radicalDiffIdeal.isDiffIdeal
    exact (Ideal.radical_mono hJK).trans radicalDiffIdeal.isRadical

end Ritt

end Wu
