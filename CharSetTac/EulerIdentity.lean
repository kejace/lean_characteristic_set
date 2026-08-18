/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Euler's identity without a finite index type

Mathlib's `MvPolynomial.IsHomogeneous.sum_X_mul_pderiv` reads

```
  ∑ i : σ, X i * pderiv i φ = n • φ
```

and `∑ i : σ` means `∑ i ∈ Finset.univ`, so the statement needs `[Fintype σ]`. That rules it
out here: `R{y} = MvPolynomial (σ × ℕ) R` is indexed by `σ × ℕ`, which is infinite.

The mathematics is unaffected. For a *given* `φ` only finitely many `pderiv i φ` are nonzero
— exactly the `i ∈ φ.vars` — so the sum is genuinely finite; the finiteness comes from `φ`,
not from `σ`. Restating it over a `Finset` containing `vars` is therefore the honest form,
and Mathlib's version is the special case `s = univ`.

This is the general lesson in `R{y}`, and it has already bitten twice elsewhere: **finiteness
always comes from the element, never from the index type.** The Euler operator's alternating
sum terminates only because a polynomial has finite `order`, and upstream's own
`WellFoundedLT (TriangularSet σ R)` instance needs `[Finite σ]` for the same reason.

Needed for the converse to `E ∘ D = 0` — see `SCOPE.md` §3(a).
-/

namespace MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- Euler's identity on a monomial, summed over any superset of its support. -/
theorem sum_X_mul_pderiv_monomial (s : Finset σ) (m : σ →₀ ℕ) (a : R)
    (hm : m.support ⊆ s) :
    ∑ i ∈ s, X i * pderiv i (monomial m a) = m.degree • monomial m a := by
  simp only [X_mul_pderiv_monomial, ← Finset.sum_smul]
  congr 1
  rw [Finsupp.degree]
  exact (Finset.sum_subset hm fun i _ hi => by
    simpa using Finsupp.notMem_support_iff.mp hi).symm

/-- **Euler's identity, with the finiteness coming from `φ` rather than from `σ`.**

Mathlib's `IsHomogeneous.sum_X_mul_pderiv` is the case `s = Finset.univ`; this form applies
when `σ` is infinite, which is the case for a differential polynomial ring. -/
theorem IsHomogeneous.sum_X_mul_pderiv_of_vars_subset {φ : MvPolynomial σ R} {n : ℕ}
    {s : Finset σ} (hs : φ.vars ⊆ s) (h : φ.IsHomogeneous n) :
    ∑ i ∈ s, X i * pderiv i φ = n • φ := by
  conv_lhs => rw [φ.as_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [φ.as_sum]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [sum_X_mul_pderiv_monomial s m _
    (fun i hi => hs (support_subset_vars_of_mem_support hm hi))]
  congr 1
  rw [Finsupp.degree_eq_weight_one]
  exact h (mem_support_iff.mp hm)

end MvPolynomial
