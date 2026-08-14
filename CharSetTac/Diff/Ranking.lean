/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.CharSet

/-!
# Ranked derivative atoms for differential Wu–Ritt

The engine works on flat variable indices. This file is the layer that gives those indices
*derivative* meaning: atom `n` denotes the `order`-th derivative of differential
indeterminate `indet`.

## Scope: one derivation

`DiffAtom` carries a single `order : ℕ`, i.e. the **ordinary** case, one derivation. That
is deliberate and it is not merely a simplification:

Critical pairs — the things coherence is about — need two chain elements whose leading
derivatives are derivatives of a *common* differential indeterminate. With one derivation
that cannot happen in a pairwise partially reduced triangular set: if `ld p₁ = δᵃu` and
`ld p₂ = δᵇu` with `a < b`, then `p₂` contains a proper derivative of `p₁`'s leader, so it
is not partially reduced with respect to `p₁`. One element per indeterminate means no
critical pairs, so coherence holds vacuously and none of the Rosenfeld machinery arises.
Boulier et al. flag exactly this by introducing critical pairs with "in the partial case".

Generalising to several derivations means replacing `order : ℕ` with a multi-index
`α : ℕ^m` and adding critical pairs; the rest of this file is unaffected.

## Why index assignment is not incremental

The engine reads the *largest* index in a polynomial as its main variable, so indices must
be assigned consistently with the ranking. They cannot be handed out as derivatives are
discovered: under an orderly ranking `y′ > z` even though `y < z`, so appending `y′` after
`z` would invert the order. The closure of needed derivatives is therefore computed first,
sorted by the ranking, and only then numbered.
-/

namespace Wu

/-- A derivative of a differential indeterminate: `δ^order (y_indet)`, for a single
derivation. -/
structure DiffAtom where
  /-- Which differential indeterminate. -/
  indet : Nat
  /-- How many times it has been differentiated. -/
  order : Nat
  deriving DecidableEq, Repr, Inhabited, BEq, Hashable

namespace DiffAtom

/-- The derivative of this atom. -/
def deriv (a : DiffAtom) : DiffAtom := { a with order := a.order + 1 }

/-- `a` is a proper derivative of `b`: same indeterminate, strictly higher order. -/
def isProperDerivOf (a b : DiffAtom) : Bool :=
  a.indet == b.indet && b.order < a.order

end DiffAtom

/-- Which ranking to use.

A ranking is a total order on derivatives with `θv ≥ v` and `v ≥ w → θv ≥ θw`. Both
choices below satisfy that; they differ in what they eliminate. -/
inductive Ranking
  /-- Order first, then indeterminate. Keeps degrees balanced; the default. -/
  | orderly
  /-- Indeterminate first, then order: eliminates higher-indexed indeterminates
  completely, which is what produces input–output relations. -/
  | elimination
  deriving Inhabited, BEq, Repr

namespace Ranking

/-- Compare two derivative atoms under this ranking. -/
def cmp : Ranking → DiffAtom → DiffAtom → Ordering
  | .orderly, a, b =>
    match compare a.order b.order with
    | .eq => compare a.indet b.indet
    | o => o
  | .elimination, a, b =>
    match compare a.indet b.indet with
    | .eq => compare a.order b.order
    | o => o

end Ranking

/-- The correspondence between engine variable indices and derivative atoms.

`toAtom` is indexed by engine variable number and is sorted increasingly under the
ranking, so a larger engine index really is a higher-ranked derivative. -/
structure AtomTable where
  /-- Engine index → derivative atom, sorted increasingly by the ranking. -/
  toAtom : Array DiffAtom
  /-- The ranking used to sort. -/
  ranking : Ranking
  deriving Inhabited

namespace AtomTable

/-- Engine index of a derivative atom, if present. -/
def index? (t : AtomTable) (a : DiffAtom) : Option Nat :=
  t.toAtom.findIdx? (· == a)

/-- Build a table from the derivatives that will be needed, sorted by the ranking.

Pass the *closure*: every derivative that any prolongation might introduce. Assigning
indices after sorting is what keeps "largest index" and "highest ranked" the same thing. -/
def build (ranking : Ranking) (atoms : Array DiffAtom) : AtomTable :=
  let deduped := atoms.foldl (init := (#[] : Array DiffAtom)) fun acc a =>
    if acc.any (· == a) then acc else acc.push a
  { toAtom := deduped.qsort fun a b => ranking.cmp a b == .lt, ranking := ranking }

/-- The closure of `atoms` under differentiation, up to `maxOrder` total order.

This is what must be known before indices are assigned. -/
def closure (atoms : Array DiffAtom) (maxOrder : Nat) : Array DiffAtom :=
  atoms.foldl (init := (#[] : Array DiffAtom)) fun acc a =>
    (Array.range (maxOrder + 1)).foldl (init := acc) fun acc k =>
      let d : DiffAtom := { a with order := a.order + k }
      if acc.any (· == d) then acc else acc.push d

end AtomTable
end Wu
