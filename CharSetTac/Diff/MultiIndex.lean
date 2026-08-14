/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Diff.Reduce

/-!
# Several derivations: multi-index derivatives and Δ-polynomials

Generalises `DiffAtom` from a single `order : ℕ` to a multi-index `α : ℕᵐ`, one exponent
per derivation. This is what PDE systems need — Gauss–Codazzi lives in two surface
parameters — and it is where coherence stops being automatic.

## What changes, and what does not

The certificate is unchanged in shape:

```
H · g = ∑ⱼ ∑_θ c_{j,θ} · θ(Aⱼ)
```

only now `θ` ranges over multi-indices. Soundness still needs one fact — `Aⱼ = 0` implies
`θ(Aⱼ) = 0` for any composition of derivations — and `ring` still checks the identity with
derivatives as atoms. **No Rosenfeld's lemma, in one derivation or many.**

## Critical pairs

With one derivation, a pairwise partially reduced triangular set has no critical pairs:
two elements with leaders `δᵃu` and `δᵇu` would have one containing a proper derivative of
the other's leader. With several derivations that argument fails — `δ₁u` and `δ₂u` are
incomparable, neither is a derivative of the other, yet `δ₂δ₁u = δ₁δ₂u` is a common
derivative. That is a critical pair, and the Δ-polynomial

```
Δ(p₁, p₂) = s₂ · (θ₁₂/θ₁)(p₁) − s₁ · (θ₁₂/θ₂)(p₂),   θ₁₂ = lcm(θ₁, θ₂)
```

(with `sᵢ` the separants) is what must reduce to zero for the set to be *coherent*.

**Coherence is used here as an algorithm, not proved as a theorem.** Δ-polynomials tell
the engine what to reduce next, exactly as Buchberger's criterion tells a Gröbner engine
what to consider — and nobody formalises Buchberger's criterion in order to *use* a
Gröbner oracle. Skipping or approximating the completion costs completeness (the engine
may fail to find a certificate that exists); it can never cost soundness, because the
certificate is checked regardless.
-/

namespace Wu

/-- A derivative under several derivations: `δ^α (y_indet)` with `α` a multi-index, one
exponent per derivation. -/
structure MDiffAtom where
  /-- Which differential indeterminate. -/
  indet : Nat
  /-- Exponent per derivation; trailing zeros are insignificant. -/
  order : Array Nat
  deriving Repr, Inhabited

namespace MDiffAtom

/-- Exponent in derivation `i`. -/
def exp (a : MDiffAtom) (i : Nat) : Nat := a.order.getD i 0

/-- Total order of differentiation. -/
def total (a : MDiffAtom) : Nat := a.order.foldl (· + ·) 0

/-- Equality up to trailing zeros in the multi-index. -/
def beq (a b : MDiffAtom) : Bool :=
  a.indet == b.indet &&
    (Array.range (max a.order.size b.order.size)).all fun i => a.exp i == b.exp i

instance : BEq MDiffAtom := ⟨beq⟩

/-- Differentiate in direction `i`. -/
def derivIn (a : MDiffAtom) (i : Nat) : MDiffAtom :=
  let n := max a.order.size (i + 1)
  { a with order := (Array.range n).map fun k => a.exp k + (if k == i then 1 else 0) }

/-- `a` is a derivative of `b` (not necessarily proper): same indeterminate and
componentwise `≥`. -/
def isDerivOf (a b : MDiffAtom) : Bool :=
  a.indet == b.indet &&
    (Array.range (max a.order.size b.order.size)).all fun i => b.exp i ≤ a.exp i

/-- `a` is a *proper* derivative of `b`. -/
def isProperDerivOf (a b : MDiffAtom) : Bool := a.isDerivOf b && !(a == b)

/-- The least common derivative of two atoms on the same indeterminate: componentwise max.

This is `θ₁₂ = lcm(θ₁, θ₂)`, the point where a critical pair's two prolongations meet. -/
def lcm (a b : MDiffAtom) : MDiffAtom :=
  { indet := a.indet
    order := (Array.range (max a.order.size b.order.size)).map fun i => max (a.exp i) (b.exp i) }

/-- The multi-index by which `a` must be differentiated to reach `b`, if `b` is a
derivative of `a`. -/
def quotient? (b a : MDiffAtom) : Option (Array Nat) :=
  if b.isDerivOf a then
    some ((Array.range (max a.order.size b.order.size)).map fun i => b.exp i - a.exp i)
  else none

/-- Two atoms form a *critical pair* if they are derivatives of a common indeterminate but
neither is a derivative of the other.

With one derivation this is never true, which is precisely why coherence is vacuous in the
ordinary case. -/
def isCriticalPair (a b : MDiffAtom) : Bool :=
  a.indet == b.indet && !a.isDerivOf b && !b.isDerivOf a

end MDiffAtom

/-- Ranking on multi-index derivatives. -/
inductive MRanking
  /-- By total order of differentiation first, then indeterminate, then multi-index. -/
  | orderly
  /-- By indeterminate first: eliminates higher-indexed indeterminates completely. -/
  | elimination
  deriving Inhabited, BEq, Repr

namespace MRanking

/-- Lexicographic comparison of multi-indices. -/
private def cmpIdx (a b : Array Nat) : Ordering :=
  let n := max a.size b.size
  (Array.range n).foldl (init := .eq) fun acc i =>
    match acc with
    | .eq => compare (a.getD i 0) (b.getD i 0)
    | o => o

/-- Compare two derivative atoms under this ranking. -/
def cmp : MRanking → MDiffAtom → MDiffAtom → Ordering
  | .orderly, a, b =>
    match compare a.total b.total with
    | .eq => match compare a.indet b.indet with
             | .eq => cmpIdx a.order b.order
             | o => o
    | o => o
  | .elimination, a, b =>
    match compare a.indet b.indet with
    | .eq => match compare a.total b.total with
             | .eq => cmpIdx a.order b.order
             | o => o
    | o => o

end MRanking

/-- Engine index ↔ multi-index derivative, sorted increasingly by the ranking. -/
structure MAtomTable where
  /-- Engine index → derivative atom. -/
  toAtom : Array MDiffAtom
  /-- Number of derivations. -/
  numDerivs : Nat
  /-- The ranking used. -/
  ranking : MRanking
  deriving Inhabited

namespace MAtomTable

/-- Engine index of an atom, if present. -/
def index? (t : MAtomTable) (a : MDiffAtom) : Option Nat := t.toAtom.findIdx? (· == a)

/-- All derivatives of `atoms` of total order at most `maxOrder`.

As in the ordinary case the closure must be known before indices are assigned, since a
larger engine index has to mean a higher-ranked derivative. -/
partial def closure (atoms : Array MDiffAtom) (numDerivs maxOrder : Nat) :
    Array MDiffAtom :=
  let rec go (frontier acc : Array MDiffAtom) (depth : Nat) : Array MDiffAtom :=
    match depth with
    | 0 => acc
    | d + 1 =>
      let next := frontier.foldl (init := (#[] : Array MDiffAtom)) fun nx a =>
        (Array.range numDerivs).foldl (init := nx) fun nx i =>
          let b := a.derivIn i
          if acc.any (· == b) || nx.any (· == b) then nx else nx.push b
      if next.isEmpty then acc else go next (acc ++ next) d
  go atoms atoms maxOrder

/-- Build a table from a closure, sorted by the ranking. -/
def build (ranking : MRanking) (numDerivs : Nat) (atoms : Array MDiffAtom) : MAtomTable :=
  let deduped := atoms.foldl (init := (#[] : Array MDiffAtom)) fun acc a =>
    if acc.any (· == a) then acc else acc.push a
  { toAtom := deduped.qsort fun a b => ranking.cmp a b == .lt
    numDerivs := numDerivs, ranking := ranking }

end MAtomTable

/-- Formal derivation in direction `i`, over several derivations.

Same chain rule as the ordinary case; only `δ(x)` changes, being the atom differentiated in
direction `i`. -/
def Poly.derivInM (t : MAtomTable) (i : Nat) (p : Poly) : Option Poly := do
  let mut acc := Poly.zero
  for k in [0:t.toAtom.size] do
    let d := p.pderiv k
    if d.isZero then continue
    let some a := t.toAtom[k]? | failure
    let some j := t.index? (a.derivIn i) | failure
    acc := Poly.add acc (Poly.mul d (Poly.var j))
  return acc

/-- Apply a multi-index of derivations. -/
def Poly.derivM (t : MAtomTable) (p : Poly) (α : Array Nat) : Option Poly := do
  let mut acc := p
  for i in [0:α.size] do
    for _ in [0:α.getD i 0] do
      acc ← Poly.derivInM t i acc
  return acc

/-- The atoms occurring in `p`, as multi-index derivatives. -/
def Poly.mDiffAtoms (t : MAtomTable) (p : Poly) : Array MDiffAtom :=
  (Array.range t.toAtom.size).filterMap fun i =>
    if p.degIn i == 0 then none else t.toAtom[i]?

/-- The leader of `f`: its highest-ranked derivative. -/
def Poly.leaderM (t : MAtomTable) (f : Poly) : Option MDiffAtom := do
  let v ← f.mainVar?
  t.toAtom[v]?

/-- The **Δ-polynomial** of a critical pair.

For `p₁, p₂` with leaders `θ₁u`, `θ₂u` and separants `s₁, s₂`, with `θ₁₂ = lcm(θ₁, θ₂)`:

```
Δ(p₁, p₂) = s₂ · (θ₁₂/θ₁)(p₁) − s₁ · (θ₁₂/θ₂)(p₂)
```

The leading terms cancel by construction, so `Δ` has strictly lower rank than `θ₁₂u`. The
set is *coherent* when every such `Δ` reduces to zero; a nonzero reduction is a new
relation that must be added, exactly as with S-polynomials.

Returns `none` when the two do not form a critical pair (in particular always, with a
single derivation). -/
def deltaPoly (t : MAtomTable) (p₁ p₂ : Poly) : Option Poly := do
  let l₁ ← p₁.leaderM t
  let l₂ ← p₂.leaderM t
  guard (l₁.isCriticalPair l₂)
  let l₁₂ := l₁.lcm l₂
  let α₁ ← l₁₂.quotient? l₁
  let α₂ ← l₁₂.quotient? l₂
  let d₁ ← Poly.derivM t p₁ α₁
  let d₂ ← Poly.derivM t p₂ α₂
  let s₁ := p₁.separant
  let s₂ := p₂.separant
  return Poly.sub (Poly.mul s₂ d₁) (Poly.mul s₁ d₂)

end Wu
