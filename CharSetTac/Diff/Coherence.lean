/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Diff.MultiIndex
import CharSetTac.CharSet

/-!
# Coherence, and completion by Δ-polynomials

`CharSetTac/Diff/MultiIndex.lean` builds the Δ-polynomial of a critical pair. This file
uses it: a set is **coherent** when every Δ-polynomial reduces to zero, and when one does
not, its remainder is a new relation that has to be added — exactly Buchberger's loop, with
Δ-polynomials in place of S-polynomials.

## Why this matters, and why only now

Coherence is the hypothesis of Rosenfeld's lemma, which is what lets a differential ideal be
handled by algebraic means. With a **single** derivation it is vacuous: any two derivatives
of one indeterminate are comparable, so `isCriticalPair` is never true and `deltaPoly`
always returns `none`. That is checked in `Diff/TestMulti.lean` and is why nothing here was
needed until the multi-index layer existed.

With two or more derivations it is not vacuous, and the completion loop computes something
real. The worked example in `Diff/TestCoherence.lean` is the smallest interesting one:
completing `{δ₁u = a, δ₂u = b}` produces `δ₁b - δ₂a`, which is the classical integrability
condition. The machinery rediscovers Clairaut.

## Reduction here is untracked

`completeCoherent` answers a question about a *set*, not about a goal, so it does not carry
cofactors. Certificates are the business of `CharSet.lean`; this is the structural
precondition that makes those certificates apply to a differential ideal.
-/

namespace Wu

/-- Pseudo-reduce `g` by every element of `ps`, discarding the bookkeeping.

Mirrors the reduction order of `setPrem` — highest-ranked element outermost — but keeps no
cofactors, because coherence is a yes/no question about the set. -/
def remBy (g : Poly) (ps : Array Poly) : Poly :=
  ps.foldr (init := g) fun f acc => (Wu.prem acc f).remainder

/-- Every Δ-polynomial of a critical pair in `ps`, reduced by `ps`, keeping the nonzero
ones. An empty result is exactly coherence. -/
def deltaRemainders (t : MAtomTable) (ps : Array Poly) : Array Poly := Id.run do
  let mut out : Array Poly := #[]
  for i in [0 : ps.size] do
    for j in [i + 1 : ps.size] do
      match deltaPoly t ps[i]! ps[j]! with
      | none => pure ()
      | some d =>
        let r := remBy d ps
        unless r.isZero || out.any (fun q => Poly.isZero (Poly.sub q r)) do
          out := out.push r
  return out

/-- **A set is coherent** when every Δ-polynomial of a critical pair reduces to zero.

Vacuously true for a single derivation, where there are no critical pairs at all. -/
def isCoherent (t : MAtomTable) (ps : Array Poly) : Bool :=
  (deltaRemainders t ps).isEmpty

/-- **Completion.** Add nonzero Δ-remainders until none appear.

The differential analogue of Buchberger's algorithm. `fuel` bounds the rounds.

Termination in the literature is **not** by the Ritt–Raudenbush basis theorem — an earlier
version of this comment said it was, and that was wrong. Rosenfeld–Gröbner terminates by a
well-founded order `≺_t` on its quadruples `(G, D, A, H)`: the rank of the triangular set
decreases, or it stays equal and the pending set decreases under "replace one element by
finitely many of strictly lower rank" (Hubert, *Notes on Triangular Sets II*, Def. 6.2 and
Props. 6.3/6.5; Boulier–Lazard–Ollivier–Petitot, Props. 29–35). The basis theorem is not used.

Neither order is formalised here, so exhausting the fuel returns the set reached so far and
`isCoherent` reports it as incomplete rather than letting the caller believe otherwise. -/
partial def completeCoherent (t : MAtomTable) (ps : Array Poly) (fuel : Nat := 20) :
    Array Poly :=
  match fuel with
  | 0 => ps
  | fuel + 1 =>
    let new := deltaRemainders t ps
    if new.isEmpty then ps else completeCoherent t (ps ++ new) fuel

end Wu
