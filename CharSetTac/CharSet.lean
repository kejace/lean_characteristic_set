/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Pseudo

/-!
# Basic sets and characteristic sets

The oracle proper. Given hypothesis polynomials and a conclusion this computes a
characteristic set and, crucially, a **certificate**: a multiplier `I` and cofactors `dⱼ`
with `I * g = ∑ⱼ dⱼ * hⱼ`.

## The algorithm

`basicSet` picks a minimal ascending set out of a polynomial list, greedily by rank
(`Poly.rankCmp`), mirroring `WeakAscendingSet.basicSet` / `StandardAscendingSet.basicSet`.

`charSet` is Wu's iteration: take the basic set `BS` of the current set `PS`, pseudo-reduce
every element of `PS \ BS` by `BS`, and if nonzero remainders appear, add them to `PS` and
repeat. On termination every element of `PS` reduces to `0` modulo `BS` — exactly
`TriangularSet.IsCharacteristicSet` (`CharacteristicSet/CharacteristicSet.lean:82`).

## Two different invariants

The *hypotheses* are tracked with `Tracked`, whose invariant is `poly = ∑ⱼ cof[j] * hⱼ`.
That works because every polynomial derived from the hypotheses is in the ideal they
generate.

The *conclusion* is not in that ideal — that is the whole point — so it needs a different
invariant. `Reduction` carries an explicit multiplier:

```
mult * g = poly + ∑ⱼ cof[j] * hⱼ
```

Reducing to `poly = 0` leaves `mult * g = ∑ⱼ cof[j] * hⱼ`, which is the certificate. The
multiplier must be tracked explicitly rather than reconstructed from the initials, because
each pseudo-division step contributes `init(f) ^ s` for a step-dependent exponent `s`; a
product of bare initials would not match and `ring1` would reject it.
-/

namespace Wu

/-- Pseudo-reduce a hypothesis-derived polynomial by a triangular set, highest-ranked
element first, as `MvPolynomial.setPseudo` does. -/
def setPrem (g : Tracked) (ts : Array Tracked) : Tracked :=
  ts.foldr (init := g) fun f acc => (Tracked.prem acc f).2.2

/-- Select a basic set: a minimal ascending set contained in `ps`.

Sort by rank, then greedily keep each polynomial whose main variable is strictly larger
than everything kept so far and which is reduced with respect to all of it. -/
def basicSet (mode : Mode) (ps : Array Tracked) : Array Tracked := Id.run do
  let sorted := ps.qsort fun a b => Poly.rankCmp a.poly b.poly == .lt
  let mut out : Array Tracked := #[]
  for t in sorted do
    if t.poly.isZero then continue
    match t.poly.mainVar? with
    | none => continue   -- a nonzero constant cannot belong to an ascending set
    | some v =>
      let okChain := out.all fun u =>
        match u.poly.mainVar? with
        | none => false
        | some w => w < v
      if okChain && reducedToSet mode t.poly (out.map (·.poly)) then
        out := out.push t
  return out

/-- One round of Wu's algorithm: the basic set, plus nonzero remainders of the rest. -/
private def charSetRound (mode : Mode) (ps : Array Tracked) :
    Array Tracked × Array Tracked :=
  let bs := basicSet mode ps
  let bsPolys := bs.map (·.poly)
  let rest := ps.filter fun t => !bsPolys.any fun b => b == t.poly
  let rems := rest.filterMap fun t =>
    let r := setPrem t bs
    if r.poly.isZero then none else some r
  (bs, rems)

/-- Wu's characteristic set algorithm.

`fuel` bounds the number of rounds; exhausting it returns the basic set computed so far,
which callers should treat as "no certificate found" rather than as a result. -/
partial def charSet (mode : Mode) (ps : Array Tracked) (fuel : Nat := 50) : Array Tracked :=
  match fuel with
  | 0 => basicSet mode ps
  | fuel + 1 =>
    let (bs, rems) := charSetRound mode ps
    if rems.isEmpty then bs else charSet mode (ps ++ rems) fuel

/-- Reduction state for the conclusion, with invariant

`mult * g = poly + ∑ⱼ cof[j] * hⱼ`. -/
structure Reduction where
  /-- Current remainder. -/
  poly : Poly
  /-- Cofactors against the original hypotheses. -/
  cof : Array Poly
  /-- The `(initial, exponent)` pairs multiplied in so far, for nondegeneracy goals.

  The multiplier itself is **not** carried here. It is exactly `∏ (I ^ e)` over these
  pairs, so maintaining it through the loop means re-multiplying an ever-growing product
  at every step — the largest single cost in the engine, for a value no caller needs until
  the end. `Certificate.mult` reconstitutes it once, in `solve`. -/
  factors : Array (Poly × Nat)
  deriving Inhabited

namespace Reduction

/-- Start reducing `g`: `1 * g = g + ∑ 0 * hⱼ`. -/
def start (n : Nat) (g : Poly) : Reduction :=
  { poly := g, cof := Array.replicate n Poly.zero, factors := #[] }

/-- Pseudo-divide the current remainder by `f`, maintaining the invariant.

With `init(f)^s * poly = q * f + r` and `f = ∑ⱼ Cf[j] * hⱼ`:
`cof'[j] = init(f)^s * cof[j] + q * Cf[j]`, `poly' = r`, and `init(f)^s` joins the
factors. -/
def step (red : Reduction) (f : Tracked) : Reduction :=
  let res := Wu.prem red.poly f.poly
  let I := f.poly.initial
  let Ipow := Poly.pow I res.exponent
  { poly := res.remainder
    cof := (Array.range (max red.cof.size f.cof.size)).map fun j =>
      Poly.add (Poly.mul Ipow (red.cof.getD j Poly.zero))
        (Poly.mul res.quotient (f.cof.getD j Poly.zero))
    factors := if res.exponent == 0 then red.factors else red.factors.push (I, res.exponent) }

/-- Reduce by a whole triangular set, highest-ranked element first. -/
def run (red : Reduction) (ts : Array Tracked) : Reduction :=
  ts.foldr (init := red) fun f acc => acc.step f

end Reduction

/-- A certificate that the conclusion follows from the hypotheses:
`mult * g = ∑ⱼ cofactors[j] * hⱼ`, where `mult = ∏ (I ^ e)` over `factors`. -/
structure Certificate where
  /-- The multiplier applied to the conclusion. -/
  mult : Poly
  /-- The `(initial, exponent)` pairs whose product is `mult`; each initial must be
  nonzero, and these become the nondegeneracy side goals. -/
  factors : Array (Poly × Nat)
  /-- Cofactors against the original hypotheses. -/
  cofactors : Array Poly
  /-- The characteristic set that was computed, for `wu?` and tracing. -/
  charSet : Array Poly
  deriving Inhabited

/-- **Cancel factors shared by the multiplier and every cofactor.**

Pseudo-division multiplies the whole reduction state by `init(f)^s` at every step, and much
of that is later cancelled by the arithmetic rather than by the bookkeeping — so the raw
certificate routinely carries initials that divide out exactly. Removing them shrinks the
`linear_combination` that Lean has to check, which is the dominant cost on hard problems
once the engine itself is fast.

It also **removes nondegeneracy side goals**: a factor cancelled to exponent zero is no
longer part of the multiplier, so the user is never asked to prove it nonzero. That is why
the conditions `wu` reports are often stronger than the theorem needs — this is the fix.

Soundness needs no argument beyond polynomial algebra. `ℚ[x]` is a domain and each `I` is
the initial of a nonzero polynomial, so `I * (M' * g - ∑ d'ⱼ hⱼ) = 0` gives
`M' * g = ∑ d'ⱼ hⱼ` as an identity of polynomials. The oracle is untrusted regardless: if
this pass ever produced a false identity, `ring1` would reject it and the tactic would
fail. -/
def Certificate.cancelCommonFactors (c : Certificate) : Certificate := Id.run do
  let mut factors : Array (Poly × Nat) := #[]
  let mut cofs := c.cofactors
  for (I, e) in c.factors do
    let mut left := e
    for _ in [0:e] do
      match cofs.mapM (fun d => Poly.divExact d I) with
      | some cofs' => cofs := cofs'; left := left - 1
      | none => break
    if left > 0 then factors := factors.push (I, left)
  return { c with
    factors := factors
    cofactors := cofs
    mult := factors.foldl (init := Poly.const 1) fun acc (I, e) => Poly.mul acc (Poly.pow I e) }

/-- Run Wu's method on hypotheses `hs` and conclusion `g`.

Returns a certificate when `g` pseudo-reduces to zero modulo the characteristic set, and
`none` otherwise — meaning Wu's method does not prove this goal, either because it is
false or because it holds only under conditions beyond nondegeneracy. -/
def solve (mode : Mode) (hs : Array Poly) (g : Poly) : Option Certificate :=
  let n := hs.size
  let tracked := hs.zipIdx.map fun (h, j) => Tracked.ofHyp n j h
  let cs := charSet mode tracked
  let red := (Reduction.start n g).run cs
  if !red.poly.isZero then none
  else
    some <| Certificate.cancelCommonFactors
      { mult := red.factors.foldl (init := Poly.const 1) fun acc (I, e) =>
          Poly.mul acc (Poly.pow I e)
        factors := red.factors
        cofactors := red.cof
        charSet := cs.map (·.poly) }

end Wu
