/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Diff.Derivation

/-!
# Differential pseudo-reduction

Reduces a differential polynomial modulo a chain, producing the certificate

```
H · g = ∑ⱼ ∑ₖ c_{j,k} · δᵏ(Aⱼ)
```

where `H` is a product of initials and separants. The differential content is confined to
one step: when `g` mentions a proper derivative of a leader, prolong that equation and
pseudo-divide by the prolongation. Every division itself is the ordinary algebraic `prem`.

## Why this needs no Rosenfeld

The certificate above is a *positive* membership statement, and it is checked directly:
each `δᵏ(Aⱼ)` vanishes because `Aⱼ` does, and the identity is a ring identity in the
derivatives. Rosenfeld's lemma is what licenses the converse — concluding
*non*-membership from a nonzero remainder — and nothing here does that.

## Cofactors

The algebraic engine tracks cofactors indexed by hypothesis. Here they are indexed by
`(hypothesis, order of prolongation)`, since `δᵏ(Aⱼ)` for different `k` are independent
generators as far as the certificate is concerned.
-/

namespace Wu

/-- A differential polynomial together with its certificate against the inputs:
`poly = ∑_{(j,k)} cof[(j,k)] · δᵏ(Aⱼ)`. -/
structure DTracked where
  /-- The polynomial itself. -/
  poly : Poly
  /-- Cofactors, indexed by `(input index, prolongation order)`. -/
  cof : Array ((Nat × Nat) × Poly)
  deriving Inhabited

namespace DTracked

/-- Input `j`, tracked as itself. -/
def ofInput (j : Nat) (p : Poly) : DTracked :=
  { poly := p, cof := #[((j, 0), Poly.const 1)] }

/-- Look up a cofactor, defaulting to zero. -/
def get (t : DTracked) (k : Nat × Nat) : Poly :=
  match t.cof.find? (fun e => e.1 == k) with
  | some (_, p) => p
  | none => Poly.zero

/-- All indices mentioned by either argument. -/
private def keys (a b : DTracked) : Array (Nat × Nat) :=
  (a.cof.map (·.1) ++ b.cof.map (·.1)).foldl (init := #[]) fun acc k =>
    if acc.any (· == k) then acc else acc.push k

/-- `c · a`, on polynomial and cofactors alike. -/
def scale (c : Poly) (a : DTracked) : DTracked :=
  { poly := Poly.mul c a.poly, cof := a.cof.map fun (k, p) => (k, Poly.mul c p) }

/-- `a - b`. -/
def sub (a b : DTracked) : DTracked :=
  { poly := Poly.sub a.poly b.poly
    cof := (keys a b).map fun k => (k, Poly.sub (a.get k) (b.get k)) }

/-- Prolong: `δ` applied to both the polynomial and the certificate.

If `poly = ∑ c·δᵏ(Aⱼ)` then `δ(poly) = ∑ (δc)·δᵏ(Aⱼ) + ∑ c·δᵏ⁺¹(Aⱼ)`, by Leibniz. Both
halves are kept, which is why a cofactor index is a *pair*. -/
def deriv (t : AtomTable) (a : DTracked) : Option DTracked := do
  let p ← Poly.deriv t a.poly
  let mut out : Array ((Nat × Nat) × Poly) := #[]
  for ((j, k), c) in a.cof do
    let dc ← Poly.deriv t c
    -- (δc) · δᵏ(Aⱼ)
    if !dc.isZero then
      out := push out (j, k) dc
    -- c · δᵏ⁺¹(Aⱼ)
    if !c.isZero then
      out := push out (j, k + 1) c
  return { poly := p, cof := out }
where
  /-- Accumulate into an existing index rather than shadowing it. -/
  push (acc : Array ((Nat × Nat) × Poly)) (k : Nat × Nat) (v : Poly) :
      Array ((Nat × Nat) × Poly) :=
    match acc.findIdx? (fun e => e.1 == k) with
    | some i => acc.set! i (k, Poly.add acc[i]!.2 v)
    | none => acc.push (k, v)

end DTracked

/-- One step of differential reduction of `g` by `f`.

If `g` mentions a proper derivative `δᵐ(v)` of `f`'s leader `v`, prolong `f` by `m` and
pseudo-divide by that; otherwise pseudo-divide by `f` itself. Returns `none` when nothing
applies, so the caller can stop. -/
def dremStep (t : AtomTable) (g f : DTracked) : Option DTracked := do
  let some v := f.poly.mainVar? | failure
  let some lead := t.toAtom[v]? | failure
  -- highest proper derivative of `lead` occurring in `g`, if any
  let props := (g.poly.diffAtoms t).filter (·.isProperDerivOf lead)
  let target ← if props.isEmpty then some f else do
    let m := props.foldl (init := 0) fun acc a => max acc (a.order - lead.order)
    let mut fp := f
    for _ in [0:m] do
      fp ← DTracked.deriv t fp
    pure fp
  -- now pseudo-divide algebraically by `target`
  let some tv := target.poly.mainVar? | failure
  if g.poly.degIn tv < target.poly.degIn tv then failure
  let res := Wu.prem g.poly target.poly
  let I := target.poly.initial
  let Ipow := Poly.pow I res.exponent
  let r := DTracked.sub (DTracked.scale Ipow g) (DTracked.scale res.quotient target)
  return { r with poly := res.remainder }

/-- Fully reduce `g` by a single `f`, prolonging as needed. -/
partial def drem (t : AtomTable) (g f : DTracked) (fuel : Nat := 32) : DTracked :=
  match fuel with
  | 0 => g
  | fuel + 1 =>
    match dremStep t g f with
    | some g' => if g'.poly == g.poly then g else drem t g' f fuel
    | none => g

/-- Reduce `g` by a whole chain, highest-ranked element first. -/
def dremSet (t : AtomTable) (g : DTracked) (chain : Array DTracked) : DTracked :=
  chain.foldr (init := g) fun f acc => drem t acc f

/-- Reduction state for the *conclusion*, with invariant

`mult * g = poly + ∑_{(j,k)} cof[(j,k)] · δᵏ(Aⱼ)`.

The conclusion needs a different invariant from the inputs, for the same reason as in the
algebraic case: it is not in the ideal the inputs generate, so it cannot carry the
"I am a combination of the inputs" invariant. Reducing `poly` to `0` leaves
`mult * g = ∑ cof · δᵏ(Aⱼ)`, which is the certificate. -/
structure DReduction where
  /-- Accumulated multiplier on the conclusion: a product of initials and separants. -/
  mult : Poly
  /-- Current remainder. -/
  poly : Poly
  /-- Cofactors against prolonged inputs. -/
  cof : Array ((Nat × Nat) × Poly)
  /-- `(initial, exponent)` pairs multiplied in, for the nondegeneracy conditions. -/
  factors : Array (Poly × Nat)
  deriving Inhabited

namespace DReduction

/-- Start reducing `g`: `1 * g = g + ∑ 0`. -/
def start (g : Poly) : DReduction :=
  { mult := Poly.const 1, poly := g, cof := #[], factors := #[] }

/-- Look up a cofactor, defaulting to zero. -/
def get (r : DReduction) (k : Nat × Nat) : Poly :=
  match r.cof.find? (fun e => e.1 == k) with
  | some (_, p) => p
  | none => Poly.zero

/-- One reduction step against `f`, maintaining the invariant.

With `init(target)^s * poly = q * target + rem` and `target = ∑ Cf · δᵏ(Aⱼ)`:
`mult' = init^s * mult`, `cof'[k] = init^s * cof[k] + q * Cf[k]`, `poly' = rem`. -/
def step (t : AtomTable) (r : DReduction) (f : DTracked) : Option DReduction := do
  let some v := f.poly.mainVar? | failure
  let some lead := t.toAtom[v]? | failure
  let props := ((Poly.diffAtoms t r.poly)).filter (·.isProperDerivOf lead)
  let target ← if props.isEmpty then some f else do
    let m := props.foldl (init := 0) fun acc a => max acc (a.order - lead.order)
    let mut fp := f
    for _ in [0:m] do
      fp ← DTracked.deriv t fp
    pure fp
  let some tv := target.poly.mainVar? | failure
  if r.poly.degIn tv < target.poly.degIn tv then failure
  let res := Wu.prem r.poly target.poly
  let I := target.poly.initial
  let Ipow := Poly.pow I res.exponent
  let keys := (r.cof.map (·.1) ++ target.cof.map (·.1)).foldl (init := #[]) fun acc k =>
    if acc.any (· == k) then acc else acc.push k
  return { mult := Poly.mul Ipow r.mult
           poly := res.remainder
           cof := keys.map fun k =>
             (k, Poly.add (Poly.mul Ipow (r.get k)) (Poly.mul res.quotient (target.get k)))
           factors := if res.exponent == 0 then r.factors
                      else r.factors.push (I, res.exponent) }

/-- Reduce fully by one chain element. -/
partial def run1 (t : AtomTable) (r : DReduction) (f : DTracked) (fuel : Nat := 32) :
    DReduction :=
  match fuel with
  | 0 => r
  | fuel + 1 =>
    match step t r f with
    | some r' => if r'.poly == r.poly then r else run1 t r' f fuel
    | none => r

/-- Reduce by a whole chain, highest-ranked element first. -/
def run (t : AtomTable) (r : DReduction) (chain : Array DTracked) : DReduction :=
  chain.foldr (init := r) fun f acc => run1 t acc f

end DReduction

end Wu
