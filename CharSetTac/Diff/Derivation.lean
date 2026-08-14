/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Diff.Ranking

/-!
# Formal derivation on `Poly`

The one genuinely new engine operation for the differential case. Everything else —
pseudo-division, basic sets, characteristic sets, cofactor tracking — is reused unchanged,
because once derivatives are flat ranked indices a differential polynomial *is* an
ordinary polynomial.

The derivation is the chain rule over atoms:

```
δ(∏ᵢ xᵢ^eᵢ) = Σᵢ eᵢ · xᵢ^(eᵢ-1) · δ(xᵢ) · ∏_{j≠i} xⱼ^eⱼ
```

with `δ(xᵢ)` the atom one order higher. Coefficients are rational constants, so they
differentiate to zero: this is a derivation over the constants, which is what a
differential polynomial ring over a field of constants requires.

## Separants and initials

For `f` with leader `v` (its main variable under the ranking):

* `initial f` = leading coefficient in `v` — already in `Poly`;
* `separant f` = `∂f/∂v`.

The separant is exactly the initial of a prolonged equation, since
`δ(f) = S_f · δ(v) + (terms of lower rank)`. That is why the differential case needs no
new nondegeneracy handling: separants enter the certificate's multiplier as ordinary
polynomial factors, and `dischargeNondeg` already knows what to do with those.
-/

namespace Wu

/-- Partial derivative of `p` with respect to engine variable `i`.

This is ordinary formal differentiation: `∂(c · xᵢ^e · m)/∂xᵢ = c·e·xᵢ^(e-1)·m`. -/
def Poly.pderiv (p : Poly) (i : Nat) : Poly :=
  Poly.ofTerms <| p.filterMap fun t =>
    let e : Nat := t.mon.exp i
    if e == 0 then none
    else some { coeff := t.coeff * (e : Rat), mon := t.mon.setExp i (e - 1) }

/-- The separant of `f`: the partial derivative with respect to its leader.

For a constant (no leader) this is zero, matching the convention that a constant has no
leading derivative to differentiate against. -/
def Poly.separant (f : Poly) : Poly :=
  match f.mainVar? with
  | none => Poly.zero
  | some v => f.pderiv v

/-- Formal derivation of `p` with respect to the differential structure in `t`.

Each atom `x` contributes `∂p/∂x · δ(x)`, where `δ(x)` is the atom one order higher. If a
needed higher derivative is missing from the table the result is `none`: the caller must
enlarge the closure and rebuild, since silently dropping the term would produce a wrong
polynomial that the certificate check would then reject with a confusing error. -/
def Poly.deriv (t : AtomTable) (p : Poly) : Option Poly := do
  let mut acc := Poly.zero
  for i in [0:t.toAtom.size] do
    let d := p.pderiv i
    if d.isZero then continue
    let some a := t.toAtom[i]? | failure
    let some j := t.index? a.deriv | failure
    acc := Poly.add acc (Poly.mul d (Poly.var j))
  return acc

/-- Apply the derivation `k` times. -/
def Poly.derivN (t : AtomTable) (p : Poly) : Nat → Option Poly
  | 0 => some p
  | n + 1 => do Poly.deriv t (← Poly.derivN t p n)

/-- The atoms actually occurring in `p`, as derivative atoms. -/
def Poly.diffAtoms (t : AtomTable) (p : Poly) : Array DiffAtom :=
  (Array.range t.toAtom.size).filterMap fun i =>
    if p.degIn i == 0 then none else t.toAtom[i]?

/-- `p` is *partially reduced* with respect to `f`: it contains no proper derivative of
`f`'s leader.

This is the precondition in Rosenfeld's lemma. We do not need the lemma, but we do need
the notion, because differential reduction works by prolonging `f` until `p` becomes
partially reduced with respect to it. -/
def partiallyReduced (t : AtomTable) (p f : Poly) : Bool :=
  match f.mainVar? with
  | none => true
  | some v =>
    match t.toAtom[v]? with
    | none => true
    | some lead => (p.diffAtoms t).all fun a => !a.isProperDerivOf lead

end Wu
