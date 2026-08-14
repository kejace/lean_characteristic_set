/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.CharSet
import Mathlib.Util.AtomM
import Mathlib.Tactic.Ring

/-!
# Reflection between `Expr` and the engine's `Poly`

Turns ring expressions into `Wu.Poly` and back. Atoms are managed by Mathlib's `AtomM`,
the same machinery `ring` and `linear_combination` use, so atom indices agree with what
those tactics see.

Anything that is not built from `+ - * ^` and numerals becomes an atom. That is what
makes `wu` work on goals about `ℝ` with arbitrary subterms rather than only on explicit
`MvPolynomial` values.

## Variable order

The engine treats larger variable indices as "later"/dependent, and the main variable of
a polynomial is its largest index. Atom indices are assigned in order of first
appearance, so by default the first atom encountered is the most free parameter. The
`wu (vars := ...)` configuration overrides this by pre-seeding the atom list.

## Coefficients

Parsing produces rational coefficients, but emitting them back into a general `CommRing`
must not introduce division. `Certificate.clearDenominators` scales the whole identity by
the least common multiple of the denominators, so everything emitted has integer
coefficients and the tactic works over any commutative ring, not just fields.
-/

open Lean Meta Elab Qq Mathlib.Tactic

namespace Wu

/-- Recognise a natural number literal.

`Expr.rawNatLit?` alone is not enough: a numeric literal at a non-`Nat` type, and even
`2 : ℕ` as written by the user, elaborates to `OfNat.ofNat 2` rather than a raw literal.
Missing this silently turns `y ^ 2` into an atom, which makes the engine unable to relate
it to anything. -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  if let some n := e.rawNatLit? then return some n
  if let some n := e.nat? then return some n
  let e ← whnfR e
  if let some n := e.rawNatLit? then return some n
  return e.nat?

/-- Recognise a numeral, including negations and divisions of numerals.

Division is accepted because the identity is ultimately checked by `ring1`: if the ring
has no division the emitted certificate simply fails to elaborate or to close, which is a
tactic failure rather than an unsound proof. -/
partial def getNumeral? (e : Expr) : MetaM (Option Rat) := do
  let e ← whnfR e
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => return (← natLit? n).map (fun n => (n : Rat))
  | (``Neg.neg, #[_, _, a]) => return (← getNumeral? a).map (fun r => -r)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => do
    let some ra ← getNumeral? a | return none
    let some rb ← getNumeral? b | return none
    if rb == 0 then return none else return some (ra / rb)
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
    let some ra ← getNumeral? a | return none
    let some rb ← getNumeral? b | return none
    return some (ra + rb)
  | _ => return (← getRawNat? e).map (fun n => (n : Rat))
where
  /-- Natural number literal, if this is one. -/
  getRawNat? (e : Expr) : MetaM (Option Nat) := natLit? e

/-- Parse an expression into a `Poly`, adding atoms as needed. -/
partial def toPoly (e : Expr) : AtomM Poly := do
  if let some r ← getNumeral? e then
    return Poly.const r
  match (← whnfR e).getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return Poly.add (← toPoly a) (← toPoly b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return Poly.sub (← toPoly a) (← toPoly b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return Poly.mul (← toPoly a) (← toPoly b)
  | (``Neg.neg, #[_, _, a]) => return Poly.neg (← toPoly a)
  | (``HPow.hPow, #[_, _, _, _, a, n]) => do
    match ← natLit? n with
    | some k => return Poly.pow (← toPoly a) k
    | none => atom e
  | _ => atom e
where
  /-- Register `e` as an atom and return it as a variable. -/
  atom (e : Expr) : AtomM Poly := do
    let (i, _) ← AtomM.addAtom e
    return Poly.var i

/-- Build a numeral of type `R` from an integer. -/
def mkIntLit (R : Expr) (n : Int) : MetaM Expr := do
  let nat ← mkAppOptM ``OfNat.ofNat #[R, mkRawNatLit n.natAbs, none]
  if n < 0 then mkAppM ``Neg.neg #[nat] else return nat

/-- Emit a monomial as an expression over `R`, given the atom expressions. -/
def monToExpr (R : Expr) (atoms : Array Expr) (m : Mon) : MetaM (Option Expr) := do
  let mut acc : Option Expr := none
  for i in [0:m.size] do
    let e := m[i]!
    if e == 0 then continue
    let some a := atoms[i]? | throwError "wu: atom index {i} out of range"
    let factor ← if e == 1 then pure a else mkAppM ``HPow.hPow #[a, mkRawNatLit e]
    acc := some (← match acc with
      | none => pure factor
      | some p => mkAppM ``HMul.hMul #[p, factor])
  return acc

/-- Emit a polynomial as an expression over `R`.

Coefficients must be integers; call `Certificate.clearDenominators` first. -/
def polyToExpr (R : Expr) (atoms : Array Expr) (p : Poly) : MetaM Expr := do
  if p.isZero then return ← mkIntLit R 0
  let mut acc : Option Expr := none
  for t in p do
    unless t.coeff.den == 1 do
      throwError "wu: non-integer coefficient {t.coeff} reached emission"
    let mon ← monToExpr R atoms t.mon
    let term ← match mon with
      | none => mkIntLit R t.coeff.num
      | some mexp =>
        if t.coeff == 1 then pure mexp
        else if t.coeff == -1 then mkAppM ``Neg.neg #[mexp]
        else mkAppM ``HMul.hMul #[← mkIntLit R t.coeff.num, mexp]
    acc := some (← match acc with
      | none => pure term
      | some s => mkAppM ``HAdd.hAdd #[s, term])
  return acc.getD (← mkIntLit R 0)

namespace Certificate

/-- Scale the certificate so every coefficient is an integer.

Multiplying `mult * g = ∑ⱼ dⱼ hⱼ` through by a nonzero rational `c` preserves it, and
turning `mult` into `c * mult` only strengthens the (still numeral-dischargeable)
nondegeneracy condition. This is what lets `wu` work over a `CommRing` with no division. -/
def clearDenominators (c : Certificate) : Certificate :=
  let dens : Nat := (c.cofactors.push c.mult).foldl (init := (1 : Nat)) fun acc p =>
    p.foldl (init := acc) fun acc t => Nat.lcm acc t.coeff.den
  if dens == 1 then c
  else
    let s : Rat := (dens : Rat)
    { c with
      mult := Poly.smul s c.mult
      cofactors := c.cofactors.map (Poly.smul s) }

end Certificate

end Wu
