/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Sparse multivariate polynomials over `ℚ` for the `wu` tactic

This is the *engine* representation: plain computable data used inside `MetaM` by the
oracle that computes characteristic sets. It is deliberately **not** `MvPolynomial`.
Mathlib's `MvPolynomial` is `noncomputable`, so it cannot be evaluated; and we do not
need it to be, because the tactic never trusts the oracle. The oracle's output is
turned into a `ring`-checkable identity, so a bug here causes a tactic *failure*, never
an unsound proof.

## Representation

A monomial is a dense exponent vector indexed by variable number, kept free of trailing
zeros so that structural equality is the right equality. A polynomial is an array of
`(coefficient, monomial)` terms, sorted strictly decreasing under `Mon.cmp` with no zero
coefficients.

Variable indices carry the *variable order*: index `0` is the smallest (a free parameter
in geometry problems) and larger indices are "later"/dependent. The **main variable** of
a polynomial is the largest index occurring in it, matching `MvPolynomial.vars.max` in
`CharacteristicSet/Order.lean`. `Mon.cmp` compares from the highest variable index
downwards, so the main variable dominates the ordering.
-/

namespace Wu

/-- A monomial: a dense exponent vector indexed by variable number, with no trailing
zeros. Use `Mon.trim` after any operation that can introduce them. -/
abbrev Mon := Array Nat

namespace Mon

/-- Drop trailing zero exponents, so that structural equality is the right equality. -/
def trim (m : Mon) : Mon :=
  let rec go (n : Nat) : Mon :=
    match n with
    | 0 => #[]
    | k + 1 => if m[k]! == 0 then go k else m.extract 0 (k + 1)
  go m.size

/-- The exponent of variable `i`; `0` past the end of the vector. -/
def exp (m : Mon) (i : Nat) : Nat := m.getD i 0

/-- The largest variable index with a nonzero exponent, if any: the main variable. -/
def mainVar? (m : Mon) : Option Nat :=
  if m.isEmpty then none else some (m.size - 1)

/-- The constant monomial. -/
def one : Mon := #[]

/-- `x_i ^ e` as a monomial. -/
def single (i e : Nat) : Mon :=
  if e == 0 then one else (Array.replicate i 0).push e

/-- Total degree. -/
def degree (m : Mon) : Nat := m.foldl (· + ·) 0

/-- Product of monomials: pointwise addition of exponents. -/
def mul (a b : Mon) : Mon :=
  trim <| (Array.range (max a.size b.size)).map fun i => a.getD i 0 + b.getD i 0

/-- Set the exponent of variable `i` to `e`. -/
def setExp (m : Mon) (i e : Nat) : Mon :=
  let m := if m.size ≤ i then m ++ Array.replicate (i + 1 - m.size) 0 else m
  trim (m.set! i e)

/-- Compare monomials from the highest variable index downwards.

Because the comparison starts at the top variable, this order refines the "main
variable, then degree in it" ranking that characteristic set theory uses. -/
def cmp (a b : Mon) : Ordering :=
  let rec go (i : Nat) : Ordering :=
    match i with
    | 0 => .eq
    | j + 1 =>
      match compare (a.getD j 0) (b.getD j 0) with
      | .eq => go j
      | o => o
  go (max a.size b.size)

end Mon

/-- A term: a nonzero rational coefficient and a monomial. -/
structure Term where
  coeff : Rat
  mon : Mon
  deriving Inhabited, BEq

/-- A polynomial: terms sorted strictly decreasing under `Mon.cmp`, no zero coefficients.

The invariant is established by `Poly.ofTerms` and maintained by every operation here. -/
abbrev Poly := Array Term

namespace Poly

/-- The zero polynomial. -/
def zero : Poly := #[]

/-- Is this the zero polynomial? -/
def isZero (p : Poly) : Bool := p.isEmpty

/-- Normalise a term array: combine equal monomials, drop zero coefficients, and sort
strictly decreasing under `Mon.cmp`. -/
def ofTerms (ts : Array Term) : Poly := Id.run do
  let sorted := ts.qsort fun a b => Mon.cmp a.mon b.mon == .gt
  let mut out : Array Term := #[]
  for t in sorted do
    if out.size > 0 && Mon.cmp out[out.size - 1]!.mon t.mon == .eq then
      let last := out[out.size - 1]!
      let c := last.coeff + t.coeff
      out := out.pop
      if c != 0 then out := out.push { coeff := c, mon := last.mon }
    else if t.coeff != 0 then
      out := out.push t
  return out

/-- A rational constant as a polynomial. -/
def const (c : Rat) : Poly := if c == 0 then zero else #[{ coeff := c, mon := Mon.one }]

/-- The variable `x_i`. -/
def var (i : Nat) : Poly := #[{ coeff := 1, mon := Mon.single i 1 }]

/-- Scale by a rational. -/
def smul (c : Rat) (p : Poly) : Poly :=
  if c == 0 then zero else p.map fun t => { t with coeff := c * t.coeff }

/-- Negation. -/
def neg (p : Poly) : Poly := smul (-1) p

/-- Addition. -/
def add (p q : Poly) : Poly := ofTerms (p ++ q)

/-- Subtraction. -/
def sub (p q : Poly) : Poly := add p (neg q)

/-- Multiplication. -/
def mul (p q : Poly) : Poly := Id.run do
  let mut ts : Array Term := #[]
  for a in p do
    for b in q do
      ts := ts.push { coeff := a.coeff * b.coeff, mon := Mon.mul a.mon b.mon }
  return ofTerms ts

/-- `p ^ n`. -/
def pow (p : Poly) : Nat → Poly
  | 0 => const 1
  | n + 1 => mul p (pow p n)

/-- The main variable: the largest variable index occurring in `p`.

`none` for a constant (including zero). Mirrors `MvPolynomial.vars.max`. -/
def mainVar? (p : Poly) : Option Nat :=
  p.foldl (init := none) fun acc t =>
    match acc, t.mon.mainVar? with
    | none, v => v
    | some a, none => some a
    | some a, some b => some (max a b)

/-- Degree of `p` in variable `i`. -/
def degIn (p : Poly) (i : Nat) : Nat :=
  p.foldl (init := 0) fun acc t => max acc (t.mon.exp i)

/-- The **main degree**: degree in the main variable, or `0` for a constant.

Mirrors `MvPolynomial.mainDegree`. -/
def mainDeg (p : Poly) : Nat :=
  match p.mainVar? with
  | none => 0
  | some v => p.degIn v

/-- The coefficient of `x_i ^ d` in `p`, as a polynomial in the other variables. -/
def coeffOf (p : Poly) (i d : Nat) : Poly :=
  ofTerms <| p.filterMap fun t =>
    if t.mon.exp i == d then some { t with mon := t.mon.setExp i 0 } else none

/-- The **initial** of `p`: the leading coefficient with respect to the main variable.

For a constant `p` this is `p` itself. Mirrors `MvPolynomial.initial`. -/
def initial (p : Poly) : Poly :=
  match p.mainVar? with
  | none => p
  | some v => p.coeffOf v (p.degIn v)

/-- Rank comparison: by main variable, then by degree in it.

This is the ordering `CharacteristicSet/Order.lean` calls `order`, used to select basic
set elements. Constants rank below anything containing a variable. -/
def rankCmp (p q : Poly) : Ordering :=
  match p.mainVar?, q.mainVar? with
  | none, none => .eq
  | none, some _ => .lt
  | some _, none => .gt
  | some a, some b =>
    match compare a b with
    | .eq => compare p.mainDeg q.mainDeg
    | o => o

/-- Content: gcd of the numerators divided by lcm of the denominators.

Dividing this out keeps coefficients from blowing up during repeated pseudo-division,
which is the dominant practical cost of Wu's method. -/
def content (p : Poly) : Rat :=
  if p.isZero then 1
  else
    let num := p.foldl (init := 0) fun g t => Nat.gcd g t.coeff.num.natAbs
    let den := p.foldl (init := 1) fun l t => Nat.lcm l t.coeff.den
    if num == 0 then 1 else (num : Rat) / (den : Rat)

/-- Divide out the content, giving a primitive polynomial with integer coefficients. -/
def primitive (p : Poly) : Poly :=
  let c := p.content
  if c == 0 then p else smul (1 / c) p

/-- Render for tracing and error messages. -/
def toString (p : Poly) : String :=
  if p.isZero then "0"
  else String.intercalate " + " (p.toList.map fun t =>
    let ms := (t.mon.toList.zipIdx.filterMap fun (e, i) =>
      if e == 0 then none else some (s!"x{i}" ++ if e == 1 then "" else s!"^{e}"))
    if ms.isEmpty then s!"{t.coeff}"
    else (if t.coeff == 1 then "" else s!"{t.coeff}*") ++ String.intercalate "*" ms)

instance : ToString Poly := ⟨toString⟩

end Poly
end Wu
