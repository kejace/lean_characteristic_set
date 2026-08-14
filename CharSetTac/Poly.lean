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

/-- Product of monomials: pointwise addition of exponents.

**No `trim` is needed.** If `a` and `b` are trimmed then so is the product: at the top
index `n - 1` where `n = max a.size b.size`, whichever operand attains that size has a
nonzero exponent there, and adding the other operand's (possibly zero) exponent keeps it
nonzero. Since this is the innermost loop of every polynomial multiplication, skipping the
scan matters. -/
def mul (a b : Mon) : Mon :=
  if a.isEmpty then b
  else if b.isEmpty then a
  else Id.run do
    let n := max a.size b.size
    let mut out := Array.mkEmpty n
    for i in [0:n] do
      out := out.push (a.getD i 0 + b.getD i 0)
    return out

/-- `a / b`, when every exponent of `b` is at most the corresponding one of `a`. -/
def div? (a b : Mon) : Option Mon :=
  let n := max a.size b.size
  if (List.range n).all fun i => b.getD i 0 ≤ a.getD i 0 then
    some (trim <| (Array.range n).map fun i => a.getD i 0 - b.getD i 0)
  else none

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
  if c == 0 then zero
  else if c == 1 then p
  else p.map fun t => { t with coeff := c * t.coeff }

/-- Negation. -/
def neg (p : Poly) : Poly := p.map fun t => { t with coeff := -t.coeff }

/-- Merge two sorted term arrays, combining equal monomials and dropping cancellations.

`fuel` is `p.size + q.size`, which is ample: every step consumes at least one input term. -/
private def mergeAux : Nat → Array Term → Nat → Nat → Poly → Poly → Array Term
  | 0, out, _, _, _, _ => out
  | fuel + 1, out, i, j, p, q =>
    if i ≥ p.size then out ++ q.extract j q.size
    else if j ≥ q.size then out ++ p.extract i p.size
    else
      let a := p[i]!
      let b := q[j]!
      match Mon.cmp a.mon b.mon with
      | .gt => mergeAux fuel (out.push a) (i + 1) j p q
      | .lt => mergeAux fuel (out.push b) i (j + 1) p q
      | .eq =>
        let c := a.coeff + b.coeff
        let out := if c == 0 then out else out.push { coeff := c, mon := a.mon }
        mergeAux fuel out (i + 1) (j + 1) p q

/-- Addition, by linear merge.

Both operands are already sorted, so this is `O(n + m)`. The earlier implementation went
through `ofTerms`, re-sorting the concatenation on every addition — and a descending array
concatenated with another descending array is precisely the input a quicksort handles
worst. Addition is the single most executed operation in the engine, so this is the
difference between a benchmark that finishes and one that does not. -/
def add (p q : Poly) : Poly :=
  if p.isEmpty then q
  else if q.isEmpty then p
  else mergeAux (p.size + q.size) (Array.mkEmpty (p.size + q.size)) 0 0 p q

/-- Subtraction. -/
def sub (p q : Poly) : Poly :=
  if q.isEmpty then p else if p.isEmpty then neg q else add p (neg q)

/-- Multiplication by a single term. Multiplying every monomial by a fixed monomial adds
the same exponent vector everywhere, which `Mon.cmp` preserves — so the result is already
sorted and no normalisation pass is needed. -/
private def mulTerm (p : Poly) (c : Rat) (m : Mon) : Poly :=
  if c == 0 then zero
  else p.map fun t => { coeff := c * t.coeff, mon := Mon.mul t.mon m }

/-- Multiplication.

The single-term fast path is not a micro-optimisation: pseudo-division multiplies by
`x_i ^ (e - d)` and by initials on every iteration, and those are very often one term. -/
def mul (p q : Poly) : Poly :=
  if p.isEmpty || q.isEmpty then zero
  else if h : q.size = 1 then mulTerm p (q[0]'(by omega)).coeff (q[0]'(by omega)).mon
  else if h : p.size = 1 then mulTerm q (p[0]'(by omega)).coeff (p[0]'(by omega)).mon
  else Id.run do
    -- Distribute over the smaller operand and merge, keeping every intermediate sorted.
    -- Accumulating into one array and sorting at the end costs `O(nm log nm)`; merging
    -- term-by-term costs `O(nm)` and, more importantly, cancels as it goes rather than
    -- carrying cancelling terms through the sort.
    let mut acc : Poly := zero
    for a in p do
      acc := add acc (mulTerm q a.coeff a.mon)
    return acc

/-- `p ^ n`. -/
def pow (p : Poly) : Nat → Poly
  | 0 => const 1
  | n + 1 => mul p (pow p n)

/-- **Exact division.** `divExact p q = some r` exactly when `p = q * r`; `none` when `q`
does not divide `p`.

Standard leading-term cancellation. `Mon.cmp` is a monomial order compatible with
multiplication (multiplying both operands by a fixed monomial shifts every exponent
equally, so the comparison is unchanged), which is what makes the leading term of `q * r`
equal to the product of the leading terms and so makes this algorithm correct.

`fuel` runs out only on inputs far larger than anything the engine produces; exhaustion
returns `none`, which callers treat as "not divisible" — a missed simplification, never a
wrong answer. -/
def divExact (p q : Poly) : Option Poly :=
  if q.isEmpty then none
  else
    let rec go (fuel : Nat) (p : Poly) (acc : Array Term) : Option Poly :=
      match fuel with
      | 0 => none
      | fuel + 1 =>
        if h : p.size = 0 then some acc
        else
          match Mon.div? (p[0]'(by omega)).mon q[0]!.mon with
          | none => none
          | some m =>
            let c := (p[0]'(by omega)).coeff / q[0]!.coeff
            go fuel (sub p (mulTerm q c m)) (acc.push { coeff := c, mon := m })
    go 20000 p #[]

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
