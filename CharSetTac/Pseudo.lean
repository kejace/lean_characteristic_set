/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Poly

/-!
# Pseudo-division and reduction for the `wu` tactic

Pseudo-division is the engine's workhorse: dividing `g` by `f` with respect to `f`'s
main variable, after multiplying through by enough powers of `init f` to make the
division exact over the coefficient ring. It satisfies

```
init(f) ^ s * g = q * f + r      with  deg_{mv f} r < deg_{mv f} f
```

which mirrors `MvPolynomial.pseudoOf_equation` in
`CharacteristicSet/PseudoDivision.lean:154`.

## Cofactor tracking

Everything here also comes in a `Tracked` flavour. A `Tracked` value carries a vector of
cofactors expressing the polynomial in terms of the user's original hypotheses:
`poly = ∑ⱼ cof[j] * hⱼ`. This is what ultimately lets the tactic emit a *single*
`linear_combination` identity against the hypotheses rather than against the
characteristic set, which the user never sees. The bookkeeping is the same one
`setPseudo.go` performs at the proof level upstream.

## Reduction

Two notions, matching the two `AscendingSetTheory` instances upstream:

* **Ritt (strong)**: `q` is reduced w.r.t. `p` when `deg_{mv p} q < deg_{mv p} p`.
* **Wu (weak)**: the same test applied to `init q` instead of `q`.
-/

namespace Wu

/-- The result of pseudo-dividing `g` by `f`, satisfying
`init(f) ^ exponent * g = quotient * f + remainder`. -/
structure PseudoResult where
  /-- The power of `init f` that had to be multiplied in. -/
  exponent : Nat
  /-- The quotient. -/
  quotient : Poly
  /-- The remainder, of lower degree in `f`'s main variable than `f` is. -/
  remainder : Poly
  deriving Inhabited

/-- Pseudo-divide `g` by `f` with respect to `f`'s main variable.

If `f` is a nonzero constant this is exact division; if `f` is zero the result is
`g` unchanged, matching upstream's convention. -/
def prem (g f : Poly) : PseudoResult :=
  match f.mainVar? with
  | none =>
    -- `f` is constant: exact division when nonzero, otherwise a no-op.
    if f.isZero then { exponent := 0, quotient := Poly.zero, remainder := g }
    else
      let c := f[0]!.coeff
      { exponent := 0, quotient := Poly.smul (1 / c) g, remainder := Poly.zero }
  | some i =>
    let d := f.degIn i
    let I := f.coeffOf i d
    -- Each iteration cancels the leading term in `x_i`, so `deg_{x_i} r` strictly
    -- decreases; `g.degIn i + 1` is therefore ample fuel.
    let rec go (fuel s : Nat) (q r : Poly) : PseudoResult :=
      match fuel with
      | 0 => { exponent := s, quotient := q, remainder := r }
      | fuel + 1 =>
        let e := r.degIn i
        if r.isZero || e < d then { exponent := s, quotient := q, remainder := r }
        else
          let L := r.coeffOf i e
          let shift : Poly := #[{ coeff := 1, mon := Mon.single i (e - d) }]
          let Lx := Poly.mul L shift
          -- I * r - L * x_i^(e-d) * f   and   I * q + L * x_i^(e-d)
          go fuel (s + 1) (Poly.add (Poly.mul I q) Lx)
            (Poly.sub (Poly.mul I r) (Poly.mul Lx f))
    go (g.degIn i + 1) 0 Poly.zero g

/-- A polynomial together with cofactors expressing it in the original hypotheses:
`poly = ∑ⱼ cof[j] * hⱼ`. -/
structure Tracked where
  /-- The polynomial itself. -/
  poly : Poly
  /-- Cofactors against the original hypothesis list. -/
  cof : Array Poly
  deriving Inhabited

namespace Tracked

/-- The `j`-th hypothesis, tracked as itself: cofactor vector `eⱼ`. -/
def ofHyp (n j : Nat) (p : Poly) : Tracked :=
  { poly := p, cof := (Array.replicate n Poly.zero).set! j (Poly.const 1) }

/-- A polynomial with no dependence on the hypotheses. -/
def ofConst (n : Nat) (p : Poly) : Tracked :=
  { poly := p, cof := Array.replicate n Poly.zero }

/-- Scale a tracked polynomial by a polynomial. -/
def scale (c : Poly) (t : Tracked) : Tracked :=
  { poly := Poly.mul c t.poly, cof := t.cof.map (Poly.mul c) }

/-- Combine: `a - b`, on both the polynomial and its cofactors. -/
def sub (a b : Tracked) : Tracked :=
  { poly := Poly.sub a.poly b.poly
    cof := (Array.range (max a.cof.size b.cof.size)).map fun j =>
      Poly.sub (a.cof.getD j Poly.zero) (b.cof.getD j Poly.zero) }

/-- Pseudo-divide a tracked `g` by a tracked `f`, carrying cofactors through.

From `init(f)^s * g = q * f + r` we get `r = init(f)^s * g - q * f`, so the remainder's
cofactors are `init(f)^s * cof(g) - q * cof(f)`. -/
def prem (g f : Tracked) : Nat × Poly × Tracked :=
  let res := Wu.prem g.poly f.poly
  let I := f.poly.initial
  let Ipow := Poly.pow I res.exponent
  let r : Tracked := sub (scale Ipow g) (scale res.quotient f)
  (res.exponent, res.quotient, { r with poly := res.remainder })

end Tracked

/-- Which notion of reduction to use when building ascending sets. -/
inductive Mode
  /-- Wu's weak (initial) reduction — the classical choice for geometry. -/
  | wu
  /-- Ritt's strong reduction. -/
  | ritt
  deriving Inhabited, BEq, Repr

/-- `q` is Ritt-reduced with respect to `p`: strictly lower degree in `p`'s main variable.

Nothing is reduced with respect to a constant, matching
`MvPolynomial.not_reducedTo_of_bot_max_vars`. -/
def reducedTo (q p : Poly) : Bool :=
  match p.mainVar? with
  | none => false
  | some c => q.degIn c < p.degIn c

/-- `q` is reduced with respect to `p` in the given mode.

Wu's weak reduction applies the same test to `init q`, matching
`WeakAscendingSet.IsAscendingSet` (`CharacteristicSet/AscendingSet.lean:128`). -/
def reducedToIn (mode : Mode) (q p : Poly) : Bool :=
  match mode with
  | .ritt => reducedTo q p
  | .wu => reducedTo q.initial p

/-- `q` is reduced with respect to every element of `ps`. -/
def reducedToSet (mode : Mode) (q : Poly) (ps : Array Poly) : Bool :=
  ps.all fun p => reducedToIn mode q p

end Wu
