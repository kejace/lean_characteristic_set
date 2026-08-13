import CharSetTac.CharSet

/-!
# Engine self-tests

These check the *identities* the engine is supposed to satisfy, not just that it runs.
The pseudo-division identity in particular is what the emitted certificate depends on,
so it is checked directly rather than by eyeballing outputs.
-/

namespace Wu
open Poly

private def x (i : Nat) : Poly := Poly.var i
private def c (n : Int) : Poly := Poly.const (n : Rat)

/-- `init(f)^s * g = q * f + r` — the defining identity of pseudo-division. -/
private def premIdentityHolds (g f : Poly) : Bool :=
  let res := prem g f
  let I := f.initial
  let lhs := Poly.mul (Poly.pow I res.exponent) g
  let rhs := Poly.add (Poly.mul res.quotient f) res.remainder
  Poly.isZero (Poly.sub lhs rhs)

/-- The remainder really is reduced in `f`'s main variable. -/
private def premRemainderReduced (g f : Poly) : Bool :=
  match f.mainVar? with
  | none => true
  | some i => let res := prem g f
              res.remainder.isZero || res.remainder.degIn i < f.degIn i

-- basic arithmetic
#guard Poly.isZero (Poly.sub (x 0) (x 0))
#guard (Poly.mul (x 0) (x 1)).degIn 0 == 1
#guard (Poly.add (x 0) (Poly.neg (x 0))).isZero
#guard (Poly.mul (Poly.add (x 0) (c 1)) (Poly.sub (x 0) (c 1)))
        == Poly.sub (Poly.pow (x 0) 2) (c 1)

-- main variable, initial, rank
#guard (Poly.add (Poly.mul (x 2) (x 0)) (x 1)).mainVar? == some 2
#guard (c 5).mainVar? == none
#guard (Poly.add (Poly.mul (x 0) (Poly.pow (x 1) 2)) (x 1)).initial == x 0
#guard (Poly.pow (x 1) 2).mainDeg == 2
#guard rankCmp (x 0) (x 1) == .lt
#guard rankCmp (Poly.pow (x 1) 2) (x 1) == .gt

-- pseudo-division identity on a spread of cases
#guard premIdentityHolds (Poly.pow (x 1) 3) (Poly.sub (Poly.pow (x 1) 2) (x 0))
#guard premIdentityHolds (Poly.add (Poly.pow (x 1) 3) (x 0))
        (Poly.sub (Poly.mul (x 0) (Poly.pow (x 1) 2)) (c 1))
#guard premIdentityHolds (Poly.mul (x 2) (Poly.pow (x 1) 4))
        (Poly.add (Poly.mul (x 0) (x 1)) (x 2))
#guard premIdentityHolds (x 0) (Poly.sub (Poly.pow (x 1) 2) (x 0))
#guard premIdentityHolds (Poly.pow (x 1) 5) (Poly.pow (x 1) 2)

#guard premRemainderReduced (Poly.pow (x 1) 3) (Poly.sub (Poly.pow (x 1) 2) (x 0))
#guard premRemainderReduced (Poly.mul (x 2) (Poly.pow (x 1) 4))
        (Poly.add (Poly.mul (x 0) (x 1)) (x 2))

-- dividing a polynomial by itself leaves no remainder
#guard (prem (Poly.sub (Poly.pow (x 1) 2) (x 0)) (Poly.sub (Poly.pow (x 1) 2) (x 0))).remainder.isZero

-- reduction predicates
#guard reducedTo (x 1) (Poly.pow (x 1) 2)
#guard !reducedTo (Poly.pow (x 1) 2) (x 1)
#guard !reducedTo (x 0) (c 3)   -- nothing is reduced w.r.t. a constant

/-- Cofactor tracking: the tracked polynomial always equals `∑ⱼ cof[j] * hⱼ`. -/
private def cofactorsAgree (hs : Array Poly) (t : Tracked) : Bool :=
  let recomputed := (hs.zip t.cof).foldl (init := Poly.zero) fun acc (h, cf) =>
    Poly.add acc (Poly.mul cf h)
  Poly.isZero (Poly.sub t.poly recomputed)

-- h₀ = x1^2 - x0, h₁ = x2 - x1; reduce h₁ by h₀ and check the cofactors still describe it
private def h0 : Poly := Poly.sub (Poly.pow (x 1) 2) (x 0)
private def h1 : Poly := Poly.sub (x 2) (x 1)
private def hs : Array Poly := #[h0, h1]

#guard cofactorsAgree hs (Tracked.ofHyp 2 0 h0)
#guard cofactorsAgree hs (Tracked.ofHyp 2 1 h1)
#guard cofactorsAgree hs (Tracked.scale (x 0) (Tracked.ofHyp 2 1 h1))
#guard cofactorsAgree hs (Tracked.sub (Tracked.ofHyp 2 0 h0) (Tracked.ofHyp 2 1 h1))

/-- The critical one: after pseudo-division the remainder's cofactors still express it. -/
private def premKeepsCofactors (g f : Tracked) : Bool :=
  cofactorsAgree hs (Tracked.prem g f).2.2

#guard premKeepsCofactors (Tracked.ofHyp 2 1 h1) (Tracked.ofHyp 2 0 h0)
-- note: the tracked value must genuinely equal `∑ⱼ cof[j] * hⱼ`, so scale a real
-- hypothesis rather than pairing an arbitrary polynomial with a unit cofactor.
#guard premKeepsCofactors
        (Tracked.scale (Poly.mul (Poly.pow (x 1) 3) (x 2)) (Tracked.ofHyp 2 1 h1))
        (Tracked.ofHyp 2 0 h0)
#guard premKeepsCofactors
        (Tracked.scale (x 0) (Tracked.ofHyp 2 1 h1)) (Tracked.ofHyp 2 0 h0)


/-! ### Certificate end-to-end -/

/-- The certificate identity: `mult * g = ∑ⱼ cofactors[j] * hⱼ`. -/
private def certificateHolds (mode : Mode) (hs : Array Poly) (g : Poly) : Bool :=
  match solve mode hs g with
  | none => false
  | some c =>
    let lhs := Poly.mul c.mult g
    let rhs := (hs.zip c.cofactors).foldl (init := Poly.zero) fun acc (h, d) =>
      Poly.add acc (Poly.mul d h)
    Poly.isZero (Poly.sub lhs rhs)

/-- `mult` really is the product of its reported `factors`. -/
private def multMatchesFactors (mode : Mode) (hs : Array Poly) (g : Poly) : Bool :=
  match solve mode hs g with
  | none => false
  | some c =>
    let prod := c.factors.foldl (init := Poly.const 1) fun acc (i, e) =>
      Poly.mul acc (Poly.pow i e)
    Poly.isZero (Poly.sub prod c.mult)

-- Parallelogram: x0..x3 and x4..x7 are the two pairs of opposite sides.
-- h₁ = x1 - x0 - (x3 - x2), h₂ = x2 - x0 - (x3 - x1);  conclusion x0 + x3 - (x1 + x2).
private def p1 : Poly := Poly.sub (Poly.sub (x 1) (x 0)) (Poly.sub (x 3) (x 2))
private def p2 : Poly := Poly.sub (Poly.sub (x 2) (x 0)) (Poly.sub (x 3) (x 1))
private def p5 : Poly := Poly.sub (Poly.add (x 0) (x 3)) (Poly.add (x 1) (x 2))

#guard (solve .wu #[p1, p2] p5).isSome
#guard certificateHolds .wu #[p1, p2] p5
#guard multMatchesFactors .wu #[p1, p2] p5
#guard certificateHolds .ritt #[p1, p2] p5

-- a simple triangular system: x1^2 = x0, x2 = x1  ⊢  x2^2 - x0 = 0
private def t1 : Poly := Poly.sub (Poly.pow (x 1) 2) (x 0)
private def t2 : Poly := Poly.sub (x 2) (x 1)
private def tc : Poly := Poly.sub (Poly.pow (x 2) 2) (x 0)

#guard certificateHolds .wu #[t1, t2] tc
#guard multMatchesFactors .wu #[t1, t2] tc
#guard certificateHolds .ritt #[t1, t2] tc

-- a goal that does NOT follow must not produce a certificate
#guard (solve .wu #[t1, t2] (Poly.sub (x 2) (x 0))).isNone

end Wu
