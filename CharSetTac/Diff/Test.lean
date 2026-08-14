import CharSetTac.Diff.Derivation

/-! Engine-level checks for the differential layer: derivation identities, not just that
the code runs. -/

namespace Wu
open Poly

-- two indeterminates y (0) and z (1), derivatives up to order 3, orderly ranking
private def tbl : AtomTable :=
  AtomTable.build .orderly
    (AtomTable.closure #[{indet := 0, order := 0}, {indet := 1, order := 0}] 3)

private def idx (i k : Nat) : Nat := (tbl.index? {indet := i, order := k}).getD 999
private def y  : Poly := Poly.var (idx 0 0)
private def y' : Poly := Poly.var (idx 0 1)
private def z  : Poly := Poly.var (idx 1 0)

-- the table really is sorted so that higher order = higher engine index
#guard idx 0 0 < idx 0 1
#guard idx 0 1 < idx 0 2
#guard idx 1 0 < idx 0 1   -- orderly: order dominates, so z < y′

-- δ is a derivation: δ(y) = y′, δ(c) = 0, and Leibniz holds
#guard (Poly.deriv tbl y).get! == y'
#guard (Poly.deriv tbl (Poly.const 5)).get!.isZero
#guard (Poly.deriv tbl (Poly.add y z)).get!
        == Poly.add (Poly.deriv tbl y).get! (Poly.deriv tbl z).get!

/-- Leibniz: `δ(pq) = p·δq + q·δp`. -/
private def leibnizHolds (p q : Poly) : Bool :=
  match Poly.deriv tbl (Poly.mul p q), Poly.deriv tbl p, Poly.deriv tbl q with
  | some d, some dp, some dq =>
    Poly.isZero (Poly.sub d (Poly.add (Poly.mul p dq) (Poly.mul q dp)))
  | _, _, _ => false

#guard leibnizHolds y z
#guard leibnizHolds (Poly.pow y 2) z
#guard leibnizHolds (Poly.add y (Poly.const 1)) (Poly.mul y z)
#guard leibnizHolds (Poly.pow y 3) (Poly.pow z 2)

-- power rule: δ(y^3) = 3y²y′
#guard (Poly.deriv tbl (Poly.pow y 3)).get!
        == Poly.mul (Poly.mul (Poly.const 3) (Poly.pow y 2)) y'

-- separant of  y′ - y²  is 1 (leader y′, coefficient 1)
#guard (Poly.sub y' (Poly.pow y 2)).separant == Poly.const 1

-- separant of  y·y′ - z  w.r.t. leader y′ is y
#guard (Poly.sub (Poly.mul y y') z).separant == y

-- partial reducedness: y″ is NOT partially reduced w.r.t. an equation with leader y′
private def y'' : Poly := Poly.var (idx 0 2)
#guard !partiallyReduced tbl y'' (Poly.sub y' (Poly.pow y 2))
#guard partiallyReduced tbl (Poly.mul y z) (Poly.sub y' (Poly.pow y 2))

end Wu
