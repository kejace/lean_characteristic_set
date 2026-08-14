import CharSetTac.Diff.MultiIndex

/-! Checks for the multi-index layer: the Leibniz rule per direction, that mixed partials
commute, and — the point of the file — that critical pairs exist with two derivations and
never with one. -/

namespace Wu
open Poly

-- one indeterminate u, two derivations, derivatives up to total order 3
private def u0 : MDiffAtom := { indet := 0, order := #[] }
private def v0 : MDiffAtom := { indet := 1, order := #[] }
private def mt : MAtomTable :=
  MAtomTable.build .orderly 2 (MAtomTable.closure #[u0, v0] 2 3)

private def at! (i : Nat) (α : Array Nat) : Nat :=
  (mt.index? { indet := i, order := α }).getD 999
private def u   : Poly := Poly.var (at! 0 #[])
private def u1  : Poly := Poly.var (at! 0 #[1, 0])   -- δ₁u
private def u2  : Poly := Poly.var (at! 0 #[0, 1])   -- δ₂u
private def u12 : Poly := Poly.var (at! 0 #[1, 1])   -- δ₂δ₁u

-- the closure contains the mixed partial, and indices respect the ranking
#guard at! 0 #[1,1] != 999
#guard at! 0 #[] < at! 0 #[1,0]
#guard at! 0 #[1,0] < at! 0 #[1,1]

-- δ in each direction behaves
#guard (Poly.derivInM mt 0 u).get! == u1
#guard (Poly.derivInM mt 1 u).get! == u2
#guard (Poly.derivInM mt 1 u1).get! == u12

/-- Mixed partials commute: `δ₂δ₁ p = δ₁δ₂ p`. -/
private def commutes (p : Poly) : Bool :=
  match Poly.derivInM mt 1 ((Poly.derivInM mt 0 p).getD Poly.zero),
        Poly.derivInM mt 0 ((Poly.derivInM mt 1 p).getD Poly.zero) with
  | some a, some b => Poly.isZero (Poly.sub a b)
  | _, _ => false

#guard commutes u
#guard commutes (Poly.pow u 2)
#guard commutes (Poly.mul u u1)

/-- Leibniz per direction. -/
private def leibnizIn (i : Nat) (p q : Poly) : Bool :=
  match Poly.derivInM mt i (Poly.mul p q), Poly.derivInM mt i p, Poly.derivInM mt i q with
  | some d, some dp, some dq =>
    Poly.isZero (Poly.sub d (Poly.add (Poly.mul p dq) (Poly.mul q dp)))
  | _, _, _ => false

#guard leibnizIn 0 u u1
#guard leibnizIn 1 (Poly.pow u 2) u2

-- multi-index derivative composition
#guard (Poly.derivM mt u #[1,1]).get! == u12
#guard (Poly.derivM mt u #[0,0]).get! == u

/-! ### Critical pairs: the actual point -/

-- δ₁u and δ₂u are a critical pair: neither is a derivative of the other, but they have a
-- common derivative δ₂δ₁u. This is what cannot happen with a single derivation.
#guard MDiffAtom.isCriticalPair { indet := 0, order := #[1,0] } { indet := 0, order := #[0,1] }
#guard ({ indet := 0, order := #[1,0] } : MDiffAtom).lcm { indet := 0, order := #[0,1] }
        == { indet := 0, order := #[1,1] }

-- a derivative and its ancestor are NOT a critical pair
#guard !MDiffAtom.isCriticalPair { indet := 0, order := #[1,0] } { indet := 0, order := #[2,0] }
-- different indeterminates are never a critical pair
#guard !MDiffAtom.isCriticalPair { indet := 0, order := #[1,0] } { indet := 1, order := #[0,1] }
-- with ONE derivation nothing is ever a critical pair: any two orders are comparable
#guard !MDiffAtom.isCriticalPair { indet := 0, order := #[1] } { indet := 0, order := #[3] }
#guard !MDiffAtom.isCriticalPair { indet := 0, order := #[2] } { indet := 0, order := #[2] }

-- the Δ-polynomial of a genuine critical pair exists and has lower rank than the lcm
private def p₁ : Poly := Poly.sub u1 (Poly.pow u 2)      -- δ₁u = u²
private def p₂ : Poly := Poly.sub u2 (Poly.mul u u)      -- δ₂u = u·u

#guard (deltaPoly mt p₁ p₂).isSome
#guard (deltaPoly mt p₁ p₂).get!.degIn (at! 0 #[1,1]) == 0   -- leading terms cancelled

-- no Δ-polynomial when the pair is not critical
#guard (deltaPoly mt p₁ (Poly.sub u12 u)).isNone

end Wu
