/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Diff.Coherence

/-!
# Completion in action: the machinery rediscovers the integrability condition

The smallest case where coherence has content. Take an unknown `u` of two variables and
prescribe both its first derivatives,

```
δ₁u = a        δ₂u = b
```

`δ₁u` and `δ₂u` are a critical pair — neither is a derivative of the other, but they share
`δ₂δ₁u` — so there is a Δ-polynomial. Both separants are `1`, so it is

```
Δ = δ₂(δ₁u - a) - δ₁(δ₂u - b) = (δ₁₂u - δ₂a) - (δ₁₂u - δ₁b) = δ₁b - δ₂a
```

The leading terms cancel, and what survives is `∂b/∂x = ∂a/∂y` — **the integrability
condition**. The system is coherent exactly when it holds, and completion adds it when it
does not.

This is Clairaut arriving out of the critical-pair machinery rather than being assumed, and
it is the multi-derivation analogue of what `WuDifferential/SurfaceRicci.lean` gets from
`ContDiffAt.isSymmSndFDerivAt` on the analytic side.
-/

namespace Wu
open Poly

-- three indeterminates u, a, b; two derivations; derivatives to total order 3
private def uA : MDiffAtom := { indet := 0, order := #[] }
private def aA : MDiffAtom := { indet := 1, order := #[] }
private def bA : MDiffAtom := { indet := 2, order := #[] }
private def mt : MAtomTable :=
  MAtomTable.build .orderly 2 (MAtomTable.closure #[uA, aA, bA] 2 3)

private def at! (i : Nat) (α : Array Nat) : Nat :=
  (mt.index? { indet := i, order := α }).getD 999
private def u1 : Poly := Poly.var (at! 0 #[1, 0])   -- δ₁u
private def u2 : Poly := Poly.var (at! 0 #[0, 1])   -- δ₂u
private def a  : Poly := Poly.var (at! 1 #[])
private def b  : Poly := Poly.var (at! 2 #[])
private def a2 : Poly := Poly.var (at! 1 #[0, 1])   -- δ₂a
private def b1 : Poly := Poly.var (at! 2 #[1, 0])   -- δ₁b

/-- The system `δ₁u = a`, `δ₂u = b`. -/
private def sys : Array Poly := #[Poly.sub u1 a, Poly.sub u2 b]

/-! ### The system is not coherent as given -/

#guard !isCoherent mt sys

-- Exactly one new relation appears.
#guard (deltaRemainders mt sys).size == 1

-- **And it is the integrability condition** `δ₁b - δ₂a`, up to sign.
#guard (Poly.isZero (Poly.sub (deltaRemainders mt sys)[0]! (Poly.sub b1 a2)))
        || (Poly.isZero (Poly.add (deltaRemainders mt sys)[0]! (Poly.sub b1 a2)))

/-! ### Completion adds it, and then stops -/

#guard (completeCoherent mt sys).size == 3
#guard isCoherent mt (completeCoherent mt sys)

-- Completion is idempotent: nothing further appears on a second pass.
#guard (completeCoherent mt (completeCoherent mt sys)).size == 3

/-! ### With the condition assumed, the system is coherent from the start

Prescribing `a` and `b` that already satisfy `δ₁b = δ₂a` — here the simplest such choice,
both constant in the relevant directions — leaves nothing to add. -/

private def sysFlat : Array Poly := #[Poly.sub u1 a, Poly.sub u2 b, Poly.sub b1 a2]

#guard isCoherent mt sysFlat
#guard (completeCoherent mt sysFlat).size == 3

/-! ### One derivation: coherence is vacuous

The same construction with a single derivation has no critical pairs at all, so every set
is coherent and completion is the identity. This is why nothing in `CharSetTac/Diff/` other
than the multi-index layer ever needed it. -/

private def mt1 : MAtomTable :=
  MAtomTable.build .orderly 1 (MAtomTable.closure #[uA, aA] 1 3)
private def at1! (i : Nat) (α : Array Nat) : Nat :=
  (mt1.index? { indet := i, order := α }).getD 999
private def sys1 : Array Poly :=
  #[Poly.sub (Poly.var (at1! 0 #[1])) (Poly.var (at1! 1 #[])),
    Poly.sub (Poly.var (at1! 0 #[2])) (Poly.var (at1! 1 #[1]))]

#guard isCoherent mt1 sys1
#guard (completeCoherent mt1 sys1).size == 2

end Wu
