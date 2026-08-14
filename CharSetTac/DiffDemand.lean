/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.DiffFrontend

/-!
# Demand-driven prolongation

`wu_pde` prolongs every hypothesis by every derivation, `order` times. That works at first
order and breaks at second: with two derivations it generates every mixed partial of
everything, most of it irrelevant, and the algebraic basic set cannot tell which equations
matter. `CharSetTac/DiffPdeTest.lean` records the failure.

`wu_pde!` chooses instead. The rule is the one differential elimination has always used:

> to reduce something whose leader is `θ·u`, prolong the equation whose leader is `u` by
> exactly `θ` — not to a uniform order.

Run as a closure. Start from the derivatives the *goal* mentions; for each, find the
hypothesis that defines its base and prolong that hypothesis by exactly the missing
multi-index; the new equation mentions further derivatives, so repeat until nothing new
appears.

The prolongations produced are therefore a function of the goal, and nothing is generated
that the goal does not reach. On the harmonicity example this is the difference between 30-odd
irrelevant equations and six relevant ones.

## Scope

This is still preprocessing — the certificate architecture is untouched, the oracle stays
untrusted, and `ring1` remains the checker. What changes is *which* equations the oracle is
given.
-/

open Lean Meta Elab Tactic

namespace Wu

/-- A derivative atom: a base term and the multi-index of derivations applied to it. -/
abbrev DAtom := Expr × Array Nat

/-- Increment component `i`. -/
private def bump (α : Array Nat) (i : Nat) : Array Nat :=
  if h : i < α.size then α.set i (α[i] + 1) else α

/-- Componentwise `≤`, i.e. "is an ancestor of". -/
private def dvdIdx (β α : Array Nat) : Bool :=
  (List.range (max α.size β.size)).all fun i => β.getD i 0 ≤ α.getD i 0

/-- `α - β`, componentwise. -/
private def subIdx (α β : Array Nat) : Array Nat :=
  (Array.range (max α.size β.size)).map fun i => α.getD i 0 - β.getD i 0

private def idxIsZero (α : Array Nat) : Bool := α.all (· == 0)

/-- Is `e` the application of derivation `d`? Derivations are coerced through
`DFunLike.coe`, so this is what an application actually looks like. -/
private def derivApp? (d : Expr) (e : Expr) : MetaM (Option Expr) := do
  let e := e.consumeMData
  unless e.isAppOfArity ``DFunLike.coe 6 do return none
  let args := e.getAppArgs
  if ← isDefEq args[4]! d then return some args[5]! else return none

/-- Peel derivation applications off `e`, returning the base and the multi-index.

`d₁ (d₂ (d₁ x))` becomes `(x, #[2, 1])`. -/
partial def peelDerivs (ds : Array Expr) (e : Expr) : MetaM DAtom := do
  for (d, i) in ds.zipIdx do
    if let some arg ← derivApp? d e then
      let (base, α) ← peelDerivs ds arg
      return (base, bump α i)
  return (e.consumeMData, Array.replicate ds.size 0)

/-- Every maximal derivative atom in `e`.

Traversal stops at a derivation application — that whole term is one atom — and otherwise
descends through the ring operations. -/
partial def collectDAtoms (ds : Array Expr) (e : Expr) : MetaM (Array DAtom) := do
  let e := e.consumeMData
  for d in ds do
    if (← derivApp? d e).isSome then
      return #[← peelDerivs ds e]
  match e with
  | .app f a => return (← collectDAtoms ds f) ++ (← collectDAtoms ds a)
  | _ => return #[]

/-- Are two atoms the same? -/
private def sameAtom (a b : DAtom) : MetaM Bool := do
  if a.2 == b.2 then isDefEq a.1 b.1 else return false

private def memAtoms (as : Array DAtom) (a : DAtom) : MetaM Bool := do
  for b in as do
    if ← sameAtom a b then return true
  return false

/-- The leader of a hypothesis `lhs = rhs`: the derivative atom of `lhs` when the left side
is a bare (possibly differentiated) unknown.

This is what makes a hypothesis *usable as a definition* of that atom, and hence
prolongable to reach its derivatives. A hypothesis whose left side is a compound expression
has no leader in this sense and is passed through untouched. -/
def hypLeader? (ds : Array Expr) (lhs : Expr) : MetaM (Option DAtom) := do
  let atoms ← collectDAtoms ds lhs
  if h : atoms.size = 1 then
    -- the left side is exactly one atom, possibly with zero derivations applied
    let a := atoms[0]'(by omega)
    if ← isDefEq a.1 lhs then return some a
    return some a
  else if atoms.isEmpty then
    -- an undifferentiated unknown such as `u` in `u = x^2 - y^2`
    return some (lhs.consumeMData, Array.replicate ds.size 0)
  else return none

/-- Build `fun z => d₁ (d₂ (… z))` for a multi-index. -/
private def mkProlongFn (dsStx : Array (TSyntax `term)) (α : Array Nat) :
    TermElabM (TSyntax `term) := do
  let mut body ← `(z)
  for (dStx, i) in dsStx.zipIdx do
    for _ in [0 : α.getD i 0] do
      body ← `($dStx $body)
  `(fun z => $body)

/-- One round: for every derivative the goal (or an already-added equation) needs, prolong
the hypothesis that defines its base by exactly the missing multi-index.

Returns `true` when something was added, so the caller can iterate to a fixpoint. -/
def prolongDemandRound (dsStx : Array (TSyntax `term)) (round : Nat) : TacticM Bool :=
  withMainContext do
    let ds ← dsStx.mapM fun s => Term.elabTerm s none
    let goalTy := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
    let some (R, glhs, grhs) := goalTy.eq? | return false
    -- what is currently available, and what is wanted
    let mut avail : Array DAtom := #[]
    let mut defs : Array (Name × DAtom) := #[]
    let mut want : Array DAtom := (← collectDAtoms ds glhs) ++ (← collectDAtoms ds grhs)
    for ldecl in ← getLCtx do
      if ldecl.isImplementationDetail then continue
      let ty := (← instantiateMVars ldecl.type).consumeMData
      let some (ty', lhs, rhs) := ty.eq? | continue
      unless ← isDefEq ty' R do continue
      if let some ld ← hypLeader? ds lhs then
        avail := avail.push ld
        defs := defs.push (ldecl.userName, ld)
      want := want ++ (← collectDAtoms ds rhs)
    -- anything wanted but not defined, whose base *is* defined at a lower index
    let mut added := false
    for a in want do
      if ← memAtoms avail a then continue
      for (nm, ld) in defs do
        if !(← isDefEq ld.1 a.1) then continue
        unless dvdIdx ld.2 a.2 do continue
        let θ := subIdx a.2 ld.2
        if idxIsZero θ then continue
        let fn ← mkProlongFn dsStx θ
        let newId := mkIdent (nm ++ Name.mkSimple s!"d{round}")
        try
          evalTactic (← `(tactic| have $newId:ident := congrArg $fn $(mkIdent nm)))
        catch _ => continue
        try
          evalTactic (← `(tactic|
            simp only [map_add, map_sub, map_neg, map_zero,
        Derivation.map_one_eq_zero,
              Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
              zsmul_eq_mul, Derivation.map_ofNat, Derivation.map_natCast,
              Nat.cast_ofNat, Nat.add_one_sub_one] at $newId:ident))
        catch _ => pure ()
        withMainContext do
          if let some d := (← getLCtx).findFromUserName? (nm ++ Name.mkSimple s!"d{round}") then
            trace[wu] "prolonged {nm} by {θ}: {← instantiateMVars d.type}"
        added := true
        break
    return added

/-- `wu_pde!` prolongs on demand rather than uniformly, then runs `wu`.

```lean
wu_pde! (derivs := [d₁, d₂])              -- closure, default depth 4
wu_pde! (derivs := [d₁, d₂]) (depth := 6)
```
-/
syntax (name := wuPdeDemandTac) "wu_pde!"
  (atomic(" (" &"derivs") " := " "[" term,* "]" ")")
  (atomic(" (" &"depth") " := " num ")")?
  (atomic(" (" &"vars") " := " "[" term,* "]" ")")? : tactic

elab_rules : tactic
  | `(tactic| wu_pde! (derivs := [$ds,*]) $[(depth := $n)]? $[(vars := [$vs,*])]?) => do
    let depth := match n with | some m => m.getNat | none => 4
    let dsStx := ds.getElems
    for round in [0 : depth] do
      unless ← prolongDemandRound dsStx round do break
    withMainContext do
      let mut cfg : Config := {}
      if let some vsyn := vs then
        let mut es := #[]
        for v in vsyn.getElems do
          es := es.push (← Term.elabTerm v none)
        cfg := { cfg with vars := es }
      wuCore cfg (← getRef) false

end Wu
