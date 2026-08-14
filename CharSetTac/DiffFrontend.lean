/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Frontend
import Mathlib.RingTheory.Derivation.DifferentialRing

/-!
# `wu_diff`: differential goals with automatic prolongation

`wu_diff` proves differential consequences by prolonging the hypotheses and then running
the ordinary algebraic engine with derivatives as atoms.

## Why this is preprocessing, not a new engine

The obvious design would compute formal derivatives inside the engine and then prove that
the computed polynomial matches Lean's `δ` of the hypothesis. That is a lot of work, and
unnecessary: `congrArg` turns `h : a = b` into `a′ = b′` for free, and `simp` with the
Leibniz rules expands `δ` over `+`, `*` and `^` into an ordinary polynomial in the
derivative atoms. After that the *existing* `wu` sees nothing differential at all — just
more atoms and more hypotheses.

So the whole differential frontend is: prolong each equational hypothesis `order` times,
expand, then call `wu`. The `Diff/` engine files remain the route for genuine differential
*elimination* (choosing prolongations by ranking, Δ-polynomials); this tactic covers the
common case where prolonging everything a fixed number of times is enough.

## Usage

```lean
wu_diff                    -- prolong every equational hypothesis once
wu_diff (order := 2)       -- prolong twice
wu_diff (vars := [x, y])   -- as `wu`, pin the variable order
```
-/

open Lean Meta Elab Tactic
open scoped Differential

namespace Wu

/-- The simp set that expands `δ` over ring operations. This is what removes the need for
the engine to know anything about derivations. -/
def derivExpandLemmas : List Name :=
  [``map_add, ``map_sub, ``map_neg, ``map_zero, ``map_one,
   ``Derivation.leibniz, ``Derivation.leibniz_pow, ``smul_eq_mul]

/-- Prolong every equational hypothesis at the goal's type once, expanding with the
Leibniz rules. New hypotheses are added to the context; existing ones are untouched. -/
def prolongOnce : TacticM Unit := withMainContext do
  let goalTy := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  let some (R, _, _) := goalTy.eq? | return
  let mut names : Array Name := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let ty := (← instantiateMVars ldecl.type).consumeMData
    match ty.eq? with
    | some (ty', _, _) => if ← isDefEq ty' R then names := names.push ldecl.userName
    | none => pure ()
  for n in names do
    let hId := mkIdent n
    let newId := mkIdent (n ++ `wuD)
    -- `congrArg` gives `a′ = b′`; `simp only` then expands both sides into the
    -- derivative atoms. If the expansion makes no progress the hypothesis is still
    -- usable, so the simp is wrapped in `try`.
    let tac ← `(tactic|
      have $newId:ident := congrArg (fun z => z′) $hId:ident)
    evalTactic tac
    let simpTac ← `(tactic|
      simp only [map_add, map_sub, map_neg, map_zero, map_one,
        Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
        Nat.cast_ofNat, Nat.add_one_sub_one] at $newId:ident)
    try evalTactic simpTac catch _ => pure ()

/-- `wu_diff` prolongs the equational hypotheses and then runs `wu`. -/
syntax (name := wuDiffTac) "wu_diff"
  (atomic(" (" &"order") " := " num ")")?
  (atomic(" (" &"vars") " := " "[" term,* "]" ")")? : tactic

elab_rules : tactic
  | `(tactic| wu_diff $[(order := $n)]? $[(vars := [$vs,*])]?) => do
    let k := match n with | some m => m.getNat | none => 1
    for _ in [0:k] do
      prolongOnce
    withMainContext do
      let mut cfg : Config := {}
      if let some vsyn := vs then
        let mut es := #[]
        for v in vsyn.getElems do
          es := es.push (← Term.elabTerm v none)
        cfg := { cfg with vars := es }
      wuCore cfg (← getRef) false

end Wu
