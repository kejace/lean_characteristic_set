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

/-- **A numeral literal is annihilated by any derivation.**

Mathlib has `Derivation.map_natCast`, but it is stated for `Nat.cast n`, and a literal like
`2` elaborates to `OfNat.ofNat 2`. So it never fires on real goals — and without it,
`Derivation.leibniz` applied to `2 * (x * y)` expands to `2 • D (x*y) + (x*y) • D 2` and
leaves that `D 2` alive. The engine then reflects it as a *spurious atom* multiplied by
`x*y`, which silently poisons the characteristic set: the equation for `D v` is no longer
linear in the derivative, and the goal stops reducing.

That failure mode is invisible from the outside — the tactic just reports that the goal does
not follow — which is why this is worth a named lemma rather than a simp-set tweak. -/
@[simp] theorem Derivation.map_ofNat {R A M : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module A M] [Module R M] (D : Derivation R A M)
    (n : ℕ) [n.AtLeastTwo] : D (no_index (OfNat.ofNat n) : A) = 0 := by
  rw [← Nat.cast_ofNat]; exact D.map_natCast _

/-- The simp set that expands `δ` over ring operations. This is what removes the need for
the engine to know anything about derivations. -/
def derivExpandLemmas : List Name :=
  [``map_add, ``map_sub, ``map_neg, ``map_zero,
   ``Derivation.map_one_eq_zero, ``Derivation.map_ofNat, ``Derivation.map_natCast,
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
      simp only [map_add, map_sub, map_neg, map_zero,
        Derivation.map_one_eq_zero,
        Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
        Derivation.map_ofNat, Derivation.map_natCast,
        Nat.cast_ofNat, Nat.add_one_sub_one] at $newId:ident)
    try evalTactic simpTac catch _ => pure ()

/-! ### Several derivations

`wu_diff` uses `Differential.deriv`, of which a ring has exactly one. A PDE system has
several, and Mathlib spells those as explicit `Derivation` terms — which is what
`WuDifferential/PDE.lean` already does by hand.

The generalisation is free: `Derivation.leibniz` is stated for *any* derivation, so
`congrArg (fun z => d z)` followed by the same expansion works for a supplied `d` exactly
as it does for `′`. Prolonging by each derivation in turn, `order` times, generates every
composition up to that total order.

**What this is not.** It does not choose prolongations by ranking, and it does not check
coherence — `CharSetTac/Diff/Coherence.lean` is where that lives, and it is a statement
about the *system* rather than about a goal. This tactic is the same bargain `wu_diff`
struck: prolong everything uniformly and let the algebraic engine do the rest, which covers
the common case and is honest about not being differential elimination. -/

/-- Prolong every equational hypothesis by the supplied derivation, tagging the new
hypotheses with `tag` so repeated rounds do not collide. -/
def prolongOnceBy (dStx : TSyntax `term) (tag : Name) (only : Option (Array Name) := none) :
    TacticM Unit := withMainContext do
  let goalTy := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  let some (R, _, _) := goalTy.eq? | return
  let mut names : Array Name := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if let some sel := only then
      unless sel.contains ldecl.userName do continue
    let ty := (← instantiateMVars ldecl.type).consumeMData
    match ty.eq? with
    | some (ty', _, _) => if ← isDefEq ty' R then names := names.push ldecl.userName
    | none => pure ()
  for n in names do
    let hId := mkIdent n
    let newId := mkIdent (n ++ tag)
    try
      evalTactic (← `(tactic| have $newId:ident := congrArg (fun z => $dStx z) $hId:ident))
    catch _ => continue
    let simpTac ← `(tactic|
      simp only [map_add, map_sub, map_neg, map_zero,
        Derivation.map_one_eq_zero,
        Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
        zsmul_eq_mul, Derivation.map_ofNat, Derivation.map_natCast,
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

/-- `wu_pde` prolongs by each of several derivations, then runs `wu`.

```lean
wu_pde (derivs := [d₁, d₂])              -- prolong once by each
wu_pde (derivs := [d₁, d₂]) (order := 2) -- all compositions to total order 2
```
-/
syntax (name := wuPdeTac) "wu_pde"
  (atomic(" (" &"derivs") " := " "[" term,* "]" ")")
  (atomic(" (" &"order") " := " num ")")?
  (atomic(" (" &"vars") " := " "[" term,* "]" ")")?
  (" [" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| wu_pde (derivs := [$ds,*]) $[(order := $n)]? $[(vars := [$vs,*])]?
        $[[$sel,*]]?) => do
    let k := match n with | some m => m.getNat | none => 1
    let only := sel.map fun s => s.getElems.map (·.getId)
    for round in [0:k] do
      for (d, i) in ds.getElems.zipIdx do
        prolongOnceBy d (Name.mkSimple s!"wuD{i}r{round}") only
    withMainContext do
      let mut cfg : Config := {}
      if let some vsyn := vs then
        let mut es := #[]
        for v in vsyn.getElems do
          es := es.push (← Term.elabTerm v none)
        cfg := { cfg with vars := es }
      wuCore cfg (← getRef) false

end Wu
