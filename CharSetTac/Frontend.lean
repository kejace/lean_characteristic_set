/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Reflect
import CharSetTac.Attr
import Mathlib.Tactic.LinearCombination

/-!
# The `wu` tactic

Proves goals of the form `lhs = rhs` in a commutative ring with no zero divisors, from
hypotheses of the form `a = b`, using Wu's characteristic set method.

## How the proof is built

The engine returns a certificate `mult * g = ∑ⱼ dⱼ * hⱼ` where `g = lhs - rhs`. The tactic
emits

```lean
have wu_key : M * (lhs - rhs) = 0 := by linear_combination d₁ * h₁ + ⋯ + dₙ * hₙ
refine sub_eq_zero.mp ((mul_eq_zero_iff_left ?wu_nd).mp wu_key)
```

`linear_combination` checks `M * (lhs - rhs) - ∑ⱼ dⱼ * (aⱼ - bⱼ) = 0` with `ring1`, which
is exactly the certificate identity. **Nothing about the engine is trusted**: if the
certificate is wrong, `ring1` fails and the tactic reports failure rather than producing
an unsound proof.

`M` is emitted in *factored* form `L * I₁^e₁ * ⋯ * I_k^e_k` rather than expanded, so that
the remaining `M ≠ 0` goal decomposes through `mul_ne_zero`/`pow_ne_zero` into one
nondegeneracy condition per initial — which is what the user needs to see. Wu's method is
only generically valid, and these conditions are exactly the degenerate configurations
being excluded.

## Syntax

```lean
wu                          -- default: Wu (weak) reduction, atom order by first appearance
wu (algo := ritt)           -- Ritt (strong) reduction instead
wu (vars := [x, y, z])      -- pin the variable order: earlier = freer parameter
wu [h₁, h₂]                 -- use only these hypotheses
wu?                         -- also print a self-contained, pasteable proof
```

The variable order matters: the engine treats *larger* indices as later/dependent, and a
polynomial's main variable is its largest index. A bad order can make Wu's method slow or
fail outright, so `(vars := ...)` is the escape hatch when first-appearance order is wrong.

`set_option trace.wu true` reports the reflected polynomials and the computed
characteristic set.
-/

open Lean Meta Elab Tactic Mathlib.Tactic

namespace Wu

initialize registerTraceClass `wu

/-- A hypothesis usable by `wu`: its fvar and the polynomial `a - b`. -/
structure HypInfo where
  /-- The fvar, so we can refer to it in the emitted `linear_combination`. -/
  fvar : Expr
  /-- The user-facing name, used when printing a pasteable proof for `wu?`. -/
  name : Name
  /-- `a - b` as a polynomial. -/
  poly : Poly

/-- Configuration for `wu`. -/
structure Config where
  /-- Which reduction to use when building ascending sets. -/
  mode : Mode := .wu
  /-- If nonempty, pin these expressions to variable indices `0, 1, 2, …` in order. -/
  vars : Array Expr := #[]
  /-- If `some`, restrict to these hypotheses. -/
  hyps : Option (Array Expr) := none

/-- Scale a polynomial so all coefficients are integers, returning the scale used. -/
def integralize (p : Poly) : Nat × Poly :=
  let l := p.foldl (init := (1 : Nat)) fun acc t => Nat.lcm acc t.coeff.den
  (l, if l == 1 then p else Poly.smul (l : Rat) p)

/-- The certificate, rewritten so every emitted polynomial has integer coefficients.

Returns `(scale, factors, cofactors)` with `(scale * ∏ Iₖ^eₖ) * g = ∑ⱼ dⱼ * hⱼ`. -/
def Certificate.integralForm (c : Certificate) :
    Nat × Array (Poly × Nat) × Array Poly :=
  -- Split the factors. A *constant* initial carries no nondegeneracy content — it is a
  -- nonzero number, so `I ≠ 0` is not a condition on the configuration — and emitting it
  -- as a factor produces junk side goals like `(-1)^2 ≠ 0`. Fold those into a rational
  -- scale and keep only the genuine, variable-carrying initials as factors.
  let (k, factors) := c.factors.foldl (init := ((1 : Rat), (#[] : Array (Poly × Nat))))
    fun (k, fs) (I, e) =>
      match I.mainVar? with
      | none =>
        -- an initial of a nonzero polynomial is nonzero, so the fallback is unreachable;
        -- use 1 rather than 0 so a malformed certificate cannot divide by zero here
        let v : Rat := if I.isZero then 1 else I[0]!.coeff
        (k / v ^ e, fs)
      | some _ =>
        let (l, I') := integralize I
        -- Normalise the sign so the user sees `a ≠ 0` rather than `-a ≠ 0`. Negating a
        -- factor contributes `(-1)^e`, which is folded back into the scale.
        if !I'.isZero && I'[0]!.coeff < 0 then
          (k * (l : Rat) ^ e * (-1 : Rat) ^ e, fs.push (Poly.neg I', e))
        else
          (k * (l : Rat) ^ e, fs.push (I', e))
  -- now `(∏ Iₖ'^eₖ) * g = k * ∑ dⱼ hⱼ`
  let cofs := c.cofactors.map (Poly.smul k)
  -- clear any denominators, in the cofactors and in `k` itself
  let l := cofs.foldl (init := (1 : Nat)) fun acc p =>
    p.foldl (init := acc) fun acc t => Nat.lcm acc t.coeff.den
  (l, factors, if l == 1 then cofs else cofs.map (Poly.smul (l : Rat)))

/-- Collect hypotheses of the form `a = b` at type `R`, optionally restricted to a given
set of fvars. -/
def collectHyps (R : Expr) (only : Option (Array Expr)) :
    TacticM (Array (Expr × Name × Expr × Expr)) := do
  let mut out := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if let some sel := only then
      unless sel.any (· == ldecl.toExpr) do continue
    let ty := (← instantiateMVars ldecl.type).consumeMData
    match ty.eq? with
    | some (ty', a, b) =>
      if ← isDefEq ty' R then
        out := out.push (ldecl.toExpr, ldecl.userName, a, b)
    | none => pure ()
  return out

/-- Build `M = L * I₁^e₁ * ⋯`, factored so that `M ≠ 0` decomposes. -/
def mkMultExpr (R : Expr) (atoms : Array Expr) (scale : Nat)
    (factors : Array (Poly × Nat)) : MetaM Expr := do
  let mut acc ← mkIntLit R (scale : Int)
  for (I, e) in factors do
    let Ie ← polyToExpr R atoms I
    let f ← if e == 1 then pure Ie else mkAppM ``HPow.hPow #[Ie, mkRawNatLit e]
    acc ← mkAppM ``HMul.hMul #[acc, f]
  return acc

/-- Split a nondegeneracy goal `L * I₁^e₁ * ⋯ ≠ 0` into one goal per initial, then
discharge what we can: numeral factors by `norm_num`, and initials the user has already
assumed nonzero by `assumption`. Whatever survives is a genuine degenerate configuration
the user must rule out, and is left as a side goal. -/
def dischargeNondeg (factors : Array (Poly × Nat)) : TacticM Unit := do
  -- Split structurally, mirroring how `mkMultExpr` associated the product, rather than
  -- by blind `repeat' apply`. Applying `pow_ne_zero` by search unifies against non-powers
  -- (via `npowRec`) and produces junk goals like `¬npowRec 0 x = 0`.
  let mut t : TSyntax `term ← `(?_)
  for (_, e) in factors do
    let f ← if e == 1 then `(?_) else `(pow_ne_zero _ ?_)
    t ← `(mul_ne_zero $t $f)
  evalTactic (← `(tactic| refine $t))
  -- `polyToExpr` emits differences as `a + -b`, so fold them back into `a - b` first:
  -- otherwise neither `assumption` against a user's `x - y ≠ 0` nor `sub_ne_zero` can
  -- match, since `sub_ne_zero` is stated about `?a - ?b`.
  evalTactic (← `(tactic| all_goals try rw [← sub_eq_add_neg]))
  evalTactic (← `(tactic| all_goals try assumption))
  -- A condition `x - y ≠ 0` is most naturally written by the user as `x ≠ y`.
  evalTactic (← `(tactic| all_goals try (apply sub_ne_zero.mpr; assumption)))
  -- Normalise both goal and context to a common form before matching: the emitted
  -- multiplier and the user's hypothesis are often equal only up to ring normalisation
  -- (`2*(E*G) + -(2*F^2)` versus `2*(E*G) - 2*F^2`).
  evalTactic (← `(tactic| all_goals try (ring_nf at * <;> assumption)))
  evalTactic (← `(tactic| all_goals try norm_num))
  -- `norm_num` may factor a product condition into a conjunction (`b * c ≠ 0` becomes
  -- `b ≠ 0 ∧ c ≠ 0`), so split those before the final `assumption` pass. It may also
  -- normalise a goal into exactly a hypothesis (`-a ≠ 0` to `a ≠ 0`).
  evalTactic (← `(tactic| all_goals try (repeat' constructor)))
  evalTactic (← `(tactic| all_goals try assumption))
  evalTactic (← `(tactic| all_goals try (apply sub_ne_zero.mpr; assumption)))

/-- Split conjunctive hypotheses.

Geometric predicates like `Midpoint` unfold to `p ∧ q` (one equation per coordinate), and
`wu` only consumes hypotheses that are equations, so the conjunctions have to be taken
apart first. -/
partial def splitConjunctions : TacticM Unit := withMainContext do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if (← instantiateMVars ldecl.type).consumeMData.isAppOf ``And then
      let subgoals ← (← getMainGoal).cases ldecl.fvarId
      if h : subgoals.size = 1 then
        replaceMainGoal [subgoals[0].mvarId]
        splitConjunctions
      return

/-- Unfold `@[wu_unfold]` predicates and split the resulting conjunctions.

Runs before reflection so that goals stated with geometric predicates reduce to the
polynomial equations the engine understands. -/
def preprocess : TacticM Unit := do
  evalTactic (← `(tactic| try simp only [wu_unfold] at *))
  splitConjunctions

/-- The core of the tactic. With `suggest`, also print a self-contained pasteable proof. -/
def wuCore (cfg : Config) (ref : Syntax) (suggest : Bool) : TacticM Unit := withMainContext do
  preprocess
  withMainContext do
  let goal ← getMainGoal
  -- `.consumeMData` matters: tactics such as `simp` and `have` leave `mdata`
  -- wrappers, which pretty-print transparently but are not applications, so `Expr.eq?`
  -- silently returns `none` on them and `wu` would reject a perfectly good equation.
  let goalTy := (← instantiateMVars (← goal.getType)).consumeMData
  let some (R, lhs, rhs) := goalTy.eq?
    | throwError "wu: the goal must be an equation `a = b`, got{indentExpr goalTy}"
  let hyps ← collectHyps R cfg.hyps
  if hyps.isEmpty then
    throwError "wu: no usable hypotheses. `wu` needs hypotheses of the form `a = b` at \
      the same type as the goal."
  -- Reflect everything in one `AtomM` run so atom indices are shared. `AtomM.run`
  -- discards the final state, so read the atom list from inside the monad. Configured
  -- variables are interned first, which is what pins the variable order.
  let (hs, g, atoms) ← AtomM.run .instances do
    for v in cfg.vars do
      let _ ← AtomM.addAtom v
    let hs ← hyps.mapM fun (fv, nm, a, b) => do
      let pa ← toPoly a
      let pb ← toPoly b
      return ({ fvar := fv, name := nm, poly := Poly.sub pa pb } : HypInfo)
    let gl ← toPoly lhs
    let gr ← toPoly rhs
    let st ← get
    return (hs, Poly.sub gl gr, st.atoms)
  let hypPolys := hs.map (·.poly)
  trace[wu] "hypotheses: {hypPolys.map (·.toString)}"
  trace[wu] "goal polynomial: {g.toString}"
  let some cert := solve cfg.mode hypPolys g
    | throwError "wu: Wu's method did not reduce the goal to zero.\n\
        The goal does not follow generically from the {hypPolys.size} hypotheses used.\n\
        If the variable order is wrong, try `wu (vars := [...])`; \
        for the stronger reduction, `wu (algo := ritt)`."
  trace[wu] "characteristic set: {cert.charSet.map (·.toString)}"
  let (scale, factors, cofs) := cert.integralForm
  let M ← mkMultExpr R atoms scale factors
  let Mstx ← Term.exprToSyntax M
  let lhsStx ← Term.exprToSyntax lhs
  let rhsStx ← Term.exprToSyntax rhs
  -- the linear combination ∑ⱼ dⱼ * hⱼ
  let mut comb : Option (TSyntax `term) := none
  for (h, d) in hs.zip cofs do
    if d.isZero then continue
    let dStx ← Term.exprToSyntax (← polyToExpr R atoms d)
    let hStx ← Term.exprToSyntax h.fvar
    let piece ← `($dStx * $hStx)
    comb := some (← match comb with
      | none => pure piece
      | some c => `($c + $piece))
  let combStx := comb.getD (← `((0 : $(← Term.exprToSyntax R))))
  -- **When the multiplier is `1` the ring need not be a domain.** Cancelling `M` uses
  -- `mul_eq_zero_iff_left`, which wants `NoZeroDivisors`; but with `M = 1` there is
  -- nothing to cancel, and demanding a domain anyway would rule out exactly the rings one
  -- most wants to instantiate at — rings of functions, where bump functions with disjoint
  -- support are zero divisors. See `WuDifferential/Manifold.lean`.
  let trivialMult := scale == 1 && factors.isEmpty
  let keyTac ←
    if trivialMult then
      `(tactic| have wu_key : $lhsStx - $rhsStx = 0 := by linear_combination $combStx:term)
    else
      `(tactic|
        have wu_key : $Mstx * ($lhsStx - $rhsStx) = 0 := by linear_combination $combStx:term)
  let finishTac ←
    if trivialMult then
      `(tactic| exact sub_eq_zero.mp wu_key)
    else
      `(tactic| refine sub_eq_zero.mp ((mul_eq_zero_iff_left ?wu_nd).mp wu_key))
  if suggest then
    -- The syntax used for elaboration wraps `Expr`s opaquely, which pretty-prints as
    -- `?m✝` and is useless to paste. Rebuild a display version from *delaborated*
    -- expressions and the hypotheses' real user-facing names.
    let Mdisp ← PrettyPrinter.delab M
    let lhsDisp ← PrettyPrinter.delab lhs
    let rhsDisp ← PrettyPrinter.delab rhs
    let mut combDisp : Option (TSyntax `term) := none
    for (h, d) in hs.zip cofs do
      if d.isZero then continue
      let dDisp ← PrettyPrinter.delab (← polyToExpr R atoms d)
      let hIdent := mkIdent h.name
      let piece ← `($dDisp * $hIdent)
      combDisp := some (← match combDisp with
        | none => pure piece
        | some c => `($c + $piece))
    let combDispStx := combDisp.getD (← `(0))
    -- Use `mkIdent` rather than quotation-literal names: identifiers written inside a
    -- quotation are hygienic and render with `✝` markers, which would make the printed
    -- proof un-pasteable — the one thing `wu?` exists to provide.
    let keyId := mkIdent (Name.mkSimple "wu_key")
    let subEqId := mkIdent ``sub_eq_zero
    let mulEqId := mkIdent ``mul_eq_zero_iff_left
    let mpId := mkIdent ``Iff.mp
    let script ←
      if trivialMult then
        `(tacticSeq|
          have $keyId:ident : $lhsDisp - $rhsDisp = 0 := by
            linear_combination $combDispStx:term
          exact $mpId $subEqId $keyId)
      else
        `(tacticSeq|
          have $keyId:ident : $Mdisp * ($lhsDisp - $rhsDisp) = 0 := by
            linear_combination $combDispStx:term
          refine $mpId $subEqId ($mpId ($mulEqId ?_) $keyId))
    Meta.Tactic.TryThis.addSuggestion ref script
    unless factors.isEmpty do
      let conds ← factors.mapM fun (I, _) => do
        return (← PrettyPrinter.delab (← polyToExpr R atoms I))
      logInfo m!"wu: nondegeneracy conditions (each must be nonzero): {conds.map (·.raw)}"
  evalTactic keyTac
  evalTactic finishTac
  -- With a trivial multiplier `finishTac` closes the goal outright, leaving nothing for
  -- the nondegeneracy discharger to act on.
  unless trivialMult do dischargeNondeg factors

/-- `wu` proves an equational goal from equational hypotheses using Wu's characteristic
set method, leaving any nondegeneracy conditions it cannot discharge as side goals.

`wu?` additionally prints a self-contained proof that does not depend on the oracle. -/
-- `atomic` on the `(keyword` prefixes so the parser can backtrack: without it, seeing
-- `(` commits to the `algo` branch and `wu (vars := ...)` fails to parse.
--
-- `wu?` is a single token rather than `wu` followed by an optional `?`, matching the
-- convention of `exact?`/`apply?`: as two tokens the optional-atom capture does not bind
-- and the elaborator never fires.
syntax (name := wuTac) "wu"
  (atomic(" (" &"algo") " := " ident ")")?
  (atomic(" (" &"vars") " := " "[" term,* "]" ")")?
  (" [" term,* "]")? : tactic

@[inherit_doc wuTac]
syntax (name := wuTacQ) "wu?"
  (atomic(" (" &"algo") " := " ident ")")?
  (atomic(" (" &"vars") " := " "[" term,* "]" ")")?
  (" [" term,* "]")? : tactic

/-- Build a `Config` from the optional syntax pieces shared by `wu` and `wu?`. -/
def mkConfig (algo : Option Syntax.Ident) (vs : Option (Syntax.TSepArray `term ","))
    (hs : Option (Syntax.TSepArray `term ",")) : TacticM Config := do
  let mut cfg : Config := {}
  if let some a := algo then
    match a.getId.toString with
    | "wu" => cfg := { cfg with mode := .wu }
    | "ritt" => cfg := { cfg with mode := .ritt }
    | s => throwErrorAt a "wu: unknown algorithm `{s}`; expected `wu` or `ritt`"
  if let some vsyn := vs then
    let mut es := #[]
    for v in vsyn.getElems do
      es := es.push (← Term.elabTerm v none)
    cfg := { cfg with vars := es }
  if let some hsyn := hs then
    let mut fvs := #[]
    for h in hsyn.getElems do
      fvs := fvs.push (← Term.elabTerm h none)
    cfg := { cfg with hyps := some fvs }
  return cfg

elab_rules : tactic
  | `(tactic| wu $[(algo := $algo:ident)]? $[(vars := [$vs,*])]? $[[$hs,*]]?) => do
    wuCore (← mkConfig algo vs hs) (← getRef) false
  | `(tactic| wu? $[(algo := $algo:ident)]? $[(vars := [$vs,*])]? $[[$hs,*]]?) => do
    wuCore (← mkConfig algo vs hs) (← getRef) true

end Wu
