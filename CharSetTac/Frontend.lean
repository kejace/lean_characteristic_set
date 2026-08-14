/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Reflect
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
-/

open Lean Meta Elab Tactic Mathlib.Tactic

namespace Wu

/-- A hypothesis usable by `wu`: its local name and the polynomial `a - b`. -/
structure HypInfo where
  /-- The fvar, so we can refer to it in the emitted `linear_combination`. -/
  fvar : Expr
  /-- `a - b` as a polynomial. -/
  poly : Poly

/-- Scale a polynomial so all coefficients are integers, returning the scale used. -/
def integralize (p : Poly) : Nat × Poly :=
  let l := p.foldl (init := (1 : Nat)) fun acc t => Nat.lcm acc t.coeff.den
  (l, if l == 1 then p else Poly.smul (l : Rat) p)

/-- The certificate, rewritten so every emitted polynomial has integer coefficients.

Returns `(scale, factors, cofactors)` with

`(scale * ∏ Iₖ^eₖ) * g = ∑ⱼ dⱼ * hⱼ`

where every `Iₖ` and `dⱼ` has integer coefficients. Each factor is made integral by
scaling, and the resulting constant is pushed onto the cofactors; then any remaining
denominators in the cofactors are cleared by scaling the whole identity. -/
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

/-- Collect hypotheses of the form `a = b` at type `R` from the local context. -/
def collectHyps (R : Expr) : TacticM (Array (Expr × Expr × Expr)) := do
  let mut out := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    match ty.eq? with
    | some (ty', a, b) =>
      if ← isDefEq ty' R then
        out := out.push (ldecl.toExpr, a, b)
    | none => pure ()
  return out

/-- Build the `M ≠ 0` side goal as `L * I₁^e₁ * ⋯ ≠ 0`, and emit it factored. -/
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
def dischargeNondeg : TacticM Unit := do
  evalTactic (← `(tactic|
    repeat' first
      | apply mul_ne_zero
      | apply pow_ne_zero))
  evalTactic (← `(tactic| all_goals try assumption))
  evalTactic (← `(tactic| all_goals try norm_num))
  -- `norm_num` may normalise a goal into exactly a hypothesis (e.g. `-a ≠ 0` to `a ≠ 0`),
  -- so try `assumption` once more on whatever it left behind.
  evalTactic (← `(tactic| all_goals try assumption))

/-- The core of the tactic. -/
def wuCore (mode : Mode) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)
  let some (R, lhs, rhs) := goalTy.eq?
    | throwError "wu: the goal must be an equation `a = b`, got{indentExpr goalTy}"
  let hyps ← collectHyps R
  -- reflect everything in one `AtomM` run so atom indices are shared; `AtomM.run`
  -- discards the final state, so read the atom list from inside the monad
  let (hs, g, atoms) ← AtomM.run .instances do
    let hs ← hyps.mapM fun (fv, a, b) => do
      let pa ← toPoly a
      let pb ← toPoly b
      return ({ fvar := fv, poly := Poly.sub pa pb } : HypInfo)
    let gl ← toPoly lhs
    let gr ← toPoly rhs
    let st ← get
    return (hs, Poly.sub gl gr, st.atoms)
  let hypPolys := hs.map (·.poly)
  let some cert := solve mode hypPolys g
    | throwError "wu: Wu's method did not reduce the goal to zero.\n\
        This means the goal does not follow generically from the hypotheses.\n\
        Hypotheses used: {hypPolys.size}"
  let (scale, factors, cofs) := cert.integralForm
  -- M = scale * ∏ Iₖ^eₖ, emitted factored so `M ≠ 0` decomposes
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
  evalTactic (← `(tactic|
    have wu_key : $Mstx * ($lhsStx - $rhsStx) = 0 := by linear_combination $combStx:term))
  evalTactic (← `(tactic|
    refine sub_eq_zero.mp ((mul_eq_zero_iff_left ?wu_nd).mp wu_key)))
  -- try to discharge the nondegeneracy conditions, leaving the rest to the user
  dischargeNondeg

/-- `wu` proves an equational goal from equational hypotheses using Wu's characteristic
set method, leaving any nondegeneracy conditions it cannot discharge as side goals. -/
elab "wu" : tactic => wuCore .wu

end Wu
