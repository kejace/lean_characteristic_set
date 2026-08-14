/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Real.Basic

/-!
# What certificate checking actually costs

The engine is an oracle; the cost that survives into the kernel is `ring1` verifying the
certificate. This file pins down what drives that cost, because the answer decides whether
a structured (categorified) proof encoding would help.

**The claim under test.** That kernel cost is driven by coefficient count, and a structured
encoding would collapse it — "from millions of polynomial coefficients to a few functor
applications".

**The measurement.** Same goal, same hypothesis, no oracle, differing only in whether the
multiplier is handed to `linear_combination` factored or pre-expanded. Re-measure with
`#count_heartbeats in` and `set_option Elab.async false` — without the latter you time the
signature and not the proof.

```
deg 6, multiplier written factored  `(a+b+c)^6`   1622 heartbeats
deg 6, multiplier written expanded  (28 terms)    3218
```

**Finding 1: representation is worth about 2×.** Handing over the compact form is half the
cost of handing over the expanded one, for the identical goal.

```
(a+b+c)^3 · h    normal form 10 terms     538 heartbeats    54 / term
(a+b+c)^6 · h    normal form 28 terms    1622               58 / term
(a+b+c)^9 · h    normal form 55 terms    4537               82 / term
```

**Finding 2: but cost still tracks the normal form.** Even with the *most compact possible*
input — three syntactic nodes — the cost grows with the expanded size, because `ring1` must
expand to verify. Roughly linear, drifting superlinear.

## What this means

Both halves matter and they point in different directions.

A structured encoding plausibly buys a **constant factor**, and that factor is real: our own
engine currently expands its cofactors before emitting them, which puts us on the wrong side
of the 2×. Emitting them factored is a cheap improvement and does not need any category
theory.

It does **not** buy the collapse. The normal form is irreducible content: whatever the proof
term looks like, something has to establish that two polynomials are equal, and that costs
in proportion to how big they are. "A few functor applications" would still have to be
checked, and checking them means computing the composite.

So the honest verdict on the categorification proposal is *partially supported*: the
intuition that representation matters is correct and measurable, the claimed
order-of-magnitude collapse is not. That is a poor return on three phases of new
foundations, and a good return on changing what the emitter prints.
-/

namespace Wu.BenchChecking

/-- Multiplier handed over factored. Measured at 1622 heartbeats. -/
example (a b c x y : ℝ) (h : x = y) :
    (a + b + c) ^ 6 * x = (a + b + c) ^ 6 * y := by
  linear_combination (a + b + c) ^ 6 * h

/-- The same goal with the multiplier pre-expanded. Measured at 3218 heartbeats — twice the
cost, for identical mathematical content. -/
example (a b c x y : ℝ) (h : x = y) :
    (a + b + c) ^ 6 * x = (a + b + c) ^ 6 * y := by
  linear_combination (a^6 + 6*a^5*b + 6*a^5*c + 15*a^4*b^2 + 30*a^4*b*c + 15*a^4*c^2
    + 20*a^3*b^3 + 60*a^3*b^2*c + 60*a^3*b*c^2 + 20*a^3*c^3 + 15*a^2*b^4 + 60*a^2*b^3*c
    + 90*a^2*b^2*c^2 + 60*a^2*b*c^3 + 15*a^2*c^4 + 6*a*b^5 + 30*a*b^4*c + 60*a*b^3*c^2
    + 60*a*b^2*c^3 + 30*a*b*c^4 + 6*a*c^5 + b^6 + 6*b^5*c + 15*b^4*c^2 + 20*b^3*c^3
    + 15*b^2*c^4 + 6*b*c^5 + c^6) * h

/-- Scaling, all maximally factored: 538, 1622, 4537 heartbeats for normal forms of 10, 28
and 55 terms. Compactness of the *input* does not stop the cost tracking the *output*. -/
example (a b c x y : ℝ) (h : x = y) :
    (a + b + c) ^ 3 * x = (a + b + c) ^ 3 * y := by
  linear_combination (a + b + c) ^ 3 * h

example (a b c x y : ℝ) (h : x = y) :
    (a + b + c) ^ 9 * x = (a + b + c) ^ 9 * y := by
  linear_combination (a + b + c) ^ 9 * h

end Wu.BenchChecking
