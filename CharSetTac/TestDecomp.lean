/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Frontend
import Mathlib.Data.Real.Basic

/-!
# `wu!` — zero decomposition

`wu` proves a goal on the *generic* component and reports the degenerate cases as side
goals. Every `I ≠ 0` it hands back is a component it declined to visit. `wu!` visits them.

The tests below pin the three behaviours that matter: it proves what holds everywhere, it
still fails on what does not, and it says *where* the failure is.
-/

section
variable (a b c x y : ℝ)

/-! ### It proves what holds on every component -/

/-- The generic argument divides by `a`; the degenerate branch `a = 0` forces `b = 0` and
`c = 0`, so both sides vanish there. `wu!` finds both. -/
example (h1 : a * x = b) (h2 : a * y = c) : c * x = b * y := by wu!

/-! ### It does not prove what is false somewhere

`x = y` genuinely fails at `a = 0`, and no amount of decomposition can fix that. The point
of the test is that `wu!` *stops* rather than quietly leaving a side goal that looks
dischargeable. -/

example (h : a * x = a * y) : True := by
  fail_if_success (have : x = y := by wu!)
  trivial

/-- With the hypothesis the theorem actually depends on, the generic branch is all there
is and plain `wu` suffices. -/
example (h : a * x = a * y) (ha : a ≠ 0) : x = y := by wu

/-! ### Bounded recursion

`(depth := 0)` degrades to plain `wu`, leaving the conditions as side goals — so the
decomposition is opt-in at every level and a runaway split is impossible. -/

example (h : a * x = a * y) (ha : a ≠ 0) : x = y := by
  wu! (depth := 0)

end
