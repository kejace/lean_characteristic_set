/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Simps.Basic

/-!
# The `wu_unfold` simp set

Lemmas tagged `@[wu_unfold]` are used by `wu` to turn geometric predicates into the
polynomial equations the engine works on, before any reflection happens.

This lives in its own file because a simp attribute must be registered in a module that
is imported before it is used, and both `CharSetTac.Frontend` (which runs the set) and
`WuGeometry` (which populates it) need to see it.
-/

/-- Simp set used by `wu` to unfold geometric predicates into polynomial equations. -/
register_simp_attr wu_unfold
