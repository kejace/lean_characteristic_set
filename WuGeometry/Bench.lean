/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WuGeometry.Basic

/-!
# Timing harness for the `wu` benchmark

`#wu_bench` wraps a declaration, elaborates it, and reports how long that took. Because it
elaborates the *actual* declaration, a theorem that fails to prove still fails the build —
the harness cannot mask a broken entry, and there is no way for a benchmark row to be
silently skipped.

**`Elab.async` is switched off for the wrapped declaration**, and that is not incidental.
Lean elaborates proof bodies on background tasks, so `elabCommand` returns as soon as the
*signature* is processed. Timing it without this gives the cost of reading the statement,
not of proving it: a `wu` proof that genuinely takes a minute was reported as 15 ms. Every
number this harness printed before that option was set was wrong by orders of magnitude.
-/

open Lean Elab Command

/-- Elaborate a declaration and report its elaboration time.

Usage: `#wu_bench theorem foo (h : ...) : ... := by wu`. -/
syntax (name := wuBench) "#wu_bench " command : command

@[command_elab wuBench]
def elabWuBench : CommandElab := fun stx => do
  match stx with
  | `(#wu_bench $decl:command) => do
    -- force synchronous elaboration, so the clock covers the proof and not just the
    -- signature (see the module docstring)
    let decl ← `(command| set_option Elab.async false in $decl)
    let t0 ← IO.monoMsNow
    elabCommand decl
    let t1 ← IO.monoMsNow
    -- report against the declaration's name when we can find one, so the log lines are
    -- identifiable rather than anonymous timings
    let name? := decl.raw.find? fun s => s.isOfKind ``Lean.Parser.Command.declId
    let label := match name? with
      | some n => n[0].getId.toString
      | none => "<anonymous>"
    logInfo m!"wu_bench {label}: {t1 - t0} ms"
  | _ => throwUnsupportedSyntax
