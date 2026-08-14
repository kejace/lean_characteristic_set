/-
Copyright (c) 2026 Wu tactic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CharSetTac.Differential
import Mathlib.Topology.Sets.Opens

/-!
# Sheaves of differential rings, and gluing local certificates

The apparatus for turning chart-local certificates into global statements.

## Why this is light

Every theorem the tactic proves is stated over an *abstract* `[CommRing R] [Differential R]`
— nothing mentions charts, coordinates or points. So a theorem proved once applies to the
sections over **every** open set simultaneously, just by instantiating `R`. There is no
per-chart re-proving to do; the only work is assembling the local conclusions.

And that assembly is the **separatedness** half of the sheaf axiom: a section vanishing on
each member of a cover vanishes. That is what `IsSeparated` below records.

## Where the actual obstruction lives

Not in the gluing. The certificate concludes `g = 0` only where its multiplier `H` is
nonzero, and `H ≠ 0` is an *open dense* condition — Wu's method is generically valid, and
"generic" is literally a statement about a dense open set. Upgrading dense-open to global
needs continuity and connectedness, which is topology, not algebra.

**The escape hatch used throughout the Riemannian examples**: when `H` is nowhere zero the
degeneracy locus is empty rather than merely thin, and the local conclusion is already
global on each open. For a metric, `det g ≠ 0` is nowhere-vanishing by definition — so
curvature identities glue with no density argument at all. `eq_zero_of_isUnit_mul`
below is that statement.
-/

open scoped Differential
open TopologicalSpace

namespace Wu

/-- A presheaf of differential rings on `X`: rings of sections, restriction maps, and a
derivation on each that commutes with restriction.

Bundled by hand rather than through `TopCat.Presheaf` because all that is needed here is
the commutation of `d` with restriction; the categorical packaging would add machinery
without adding content. -/
structure DiffPresheaf (X : Type*) [TopologicalSpace X] where
  /-- Sections over an open set. -/
  sections : Opens X → Type*
  /-- Each is a commutative ring. -/
  [commRing : ∀ U, CommRing (sections U)]
  /-- Each carries a derivation. -/
  [diff : ∀ U, Differential (sections U)]
  /-- Restriction along an inclusion, as a ring homomorphism. -/
  restrict : ∀ {U V : Opens X}, V ≤ U → sections U →+* sections V
  /-- **The differential condition**: restriction commutes with the derivation. This is the
  only thing beyond an ordinary presheaf of rings, and it is what makes a chart-local
  differential computation meaningful globally. -/
  restrict_deriv : ∀ {U V : Opens X} (h : V ≤ U) (a), restrict h (a′) = (restrict h a)′

attribute [instance] DiffPresheaf.commRing DiffPresheaf.diff

namespace DiffPresheaf

variable {X : Type*} [TopologicalSpace X] (F : DiffPresheaf X)

/-- `F` is **separated**: a section vanishing on every member of a cover vanishes.

This is the half of the sheaf axiom that gluing conclusions needs. The other half —
existence of a glued section — is not needed here: the sections are already given, only
their equality is in question. -/
def IsSeparated : Prop :=
  ∀ (U : Opens X) (ι : Type) (V : ι → Opens X) (hV : ∀ i, V i ≤ U),
    U ≤ iSup V → ∀ s : F.sections U, (∀ i, F.restrict (hV i) s = 0) → s = 0

/-- **Gluing a local certificate.** A section restricting to zero on a cover is zero. This
is the entire content of "local to global" for equational conclusions: the identities glue
for free. -/
theorem glue_zero (hsep : F.IsSeparated) {U : Opens X} {ι : Type} {V : ι → Opens X}
    (hV : ∀ i, V i ≤ U) (hcover : U ≤ iSup V) (s : F.sections U)
    (h : ∀ i, F.restrict (hV i) s = 0) : s = 0 :=
  hsep U ι V hV hcover s h

/-- **Gluing an equation.** Two sections agreeing on a cover are equal. -/
theorem glue_eq (hsep : F.IsSeparated) {U : Opens X} {ι : Type} {V : ι → Opens X}
    (hV : ∀ i, V i ≤ U) (hcover : U ≤ iSup V) (s t : F.sections U)
    (h : ∀ i, F.restrict (hV i) s = F.restrict (hV i) t) : s = t :=
  sub_eq_zero.mp <| F.glue_zero hsep hV hcover (s - t) fun i => by
    rw [map_sub, h i, sub_self]

end DiffPresheaf

/-! **The nowhere-vanishing multiplier principle** — `Wu.eq_zero_of_isUnit_mul` — now lives
in `CharSetTac/Frontend.lean`, because the tactic itself uses it: on a ring that is not a
domain, `wu` cancels its multiplier by unit-ness rather than by `NoZeroDivisors`. It is
still the statement this file needs, and is available through the import chain. -/

end Wu
