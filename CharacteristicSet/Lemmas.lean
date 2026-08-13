import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Auxiliary `MvPolynomial` lemmas

Every lemma that used to live in this file has since been upstreamed to Mathlib, into
`Mathlib.Algebra.MvPolynomial.Degrees` and `Mathlib.Algebra.MvPolynomial.Variables`.
Keeping them here as well now produces "has already been declared" errors, so the
declarations have been removed.

This module is retained as a re-export: `Mathlib.Algebra.MvPolynomial.Variables` itself
imports `Mathlib.Algebra.MvPolynomial.Degrees`, so downstream files that
`import CharacteristicSet.Lemmas` continue to see exactly the same lemmas as before.
-/
