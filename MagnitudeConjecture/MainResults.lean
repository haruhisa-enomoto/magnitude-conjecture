import MagnitudeConjecture.Algebra.StatementTheorem

/-!
# Public theorem entry point

Import this module to use the magnitude theorem and its definitions.

* `Statement.mainClaim` proves the independent Mathlib-only statement,
  including nonsingularity and the full equality case.
* `RightModule.magnitudeConjecture_simpleCount` states the full theorem with
  a direct simple-module count.
* `RightModule.simpleModuleCount_eq_numberOfSimpleModules` connects that
  count to the original projective-count interface.
* `RightModule.FiniteIndecomposableSkeleton.projectiveLabelEquivSimpleLabel`
  is the simple-top bijection over any field.
* `RightModule.FiniteIndecomposableSkeleton.magnitudeConjecture_simpleCount`
  permits an arbitrary complete finite indecomposable family.

`MagnitudeConjecture` imports the broader development, and
`MagnitudeConjecture.AxiomAudit` checks its supporting results. For the
headline theorem and the count interface, use `MagnitudeConjecture.PublicAxiomAudit`.
-/
