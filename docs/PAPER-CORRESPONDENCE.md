# Frozen F1 manuscript-to-Lean correspondence

This record compares the formalization with Haruhisa Enomoto's frozen
September 10 proof of *The magnitude conjecture for module categories*. The
exact manuscript identifiers are canonical commit
`6d9095121c8cafac4b97e9dfabf1f6bc9b6519e5` and source blob
`c4d50a6257aab1c0368ccbc2ba618d1e389367fe`. The synchronized Lean source comes
from canonical formalization commit `d0831ee92`.

The statement uses the same field, finiteness, and handedness hypotheses: a
finite-dimensional representation-finite algebra over an algebraically closed
field, with finitely generated right modules. There is no characteristic
restriction and no basicness hypothesis on the original algebra. Special
biseriality means an admissible special-biserial bound-quiver presentation in
the Morita class. Right modules use `Aᵐᵒᵖ`, and the public magnitude conventions
are unchanged.

## Proof coverage

| Frozen F1 passage | Lean implementation | Correspondence |
| --- | --- | --- |
| Sections 1-2: magnitude, AR conventions, imported structural inputs | `CategoryTheory.Magnitude`, `Algebra.RightModuleBasicMorita`, `DeferredStructuralInputs` | Exact existing interfaces retained |
| Sections 3-4: primitive factor, faithful reconstruction, Schur-image boundary | `Algebra.RightModulePrimitiveGrading`, `Algebra.RightModulePrimitiveDirectedDeletion`, `Algebra.RightModulePrimitiveSpecialBiserial`, `Algebra.RightModuleBasicMorita` | Proved modules wired into the F1 cone |
| Section 5: Ext boundary compensation | `CategoryTheory.FiniteDecompositionVanishes`, `CategoryTheory.IncomingHomLocalDensity` | Finite decomposition and incoming-locality interfaces |
| Section 6: direct mesh construction and positive grading | `Algebra.RightModuleStandardMeshConstruction`, `Algebra.RightModuleStandardMeshGrading`, `Algebra.RightModulePrimitiveGrading` | Direct mesh and grading interfaces |
| Section 9: finite locality and support quotient | `CategoryTheory.F1LocalDensity`, `CategoryTheory.F1FiniteDeletionSupport` | Frozen support quotient and local-change declarations |
| Section 10: finite positive deletion-order average | `Combinatorics.DeletionOrderWeight`, `Combinatorics.F1FiniteDeletionAverage`, `CategoryTheory.F1FiniteOrbitSourceRepresentatives`, `CategoryTheory.F1FiniteSupportIncidence` | The finite telescope, exact support-average identity, source-orbit representatives, shift transport, and incidence certificate |
| Section 11: general lower bound | `Algebra.RightModuleF1Inequality` | F1 lower-bound endpoint |
| Section 12: equality transfer | `Algebra.RightModuleF1Equality`, `Algebra.RightModuleF1EqualityThin`, `CategoryTheory.F1FiniteObjectDeletion`, `Algebra.RightModuleF1EqualityBiserialCover`, `Algebra.RightModuleF1EqualityBiserialAlgebra` | Finite object-support deletion and quotient-Yoneda restriction replace the former finite-convex step |
| Section 13: weighted converse and socle rejection | `Algebra.RightModuleF1EqualityCharacterization`, `Algebra.RightModuleSocleReductionString`, `Algebra.RepresentationFiniteSpecialBiserialBeta` | Equality is transferred to the exact special-biserial characterization |
| Theorem 1.1: public endpoint | `Algebra.RightModuleF1Proof`, `Algebra.RightModuleF1CoveringBridge`, re-exported by `Algebra.RightModuleMagnitudePublic` | The public bridge uses the direct finite-support incidence route |

Module names in the table are prefixed by `MagnitudeConjecture`. The public
`Statement.isSpecialBiserial_iff` proves that the independent presentation has
exactly the production meaning. The direct simple count is connected to the
projective count by `RightModule.simpleModuleCount_eq_numberOfSimpleModules`;
the underlying simple-top bijection holds over any field.

The formal decomposition is finer than the prose organization because Lean
isolates the finite arithmetic, locality, orbit transport, algebra transport,
and equality interfaces in separate modules. These are implementation
boundaries for the same frozen argument rather than additional mathematical
hypotheses. The public statement is unchanged by the migration.

## Superseded source

The earlier algebra files `RightModuleMagnitudeInequality`,
`RightModuleMagnitudeEquality*`, `RightModuleMagnitudeCharacterization*`, and
`RightModuleStandardFormCoveringAverage*` were deleted after the import and
declaration-use audit. Their public declarations now live in F1-named modules.
The stable `RightModuleMagnitudePublic` interface remains.

The former category files for finite-convex thinness and representable
extension, residual endpoints, stage endpoints, and the category-algebra
covering bridge were also removed from the production tree. Shared
decomposition lemmas live in `FiniteDecompositionVanishes`.
`F1FiniteObjectDeletion` supplies the finite survivor quotient, its finiteness
instance, and the quotient-Yoneda comparison. The standard-form covering
bridge consumes the finite source-family incidence theorem directly, without
the previous residual-finiteness or free-group assumptions at its public
inequality and rigidity endpoints.

Git retains the full history of every deleted file.

## Verification boundary

The canonical migration passed the complete library and public builds, both
axiom audits, source and dependency audits, the generated Challenge/Solution
check, exact statement comparison, permitted-axiom enforcement, NanoDa replay,
and Lean default-kernel replay. The standalone rerun and its exact artifacts
are recorded in [VERIFICATION.md](VERIFICATION.md).

This correspondence records an agent-audited formal proof. Haruhisa Enomoto
has not designated it as independently human-checked in this repository.

Any later change to definitions, hypotheses, conclusions, or proof route
requires a new correspondence checkpoint. Wording and numbering changes need
reference updates. Each release should retain its own source and manuscript
identifiers so later revisions do not change the meaning of this record.
