# Manuscript–Lean correspondence

The current target is the revised manuscript frozen on September 21 from
research commit `8c01dab074320c81a87b7094351cc3a41b3be53a`, manuscript commit
`781560011ef76c07943d7f4887cae5e5cf603a74`. Its TeX blob is
`fe59cb133871162b2a9777e697b3d47fd6aa1466` and SHA-256 is
`8255d1f669586781393b5b235238e0e260e0a85f90a7bdb24b6786b2131c2eec`.
The research snapshot is `frozen-exposition-2026-09-21/`; the standalone copy
is `docs/manuscript/`. Both contain the exact TeX, 29-page PDF and hash manifest.
This target supersedes the September 20 snapshot. Later live exposition edits
do not move it automatically.

The revised text has five main sections and Appendix A. Its graded-interval
proof is covered by the existing Lean implementation at research commit
`62b5468c3`; no Lean source, theorem statement, dependency or toolchain changed
in this exposition migration. Evidence status remains `proved/agent`, with
Lean checking; this does not claim owner verification.

Lean remains `v4.33.1`, with Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` as the only external Lake dependency.
Right modules are modules over the opposite algebra. Magnitude is the inverse
rational Hom-matrix sum on a complete finite indecomposable family. Multiplicities
are retained. The public theorem includes Morita reduction, so it needs no
basicness hypothesis on the input algebra and no characteristic restriction.

## Proof correspondence

Module names below are relative to `MagnitudeConjecture`. Each row identifies
checked source, rather than an assumed mathematical input.

| Current frozen passage | Principal Lean modules | Content |
| --- | --- | --- |
| §§1–2, `lem:count`, `prop:ar-duality` | `CategoryTheory.Magnitude`, `Algebra.RightModuleMagnitudeSurplus`, `Algebra.RightModuleCoherentDuality` | Hom-matrix inverse, magnitude/surplus identity and AR foundations |
| §§3.1–3.2, `lem:evaluation`, `lem:surviving-arrows`, `prop:quotient-sequences`, `lem:quotient-identities` | `Algebra.RightModulePrimitiveDirectedDeletion`, `Algebra.RightModulePrimitiveRelativeMesh`, `Algebra.RightModulePrimitiveCrossingMesh` | Primitive quotient, inherited approximation sequences and surviving irreducibles |
| §3.3 and Appendix A.1, `lem:finite-kernel`, `prop:boundary-one`, `cor:boundary-arrows` | `CategoryTheory.FiniteKernelBound`, `Algebra.RightModuleFiniteKernelBound`, `Algebra.RightModulePrimitiveFiniteKernelBoundary`, `Algebra.RightModulePrimitiveFiniteKernelDualBoundary`, `Algebra.RightModulePrimitiveFiniteKernelFactorBoundary` | Finitely many kernels and multiplicity-one boundary estimates on both sides |
| §3.4 and Appendix A.2, `prop:height`, `lem:height-count` | `Algebra.RightModuleDirectFactorHeight`, `Algebra.RightModuleDirectHeightExcess`, `Algebra.RightModuleDirectRadicalConcentration` | Direct height, arrow and translation increments, exact excess count; Hom = rad^ell and rad^(ell+1) = 0 for distinct labels with nonzero Hom |
| §3.5 and Appendix A.3, `con:poset`, `prop:poset-equivalence` | `Algebra.RightModuleGeneratedRelationsQuotient`, `Algebra.RightModuleGeneratedRelationsRealization`, `Algebra.RightModuleGeneratedRelationsFactorLift`, `Algebra.RightModuleGeneratedCoordinateEquality` | Explicit generated-relations realization, Ext vanishing, lifting and compatibility of the indexed images |
| §3.6 and Appendix A.4, `prop:intrinsic` | `Algebra.RightModuleDirectPosetExcess`, `Algebra.RightModuleDirectUpperSetSquare`, `Algebra.RightModuleDirectPosetThinness` | Nonnegative intrinsic excess; commutative-square obstruction and two-filtration equality argument |
| §4, `lem:relative-ar`, `lem:new-sequence-terms`, `prop:compensation`, `thm:directed-deletion`, `cor:directed` | `Algebra.RightModulePrimitiveRelativeMesh`, `Algebra.RightModulePrimitiveDirectedDeletion`, `Algebra.RightModuleDirectedSurplus`, `CategoryTheory.FiniteCategoryDirectedSurplus` | Relative sequences, Ext compensation, directed deletion and zero-surplus thinness |
| §5.1, `thm:standard`, `con:hom-grading`, `lem:standard-grading`, `set:grading`, `prop:graded-classification` | `Algebra.RightModuleStandardFormUniversalCovering`, `Algebra.RightModuleStandardGradedRepresentatives`, `Algebra.RightModuleStandardGradedClassification`, `Algebra.RightModuleStandardGradedIrreducible` | Retained standard-form theorem, graded representatives, unique shifts and homogeneous Hom/irreducible spaces |
| §5.2, `con:interval`, `prop:interval-modules` | `Algebra.RightModuleStandardIntervalAlgebra`, `Algebra.RightModuleStandardIntervalSkeleton`, `Algebra.RightModuleStandardIntervalSkeletonDirected`, `Algebra.RightModuleStandardIntervalSimpleCount` | Actual finite interval algebras, complete finite indecomposable families, directedness and simple counts |
| §5.2, `prop:interval-count`, `thm:lower-bound` | `Algebra.RightModuleStandardIntervalArrowError`, `Algebra.RightModuleStandardIntervalSurplusError`, `Algebra.RightModuleIntervalInequality` | Exact interior arrow counts, uniform boundary error and the unconditional ambient inequality |
| §5.3, `prop:interval-equality` | `CategoryTheory.GradedPrincipalSeparatedDeletion`, `CategoryTheory.GradedPrincipalPackedSurplus`, `Algebra.RightModuleStandardIntervalPacking`, `Algebra.RightModuleStandardIntervalThin`, `Algebra.RightModuleStandardIntervalBiserial` | Literal gap deletion, orthogonal blocks, packing, zero interval surplus, thinness and two-sided interval biseriality |
| §5.4, `prop:ar-transfer` | `Algebra.RightModuleStandardGradedIncomingAlmostSplit`, `Algebra.RightModuleStandardIntervalIncoming`, `Algebra.RightModuleStandardIntervalIncomingDecomposition`, `Algebra.RightModuleStandardIntervalBetaTransfer` | Degree-one incoming maps, supported middle decomposition, second-shift nonprojectivity and beta transfer |
| §5.4, `prop:equality-forward`, `prop:equality-converse`, `thm:main` | `Algebra.RightModuleIntervalEquality`, `Algebra.RightModuleSocleReductionString`, `Algebra.RightModuleIntervalProof`, `Algebra.RightModuleMagnitudePublic`, `Algebra.StatementTheorem` | Equality implication, retained proved string/socle converse, Morita reduction and unchanged independent public statement |

## Newly separated statements and source attribution

The revised statements organize arguments already present in the proof.
The correspondences below identify their existing mathematical implementation;
Lean need not package every numbered assertion as one declaration.

| Current passage | Existing implementation |
| --- | --- |
| §2, `prop:ar-multiplicity` | `finrank_irreducibleHomSpace_eq_arrowMultiplicity_of_scalarEndomorphisms` in `Algebra.RightModulePrimitiveArrowGain`, with its left/right occurrence-basis imports. Multiplicities are dimensions over the algebraically closed base field. |
| §3, `lem:quotient-closure` | `Algebra.RightModulePrimitiveQuotient`, `Algebra.RightModulePrimitiveQuotientSkeleton`, `Algebra.RightModulePrimitiveQuotientFiniteSkeleton` and the closure arguments in `Algebra.RightModulePrimitiveCrossingMesh` implement annihilation by the primitive ideal, the literal quotient family and preservation of directedness. |
| §3.2, `lem:quotient-identities` | `Algebra.RightModulePrimitiveMultiplicity` supplies `meshUnitEquations`; `Algebra.RightModulePrimitiveDirectCount` supplies surviving middle decompositions and the mesh/vertex partitions. `CategoryTheory.FiniteTauTranslationMultiplicity` proves `arrowMultiplicity_eq_translation`. |
| §4.1, `lem:relative-ar` | `Algebra.RightModulePrimitiveTorsion` constructs the torsion functor, canonical `primitiveTorsionLift`, its factorization identity and `hom_to_primitiveTorsionQuotient_eq_zero`. `Algebra.RightModuleHoshinoTorsion` proves minimality; `Algebra.RightModulePrimitiveRelativeMesh` gives short exactness and both almost-split maps. Opposite-module duality supplies the other side. Universal factorizations are used directly, rather than a separately named pair of adjunctions. |
| §4.1, `lem:new-sequence-terms` | `Algebra.RightModulePrimitiveCrossingMesh` proves the unique non-killed middle occurrence; `Algebra.RightModulePrimitiveBoundaryCorrespondence` identifies the opposite endpoint and its unit multiplicity. `Algebra.RightModulePrimitiveArrowGain` identifies relative arrow multiplicities; `Algebra.RightModulePrimitiveContragredientMultiplicity` proves their dual compatibility. |
| §4, `thm:directed-deletion`, `eq:directed-deletion` | `ambientARSurplus_sub_primitiveQuotientARSurplus_eq_cost` in `Algebra.RightModulePrimitiveDirectedDeletion` already states the exact difference identity; its cost is the intrinsic excess plus arrow gain minus new mesh count. |
| §5.1, `con:hom-grading`, `lem:standard-grading`, `prop:graded-classification` | The standard-form graded functor and representatives supply the concrete grading. `standardFormGradedHomEquiv` in `Algebra.RightModuleStandardGradedHom` uses source shift minus target shift. `Algebra.RightModuleStandardGradedClassification`, `Algebra.RightModuleStandardGradedDirected` and `Algebra.RightModuleStandardGradedIrreducible` prove uniqueness, directedness and irreducible dimensions. |
| §5.3, successive deletion in `prop:interval-equality` | `CategoryTheory.GradedPrincipalSeparatedDeletion` and `Algebra.RightModuleStandardIntervalPacking` construct the actual separated quotient and apply directed deletion through the intermediate quotients. |
| §5.4, `thm:main` | `Algebra.RightModuleMagnitudePublic` and `Algebra.StatementTheorem` already include Morita reduction and the theorem for nonbasic input algebras. |

The manuscript now cites Ringel–Vossieck for the structural statements in §3
and retains their direct proofs in Appendix A. Lean retains the checked direct
finite-kernel, height, generated-relations and two-filtration arguments; no
literature assertion is introduced as an axiom. The citation revisions identify
Assem–Simson–Skowroński IV.2.13 for AR duality, the original Iyama sources for
tau-category structure and notation, and Skowroński–Waschbüsch for finite
biserial implies special biserial, with Pogorzały–Skowroński as a restatement.
Gabriel's left/right observation is explicitly credited. These changes do not
alter the corresponding Lean theorems or their assumptions.

Section numbers in this table refer exclusively to the current snapshot.
Historical manuscript locators in retained supporting-module comments are not
current section references; use this correspondence for navigation.

## Exact almost-split formulation

For `prop:ar-transfer`, the checked endpoint is
`RightModule.FiniteIndecomposableSkeleton.beta_le_standardFormInterval_beta`.
The supporting code constructs the actual homogeneous incoming map, proves
right almost-splitness and right minimality after restriction, identifies its
source with the direct sum indexed by incoming arrow occurrences, and proves
that each originally nonprojective summand stays nonprojective in the control
interval. The supported maps at shifts zero and one are nonsplit epimorphisms;
the second shift is the required witness for middle summands. The resulting
beta inequality counts occurrences, including repeated isomorphic summands.

This is the final-map formulation of the displayed almost-split sequence
`eq:graded-ar`. Lean does not separately name the manuscript's graded kernel
`N_X` or assert its displayed support interval as a standalone theorem. Neither
is an extra hypothesis of the beta transfer: the checked argument uses the
last map, its actual source decomposition and the nonsplit epimorphisms.
No injectivity transfer or complete identification of the interval AR quiver
is used. The shift convention puts the incoming source one degree above its
target, and both shifts fit in `[0,h+2]`.

## Retained foundations and removed route

The standard-form input retains its checked covering-theoretic foundations,
as the manuscript's imported theorem does. The subsequent inequality and
equality proofs use finite graded intervals. The public import closure has
1,089 local modules and no F1 or averaging module. The 199 old-route-exclusive
modules were deleted after checking all retained callers. Shared foundations
and supplementary checked results remain; Git preserves the removed source.
The root also includes full radical concentration and supplementary results
that need not occur in the final theorem's import closure.

This correspondence covers the main proof and its supporting constructions.
The manuscript's illustrative examples are not asserted to have separate Lean
certificates. Imported mathematical results used by the production theorem
are proved in the package or Mathlib; they are not added as local axioms.

## Verification

The complete library, public endpoint, Challenge/Solution, dependency and
vendored audits pass under the existing serial build settings. The source
census covers 1,183 development files and finds no banned production token.
The expanded audit checks 4,090 declarations, all with standard axioms only
or no axioms. The seven public checks have the same permitted boundary.
The generated Mathlib-only Challenge is unchanged at 298 lines. Independent
replay also passes: current Comparator checks the statement and axiom boundary,
and NanoDa and Lean's kernel accept the solution. The exact standalone source
is `9380dc294e2586430ff853b613918d5d9fc44375`; its verification record is
`verification/2026-09-20/comparator.json` in the standalone repository. The run
took 38.1 minutes. These local checks do not claim a fresh hosted Palomar-profile
preflight, editorial review or registry acceptance.

The September 21 exposition migration checks exact source equality against
that replayed proof and both repository copies, the new snapshot hashes,
current manuscript labels and cited Lean modules, and the refreshed metadata
and website. It does not rerun the unchanged proof or redate the original
build, axiom and replay evidence. The new migration record is
`verification/2026-09-21/exposition-migration.json` in the standalone repository.
