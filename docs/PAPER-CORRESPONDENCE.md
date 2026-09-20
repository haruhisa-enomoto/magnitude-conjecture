# Frozen graded-interval manuscript–Lean correspondence

The target is the September 20 manuscript frozen from research commit
`4404dea52deec5a0dc20dddf1ac8204b620ecb6a`, TeX blob
`3f2273a3faf11d226ec2a131a902ff05664f9ebf`, SHA-256
`8941be673f965879cae99484353ce50f6a05a6b8f3649229570976eedab5e5b8`.
Later exposition edits do not move this target. The frozen source and its
manifest are preserved in `frozen-graded-proof/` in the research thread.
The Lean proof and obsolete-route cleanup are recorded at research commit
`62b5468c3`. Evidence status is `proved/agent`, with Lean checking; this does
not claim owner verification.

Lean remains `v4.33.1`, with Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` as the only external Lake dependency.
Right modules are modules over the opposite algebra. Magnitude is the inverse
rational Hom-matrix sum on a complete finite indecomposable family. Multiplicities
are retained. The public theorem includes Morita reduction, so it needs no
basicness hypothesis on the input algebra and no characteristic restriction.

## Proof correspondence

Module names below are relative to `MagnitudeConjecture`. Each row identifies
checked source, rather than an assumed mathematical input.

| Frozen passage | Principal Lean modules | Content |
| --- | --- | --- |
| §§1–2, `lem:count`, `prop:ar-duality` | `CategoryTheory.Magnitude`, `Algebra.RightModuleMagnitudeSurplus`, `Algebra.RightModuleCoherentDuality` | Hom-matrix inverse, magnitude/surplus identity and AR foundations |
| §3, `lem:evaluation`, `lem:surviving-arrows`, `prop:quotient-sequences` | `Algebra.RightModulePrimitiveDirectedDeletion`, `Algebra.RightModulePrimitiveRelativeMesh`, `Algebra.RightModulePrimitiveCrossingMesh` | Primitive quotient, inherited approximation sequences and surviving irreducibles |
| §3.3, `lem:finite-kernel`, `prop:boundary-one`, `cor:boundary-arrows` | `CategoryTheory.FiniteKernelBound`, `Algebra.RightModuleFiniteKernelBound`, `Algebra.RightModulePrimitiveFiniteKernelBoundary`, `Algebra.RightModulePrimitiveFiniteKernelDualBoundary`, `Algebra.RightModulePrimitiveFiniteKernelFactorBoundary` | Finitely many kernels and multiplicity-one boundary estimates on both sides |
| §4.1, `prop:height`, `lem:height-count`, formula (4.2) | `Algebra.RightModuleDirectFactorHeight`, `Algebra.RightModuleDirectHeightExcess`, `Algebra.RightModuleDirectRadicalConcentration` | Direct height, arrow and translation increments, exact excess count; Hom = rad^ell and rad^(ell+1) = 0 for distinct labels with nonzero Hom |
| §4.2, `con:poset`, `prop:poset-equivalence` | `Algebra.RightModuleGeneratedRelationsQuotient`, `Algebra.RightModuleGeneratedRelationsRealization`, `Algebra.RightModuleGeneratedRelationsFactorLift`, `Algebra.RightModuleGeneratedCoordinateEquality` | Explicit generated-relations realization, Ext vanishing, lifting and compatibility of the indexed images |
| §4.3, `prop:intrinsic` | `Algebra.RightModuleDirectPosetExcess`, `Algebra.RightModuleDirectUpperSetSquare`, `Algebra.RightModuleDirectPosetThinness` | Nonnegative intrinsic excess; commutative-square obstruction and two-filtration equality argument |
| §5, `lem:relative-ar`, `prop:compensation`, `thm:directed-deletion`, `cor:directed` | `Algebra.RightModulePrimitiveRelativeMesh`, `Algebra.RightModulePrimitiveDirectedDeletion`, `Algebra.RightModuleDirectedSurplus`, `CategoryTheory.FiniteCategoryDirectedSurplus` | Relative sequences, Ext compensation, directed deletion and zero-surplus thinness |
| §6.1, `thm:standard`, `set:grading`, `prop:graded-classification` | `Algebra.RightModuleStandardFormUniversalCovering`, `Algebra.RightModuleStandardGradedRepresentatives`, `Algebra.RightModuleStandardGradedClassification`, `Algebra.RightModuleStandardGradedIrreducible` | Retained standard-form theorem, graded representatives, unique shifts and homogeneous Hom/irreducible spaces |
| §6.2, `con:interval`, `prop:interval-modules` | `Algebra.RightModuleStandardIntervalAlgebra`, `Algebra.RightModuleStandardIntervalSkeleton`, `Algebra.RightModuleStandardIntervalSkeletonDirected`, `Algebra.RightModuleStandardIntervalSimpleCount` | Actual finite interval algebras, complete finite indecomposable families, directedness and simple counts |
| §6.2, `prop:interval-count`, `thm:lower-bound` | `Algebra.RightModuleStandardIntervalArrowError`, `Algebra.RightModuleStandardIntervalSurplusError`, `Algebra.RightModuleIntervalInequality` | Exact interior arrow counts, uniform boundary error and the unconditional ambient inequality |
| §6.3, `prop:interval-equality` | `CategoryTheory.GradedPrincipalSeparatedDeletion`, `CategoryTheory.GradedPrincipalPackedSurplus`, `Algebra.RightModuleStandardIntervalPacking`, `Algebra.RightModuleStandardIntervalThin`, `Algebra.RightModuleStandardIntervalBiserial` | Literal gap deletion, orthogonal blocks, packing, zero interval surplus, thinness and two-sided interval biseriality |
| §6.4, `prop:ar-transfer` | `Algebra.RightModuleStandardGradedIncomingAlmostSplit`, `Algebra.RightModuleStandardIntervalIncoming`, `Algebra.RightModuleStandardIntervalIncomingDecomposition`, `Algebra.RightModuleStandardIntervalBetaTransfer` | Degree-one incoming maps, supported middle decomposition, second-shift nonprojectivity and beta transfer |
| §6.4, `prop:equality-forward`, `prop:equality-converse`, `thm:main` | `Algebra.RightModuleIntervalEquality`, `Algebra.RightModuleSocleReductionString`, `Algebra.RightModuleIntervalProof`, `Algebra.RightModuleMagnitudePublic`, `Algebra.StatementTheorem` | Equality implication, retained proved string/socle converse, Morita reduction and unchanged independent public statement |

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
kernel replay and standalone delivery are recorded separately in the final
verification checkpoint; a successful build alone does not imply registry
acceptance.
