# Manuscript–Lean correspondence

The target is the main theorem of *Magnitude of module categories and special
biserial algebras*, frozen on September 29, 2026 from research commit
`e091a2d056470e49366a64650e1504d3d151df85`, manuscript commit
`ea7d79800044d5a007679ced5bf7115b62140631`. Its TeX blob is
`7fa94a158b16b701cd1b315793ca6d56d85a9a3e` and SHA-256 is
`1e76449d38b7884215ff02d7b41c39227b670b469902013b5b97aadb3f27ae36`.
The research snapshot is `frozen-exposition-2026-09-29/`; the standalone copy
is `docs/manuscript/`. Both contain the exact TeX, 33-page PDF and manifest.
This supersedes the September 21 target. Later live edits do not move it.

The manuscript has six main sections and Appendix A. The formalization covers
its main theorem and the special cases needed to prove it, using Appendix A's
direct structural arguments. It does not claim every generalized theorem in
the manuscript. No Lean source, public theorem, dependency or toolchain changed
in this synchronization. Evidence remains `proved/agent`, with Lean checking;
owner verification is not claimed.

Lean is `v4.33.1`, with Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` as the only external Lake dependency.
Right modules are modules over the opposite algebra. Magnitude is the inverse
rational Hom-matrix sum on a complete finite indecomposable family. Arrow and
middle-term multiplicities are retained. The public theorem includes Morita
reduction and needs no basicness or characteristic restriction on the input.
The manuscript's `sigma(A)` is Lean's ambient AR surplus. The quotient's
`chi(D) - 1` is its intrinsic excess; `|A|` counts simple isomorphism classes,
whereas `|M|` in the manuscript counts indecomposable summands with multiplicity.

## Main theorem dependencies

Module names are relative to `MagnitudeConjecture`. Section numbers and labels
refer to this snapshot. A row marked as a special case does not assert the
full generality of the corresponding manuscript statement.

| Frozen passage | Principal Lean modules | Coverage needed for the main theorem |
| --- | --- | --- |
| §2, `lem:count`, `prop:ar-duality`, `prop:ar-multiplicity` | `CategoryTheory.Magnitude`, `Algebra.RightModuleMagnitudeSurplus`, `Algebra.RightModuleCoherentDuality`, `Algebra.RightModulePrimitiveArrowGain` | Hom-matrix inverse, magnitude/surplus formula, AR duality and multiplicities for module categories |
| §§3.1–3.3 and §§4.2–4.3, `lem:surviving-arrows`, `prop:quotient-sequences`, `lem:relative-ar`, `lem:quotient-closure`, `lem:evaluation`, `lem:quotient-identities` | `Algebra.RightModulePrimitiveQuotient`, `Algebra.RightModulePrimitiveQuotientFiniteSkeleton`, `Algebra.RightModulePrimitiveTorsion`, `Algebra.RightModuleHoshinoTorsion`, `Algebra.RightModulePrimitiveRelativeMesh`, `Algebra.RightModulePrimitiveMultiplicity`, `Algebra.RightModulePrimitiveCrossingMesh` | Primitive quotient family, surviving irreducibles, torsion factorizations and restricted almost-split sequences in the required setting |
| §4.4 and Appendix A.1, `lem:finite-kernel`, `prop:boundary-one`, `cor:boundary-arrows` | `CategoryTheory.FiniteKernelBound`, `Algebra.RightModuleFiniteKernelBound`, `Algebra.RightModulePrimitiveFiniteKernelBoundary`, `Algebra.RightModulePrimitiveFiniteKernelDualBoundary`, `Algebra.RightModulePrimitiveFiniteKernelFactorBoundary` | Direct finite-kernel proof and multiplicity-one boundary estimates on both sides |
| §4.5 and Appendix A.2, `prop:height`, `lem:height-count` | `Algebra.RightModuleDirectFactorHeight`, `Algebra.RightModuleDirectHeightExcess`, `Algebra.RightModuleDirectRadicalConcentration` | Direct heights, exact excess count and radical concentration |
| §4.6 and Appendix A.3, `con:poset`, `prop:poset-equivalence` | `Algebra.RightModuleGeneratedRelationsQuotient`, `Algebra.RightModuleGeneratedRelationsRealization`, `Algebra.RightModuleGeneratedRelationsFactorLift`, `Algebra.RightModuleGeneratedCoordinateEquality` | Explicit generated-relations realization for the directed primitive quotient |
| §4.6 and Appendix A.4, `prop:intrinsic`, `lem:two-chains` | `Algebra.RightModuleDirectPosetExcess`, `Algebra.RightModuleDirectUpperSetSquare`, `Algebra.RightModuleDirectPosetThinness` | Nonnegative intrinsic excess, commutative-square obstruction and two-filtration equality thinness |
| §§3.4–3.5 and §4.7, `thm:serre-magnitude`, `prop:compensation`, `cor:directed-compensation`, `thm:directed-deletion`, `eq:directed-deletion` | `Algebra.RightModulePrimitiveDirectCount`, `Algebra.RightModulePrimitiveBoundaryCorrespondence`, `Algebra.RightModulePrimitiveArrowGain`, `Algebra.RightModulePrimitiveContragredientMultiplicity`, `Algebra.RightModulePrimitiveDirectedDeletion` | Directed primitive specialization: crossing correction is zero, new sequences have distinct gaining pairs, exact deletion identity and equality thinness |
| §4.8, `cor:directed`, `prop:thin-biserial`, `thm:biserial-special` | `Algebra.RightModuleDirectedSurplus`, `CategoryTheory.FiniteCategoryDirectedSurplus`, `Algebra.RightModuleStandardIntervalThin`, `Algebra.RightModuleStandardIntervalBiserial` | Directed lower bound, zero-surplus thinness, and the resulting two-sided biseriality needed for the interval algebras |
| §§5.2–5.3, `thm:standard`, `con:hom-grading`, `lem:standard-grading`, `set:grading`, `prop:graded-classification` | `Algebra.RightModuleStandardFormUniversalCovering`, `Algebra.RightModuleStandardGradedRepresentatives`, `Algebra.RightModuleStandardGradedClassification`, `Algebra.RightModuleStandardGradedHom`, `Algebra.RightModuleStandardGradedDirected`, `Algebra.RightModuleStandardGradedIrreducible` | Standard-form construction, concrete graded lifts, unique shifts, directedness and homogeneous Hom/irreducible spaces |
| §5.1, `con:interval`, `prop:interval-modules`, `prop:interval-count` | `Algebra.RightModuleStandardIntervalAlgebra`, `Algebra.RightModuleStandardIntervalSkeleton`, `Algebra.RightModuleStandardIntervalSkeletonDirected`, `Algebra.RightModuleStandardIntervalSimpleCount`, `Algebra.RightModuleStandardIntervalArrowError`, `Algebra.RightModuleStandardIntervalSurplusError` | Actual standard-form interval algebras, complete indecomposable families, counts and uniform surplus error |
| §5.3, `thm:lower-bound` | `Algebra.RightModuleIntervalInequality` | Nonnegative interval surplus implies the unconditional ambient inequality |
| §6.1, `lem:separated-intervals`, `prop:interval-equality` | `CategoryTheory.GradedPrincipalSeparatedDeletion`, `CategoryTheory.GradedPrincipalPackedSurplus`, `Algebra.RightModuleStandardIntervalPacking`, `Algebra.RightModuleStandardIntervalThin`, `Algebra.RightModuleStandardIntervalBiserial` | Surplus specialization: separated quotient, quantitative packing bound, zero interval surplus, thinness and biseriality |
| §6.2, `prop:ar-transfer` | `Algebra.RightModuleStandardGradedIncomingAlmostSplit`, `Algebra.RightModuleStandardIntervalIncoming`, `Algebra.RightModuleStandardIntervalIncomingDecomposition`, `Algebra.RightModuleStandardIntervalBetaTransfer` | Standard-form beta transfer to one control interval, sufficient for the equality implication |
| §§6.2–6.3, `thm:biserial-ar`, `prop:equality-forward`, `prop:equality-converse`, `thm:main` | `Algebra.RightModuleIntervalEquality`, `Algebra.RightModuleSocleReductionString`, `Algebra.RightModuleIntervalProof`, `Algebra.RightModuleMagnitudePublic`, `Algebra.StatementTheorem` | Proved beta characterization, socle/string converse, Morita reduction and the full independent public theorem |

## Why the specialized results suffice

**Appendix A replaces the arbitrary-poset detour.** The direct boundary,
height, realization and two-filtration arguments prove the intrinsic estimate
and its equality consequence for the directed primitive quotient. The main
theorem does not require §4.1's `thm:poset-magnitude` for every
representation-finite poset over an arbitrary field. Ringel–Vossieck is cited
in the main text; its relevant directed structural inputs have direct checked
proofs in the package.

**Directed deletion uses the zero-correction crossing identity.**
`ambientARSurplus_sub_primitiveQuotientARSurplus_eq_cost` in
`Algebra.RightModulePrimitiveDirectedDeletion` states the exact difference
identity. Its cost is intrinsic excess plus arrow gain minus new mesh count.
The boundary and crossing modules prove the unique non-killed middle
occurrence needed to make the manuscript's general correction `delta` zero.
Thus the general Serre identity is not an additional assumed input.

**Compensation already constructs distinct pairs.** In
`Algebra.RightModulePrimitiveArrowGain`, `newMeshGainingPair` and
`newMeshGainingPair_injective` assign distinct gaining pairs to new sequences;
`card_primitiveNewRightMeshEndpoint_le_primitiveTotalArrowGain` gives the
numerical bound. Directedness and the proved primitive boundary data are
available at the call site. This covers `cor:directed-compensation` and the
needed instance of `prop:compensation`, without claiming the latter under
its more general disjoint-extension-support hypothesis alone.

**Concrete standard-form lifts suffice.** The standard-form classification
constructs graded representatives directly and proves uniqueness up to shift.
The general Gordon–Green gradability and graded almost-split results cited in
§§5–6 are not extra axioms or missing hypotheses of the public theorem.
The implementation proves the required standard-form instances, rather than
the manuscript's statements for arbitrary nonnegatively graded algebras.

**The quantitative packing conclusion is already proved.**
`standardFormInterval_surplus_le_length_mul` in
`Algebra.RightModuleStandardIntervalPacking` bounds the interval surplus by
`(r + h + 1)` times the ambient surplus, where `h` is the implementation's
control height, a bound on the grading. Together with
`standardFormInterval_surplus_nonnegative` in
`Algebra.RightModuleIntervalInequality`, this gives the required two-sided
bound. `standardFormInterval_surplus_eq_zero_of_ambient_eq_zero` gives the
zero-surplus consequence. The abstract real-valued invariant formulation with
an `o(m)` error in `lem:separated-intervals` is outside scope; the proved
surplus specialization uses a uniform error bound.

**One control interval is enough for beta transfer.** The endpoint
`RightModule.FiniteIndecomposableSkeleton.beta_le_standardFormInterval_beta`
compares the original algebra's beta with that of the standard-form interval
`[0,h+2]`. The original and standard-form counts are identified through arrow
occurrence labels. Supporting code constructs homogeneous incoming maps,
proves right almost-splitness and right minimality after restriction, and
identifies the source with the direct sum of incoming occurrences.
The second shift supplies nonsplit epimorphisms witnessing nonprojectivity
of the relevant middle summands, with multiplicities retained.
At zero ambient surplus every interval is biserial, so this particular
interval supplies the beta bound required in `prop:equality-forward`.
No eventual transfer theorem for all sufficiently long intervals of an
arbitrary graded algebra, or separately named graded kernel, is claimed.

## Scope, attribution and retained foundations

The public endpoint is `Statement.mainClaim`, reached through
`Algebra.RightModuleIntervalProof`. It proves the full conjecture, including
nonsingularity, over any algebraically closed field and for nonbasic inputs.
All load-bearing mathematical inputs are proved in the package or Mathlib;
none is introduced as a project-local axiom. In particular, the beta
characterization and special-biserial socle reduction are proved, even though
the manuscript cites external sources for them.

Current source attributions include Assem–Simson–Skowroński IV.2.13 for AR
duality, Iyama for tau-categories and ideal quotients, Hoshino for relative
sequences, Ringel–Vossieck for the directed structural results, Gordon–Green
for general graded statements, Auslander–Reiten and Skowroński–Waschbüsch
for the beta characterization, and Børve–Horiatakis–Kalck for the converse.
These citations describe the manuscript; they do not enlarge formal coverage.
The general strict tau-category magnitude result, arbitrary Serre crossing
formula, disjoint-support compensation, arbitrary-poset theorem, arbitrary
grading results and abstract invariant packing lemma are not claimed in their
full manuscript generality. Illustrative examples have no separate certificates.

The standard-form theorem retains its checked covering foundations. The
subsequent inequality and equality proofs use finite graded intervals.
The public import closure contains 1,089 local modules and no F1 or averaging
module. The 199 old-route-exclusive modules were removed after checking
retained callers; Git preserves them. Shared and supplementary foundations
remain. Historical manuscript locators in supporting-module comments are not
current section references; this correspondence supplies current navigation.

## Verification

The unchanged complete library, public endpoint, Challenge/Solution, dependency
and vendored audits passed in the September 20–21 verification. The source
census covers 1,183 development files. Public and expanded axiom checks cover
7 and 4,090 declarations respectively, using only standard axioms or none.
The Mathlib-only Challenge remains 298 lines with its deliberate comparison
placeholder excluded from the production proof.

Independent Comparator statement/axiom checking, NanoDa and Lean-kernel
replay passed for standalone source
`9380dc294e2586430ff853b613918d5d9fc44375`. The run took 38.1 minutes; its
record is `verification/2026-09-20/comparator.json`. These local results do
not claim a fresh hosted Palomar-profile run or registry acceptance.

The September 29 synchronization checks all 1,193 source-manifest files in
both repositories against their verified hashes, unchanged source sets and
pins, the new snapshot hashes, current manuscript labels and cited Lean
modules/declarations, metadata and website. Its separate record is
`verification/2026-09-29/exposition-migration.json`. The existing proof
verification is retained by exact source identity, without rerunning or
redating the expensive build and replay.
