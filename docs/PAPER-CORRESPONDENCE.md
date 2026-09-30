# Manuscript–Lean correspondence

The formalization proves the main theorem of Haruhisa Enomoto's *Magnitude
of module categories and special biserial algebras*, using the direct proofs
in Appendix A and the required directed and standard-form special cases.

This correspondence refers to the September 30, 2026 manuscript: six sections
and Appendix A, 33 pages, source commit
`e327fbcf1b75a3f6986f4f29d5afe5089e384297` and TeX blob
`a4c2b5b788a0f607285e6d14edbd2e4830c7021a`.
The exact TeX, PDF and hash manifest are in `docs/manuscript/` in the standalone
repository and `frozen-exposition-2026-09-30/` in the research thread.

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
| §§3.1–3.3 and §§4.2–4.3, `lem:surviving-arrows`, `prop:quotient-sequences`, `lem:relative-ar`, `lem:quotient-closure`, `lem:evaluation` | `Algebra.RightModulePrimitiveQuotient`, `Algebra.RightModulePrimitiveQuotientFiniteSkeleton`, `Algebra.RightModulePrimitiveTorsion`, `Algebra.RightModuleHoshinoTorsion`, `Algebra.RightModulePrimitiveRelativeMesh`, `Algebra.RightModulePrimitiveMultiplicity`, `Algebra.RightModulePrimitiveCrossingMesh` | Primitive quotient family, surviving irreducibles, torsion factorizations and restricted almost-split sequences in the required setting |
| §4.4 and Appendix A.1–A.2, `lem:finite-kernel`, `prop:boundary-one`, `cor:boundary-arrows` | `CategoryTheory.FiniteKernelBound`, `Algebra.RightModuleFiniteKernelBound`, `Algebra.RightModulePrimitiveFiniteKernelBoundary`, `Algebra.RightModulePrimitiveFiniteKernelDualBoundary`, `Algebra.RightModulePrimitiveFiniteKernelFactorBoundary` | Direct finite-kernel proof and multiplicity-one boundary estimates on both sides |
| Appendix A.2 and A.4, `lem:quotient-identities`, `prop:height`, `lem:height-count` | `Algebra.RightModuleDirectFactorHeight`, `Algebra.RightModuleDirectHeightExcess`, `Algebra.RightModuleDirectRadicalConcentration` | Direct heights, exact excess count and radical concentration |
| §4.5 and Appendix A.3, `con:poset`, `prop:poset-equivalence` | `Algebra.RightModuleGeneratedRelationsQuotient`, `Algebra.RightModuleGeneratedRelationsRealization`, `Algebra.RightModuleGeneratedRelationsFactorLift`, `Algebra.RightModuleGeneratedCoordinateEquality` | Explicit generated-relations realization for the directed primitive quotient |
| §4.5 and Appendix A.4, `prop:intrinsic`, `lem:two-chains` | `Algebra.RightModuleDirectPosetExcess`, `Algebra.RightModuleDirectUpperSetSquare`, `Algebra.RightModuleDirectPosetThinness` | Nonnegative intrinsic excess, commutative-square obstruction and two-filtration equality thinness |
| §§3.4–3.5 and §4.6, `thm:serre-magnitude`, `prop:compensation`, `cor:directed-compensation`, `thm:directed-deletion`, `eq:directed-deletion` | `Algebra.RightModulePrimitiveDirectCount`, `Algebra.RightModulePrimitiveBoundaryCorrespondence`, `Algebra.RightModulePrimitiveArrowGain`, `Algebra.RightModulePrimitiveContragredientMultiplicity`, `Algebra.RightModulePrimitiveDirectedDeletion` | Directed primitive specialization: crossing correction is zero, new sequences have distinct gaining pairs, exact deletion identity and equality thinness |
| §4.7, `cor:directed`, `prop:thin-biserial`, `thm:biserial-special` | `Algebra.RightModuleDirectedSurplus`, `CategoryTheory.FiniteCategoryDirectedSurplus`, `Algebra.RightModuleStandardIntervalThin`, `Algebra.RightModuleStandardIntervalBiserial` | Directed lower bound, zero-surplus thinness, and the resulting two-sided biseriality needed for the interval algebras |
| §§5.2–5.3, `thm:standard`, `con:hom-grading`, `lem:standard-grading`, `set:grading`, `prop:graded-classification` | `Algebra.RightModuleStandardFormUniversalCovering`, `Algebra.RightModuleStandardGradedRepresentatives`, `Algebra.RightModuleStandardGradedClassification`, `Algebra.RightModuleStandardGradedHom`, `Algebra.RightModuleStandardGradedDirected`, `Algebra.RightModuleStandardGradedIrreducible` | Standard-form construction, concrete graded lifts, unique shifts, directedness and homogeneous Hom/irreducible spaces |
| §5.1, `con:interval`, `prop:interval-modules`, `prop:interval-count` | `Algebra.RightModuleStandardIntervalAlgebra`, `Algebra.RightModuleStandardIntervalSkeleton`, `Algebra.RightModuleStandardIntervalSkeletonDirected`, `Algebra.RightModuleStandardIntervalSimpleCount`, `Algebra.RightModuleStandardIntervalArrowError`, `Algebra.RightModuleStandardIntervalSurplusError` | Actual standard-form interval algebras, complete indecomposable families, counts and uniform surplus error |
| §5.3, `thm:lower-bound` | `Algebra.RightModuleIntervalInequality` | Nonnegative interval surplus implies the unconditional ambient inequality |
| §6.1, `lem:separated-intervals`, `prop:interval-equality` | `CategoryTheory.GradedPrincipalSeparatedDeletion`, `CategoryTheory.GradedPrincipalPackedSurplus`, `Algebra.RightModuleStandardIntervalPacking`, `Algebra.RightModuleStandardIntervalThin`, `Algebra.RightModuleStandardIntervalBiserial` | Surplus specialization: separated quotient, quantitative packing bound, zero interval surplus, thinness and biseriality |
| §6.2, `prop:ar-transfer` | `Algebra.RightModuleStandardGradedIncomingAlmostSplit`, `Algebra.RightModuleStandardIntervalIncoming`, `Algebra.RightModuleStandardIntervalIncomingDecomposition`, `Algebra.RightModuleStandardIntervalBetaTransfer` | Standard-form beta transfer to one control interval, sufficient for the equality implication |
| §§6.2–6.3, `thm:biserial-ar`, `prop:equality-forward`, `prop:equality-converse`, `thm:main` | `Algebra.RightModuleIntervalEquality`, `Algebra.RightModuleSocleReductionString`, `Algebra.RightModuleIntervalProof`, `Algebra.RightModuleMagnitudePublic`, `Algebra.StatementTheorem` | Proved beta characterization, socle/string converse, Morita reduction and the full independent public theorem |

## Why the specialized results suffice

**Direct quotient arguments in Appendix A.** The direct boundary,
height, realization and two-filtration arguments prove the intrinsic estimate
and its equality consequence for the directed primitive quotient. The main
theorem does not require §4.1's `thm:poset-magnitude` for every
representation-finite poset. Ringel–Vossieck is cited
in the main text; its relevant directed structural inputs have direct checked
proofs in the package.

**Directed deletion uses the zero-correction crossing identity.**
`ambientARSurplus_sub_primitiveQuotientARSurplus_eq_cost` in
`Algebra.RightModulePrimitiveDirectedDeletion` states the exact difference
identity. Its cost is intrinsic excess plus arrow gain minus new mesh count.
The boundary and crossing modules prove the unique non-killed middle
occurrence needed to make the manuscript's general correction `delta` zero.
This proves the directed primitive instance of the Serre identity.

**Distinct pairs in directed compensation.** In
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

**Interval equality from quantitative packing.**
`standardFormInterval_surplus_le_length_mul` in
`Algebra.RightModuleStandardIntervalPacking` bounds the interval surplus by
`(r + h + 1)` times the ambient surplus, where `h` is the implementation's
control height, a bound on the grading. Together with
`standardFormInterval_surplus_nonnegative` in
`Algebra.RightModuleIntervalInequality`, this gives the required two-sided
bound. `standardFormInterval_surplus_eq_zero_of_ambient_eq_zero` gives the
zero-surplus consequence used in the current `prop:interval-equality`, whose
statement asserts zero surplus and biseriality of every interval.
The abstract real-valued invariant formulation with
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

## Coverage and mathematical sources

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

The standard-form theorem has checked covering-theoretic foundations. The
inequality and equality proofs then use finite graded intervals. The public
import closure contains 1,089 local modules; the full library also includes
supplementary results. Use this correspondence for current manuscript
locations; section references in older supporting-module comments may differ.

## Verification

The complete library, public theorem, Challenge/Solution and dependency audits
passed in September 20–21 verification. The source census covers 1,183
development files. Public and expanded axiom checks cover 7 and 4,090
declarations, using only `propext`, `Classical.choice`, `Quot.sound`, or none.
The Mathlib-only Challenge is 298 lines; its comparison placeholder is excluded
from the production proof.

Comparator statement and axiom checks, NanoDa and Lean-kernel replay passed
for standalone source `9380dc294e2586430ff853b613918d5d9fc44375`.
The exact result is `verification/2026-09-20/comparator.json`.
The September 30 documentation checks, including manuscript hashes and
identity of all 1,193 source-manifest files in both repositories, are recorded
separately in `verification/2026-09-30/exposition-migration.json`.
The Lean sources and pins match the replayed proof. These records distinguish
kernel verification from manuscript correspondence and human review.
