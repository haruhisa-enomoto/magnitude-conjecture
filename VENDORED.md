# Vendored Lean source

The campaign vendors a minimal categorical foundation from
`haruhisa-enomoto/quotient-submodule-equidistribution` rather than adding that
repository as a Lake dependency.

## Source

- Local donor: `/home/italing/work/quotient-submodule-equidistribution`
- Git remote: `https://github.com/haruhisa-enomoto/quotient-submodule-equidistribution.git`
- Branch: `main`
- Commit: `d5ba0c48e7a851afd51247ff9cd81fc629e00ed2`
- License: Apache License 2.0
- Donor Lean: `v4.32.0`
- Donor Mathlib: `28313485bc624fcd16dcb162dd2e2c3c813aa8fe`

The donor repository's `PROVENANCE.md` records that eleven of its foundational
modules were themselves adapted from TauCeti commit
`eeb5b4e20c16d302fab0930c4b589c1e0bdd7241`; exact attribution in copied source
headers and the donor license must be preserved.

## Policy

- Copy only a dependency cone with a concrete magnitude-proof purpose.
- Preserve the donor module paths and namespaces until a compiled
  magnitude-specific interface justifies refactoring.
- Record every copied file below before its first campaign commit.
- Treat OP-specific theorem layers as proof donors to be adapted, not as a
  reason to vendor the entire equidistribution package.

## Current integrity and recorded local deltas

The checksum manifest records the current integrated contents of all 74
vendored paths.  Relative to the corresponding files in the donor checkout at
commit `20ee4b964a9174b15304ac96485beeb73be113d8`, 69 remain byte-identical.
The other five have the following exact, project-local deltas:

- `CategoryTheory/MinimalMorphism.lean` adds the `LocalRing` import and the
  generic lemma `isRightMinimal_of_localEnd_of_ne_zero`, used by the factor
  and string-algebra layers.  Donor SHA-256:
  `fd81f1295cb282aa5e1c1714457c0e84afcc02782ede77c250cb856fd83ed865`.
- `CategoryTheory/IyamaSpecialMorphism.lean` adds only the local Lean 4.33
  definitional-equality compatibility option.  Donor SHA-256:
  `c3f8be6ba2555d4b36c5e230eb3f26bfaa484542d1e41fb61255b8837900ffd6`.
- `CategoryTheory/IyamaKrullSchmidtDirectFinite.lean` adds the same option and
  has one layout-only closing-brace change.  Donor SHA-256:
  `41d011901e95972e965cb04b196215f0297d7be6b320d2ca872ccf0dbfae9f73`.
- `RepresentationTheory/EndomorphismRadical.lean` replaces one proof step by
  an equivalent `simpa` compatible with the pinned Mathlib API; no declaration
  statement changes.  Donor SHA-256:
  `df1d050a3ed34c9f490c9fe56bcc22a7f614b3386302425827e0afde661fd636`.
- `RepresentationTheory/IrreducibleCofinite.lean` differs only by a terminal
  blank line.  Donor SHA-256:
  `66bd00036423190fc9c167cbab8b4fc756b50857c68bf35e556e3b042a1cc026`.

Thus the historical “byte-identical” descriptions below record the state at
initial import; the exhaustive list above records every present-day exception.
Run `sha256sum -c vendor/quotient-submodule-equidistribution.sha256` from the
package root to verify the integrated source exactly.

## Initial generic categorical cone

The initial cone contains the following byte-identical donor files:

- `CategoryTheory/HomIdeal.lean`
- `CategoryTheory/CategoricalRadical.lean`
- `CategoryTheory/CategoricalRadicalIdeal.lean`
- `CategoryTheory/MinimalMorphism.lean`
- `CategoryTheory/IdealQuotient.lean`
- `CategoryTheory/Rejective.lean`
- `CategoryTheory/RejectiveOpposite.lean`
- `CategoryTheory/HomIdealPowers.lean`
- `CategoryTheory/NilpotentCategoricalRadical.lean`
- `CategoryTheory/IyamaTauSequence.lean`
- `CategoryTheory/IyamaTauBiproduct.lean`
- `CategoryTheory/FiniteTauCategory.lean`

The copied source has 3,039 lines.  `cmp` verified every file and the Apache
license against the donor checkout.  Individual SHA-256 digests are stored in
`vendor/quotient-submodule-equidistribution.sha256`.

## Residue-dimension extension

The Hom--mesh inverse discharge adds two further byte-identical generic files:

- `CategoryTheory/SplitMorphismComplement.lean`
- `CategoryTheory/IyamaLadderRadical.lean`

They construct complements to split morphisms in an idempotent-complete
preadditive category and identify radical morphisms out of, or into, a chosen
indecomposable with failure of split monicity or split epicity.  This extension
adds 356 lines, for 3,395 vendored lines in total.  It does not import an
OP-specific theorem layer.

## Positive-weight strictness extension

The discharge of right-mesh monicity adds the exact transitive dependency
closure of `CategoryTheory/IyamaNakayamaExtraction.lean` and
`CategoryTheory/IyamaKrullSchmidtWeight.lean`:

- `CategoryTheory/IyamaFiniteLadderComparison.lean`
- `CategoryTheory/IyamaKrullSchmidtConormalForm.lean`
- `CategoryTheory/IyamaKrullSchmidtDirectFinite.lean`
- `CategoryTheory/IyamaKrullSchmidtNormalForm.lean`
- `CategoryTheory/IyamaKrullSchmidtWeight.lean`
- `CategoryTheory/IyamaLadderComparisonAssembly.lean`
- `CategoryTheory/IyamaLadderComparisonCertificate.lean`
- `CategoryTheory/IyamaLadderComparisonEndpoint.lean`
- `CategoryTheory/IyamaLeftLadderBasic.lean`
- `CategoryTheory/IyamaLeftLadderIteration.lean`
- `CategoryTheory/IyamaLeftLadderNormalization.lean`
- `CategoryTheory/IyamaLeftLadderPropagation.lean`
- `CategoryTheory/IyamaLeftLadderRadicalLayer.lean`
- `CategoryTheory/IyamaLeftSuccessorSpecialness.lean`
- `CategoryTheory/IyamaMeshSplitLifting.lean`
- `CategoryTheory/IyamaMixedMeshSplitLifting.lean`
- `CategoryTheory/IyamaNakayamaBoundary.lean`
- `CategoryTheory/IyamaNakayamaExtraction.lean`
- `CategoryTheory/IyamaNakayamaPair.lean`
- `CategoryTheory/IyamaNakayamaWeight.lean`
- `CategoryTheory/IyamaReversedDomination.lean`
- `CategoryTheory/IyamaReversedRightPrefix.lean`
- `CategoryTheory/IyamaRightLadderConstruction.lean`
- `CategoryTheory/IyamaRightLadderIteration.lean`
- `CategoryTheory/IyamaRightLadderPropagation.lean`
- `CategoryTheory/IyamaRightLadderRadicalWitness.lean`
- `CategoryTheory/IyamaRightSuccessorSpecialness.lean`
- `CategoryTheory/IyamaSpecialMorphism.lean`

These 28 byte-identical files contain the generic finite-ladder and Nakayama
pair argument needed to prove that a positive right-additive weight forces the
first map of every right mesh to be monic.  They add 9,732 lines, for 42 files
and 13,127 vendored lines in total.  This closure contains no representation-
directed, word-combinatorial, equidistribution, or OP-conjecture theorem layer.
Every file was byte-compared with the donor checkout; its digest is recorded in
`vendor/quotient-submodule-equidistribution.sha256`.

## Finite-type almost-split extension

The literal module-category construction adds the exact transitive dependency
closure of `RepresentationTheory/FiniteTypeAlmostSplit.lean`,
`RepresentationTheory/AlmostSplitKernel.lean`, and
`RepresentationTheory/AlmostSplitUniqueness.lean`.  Besides the already
vendored `CategoryTheory/MinimalMorphism.lean`, the closure adds:

- `ConvexGeometry/Basic.lean`
- `Foundation/RingTheory/LocalRing/Basic.lean`
- `Foundation/RingTheory/KrullSchmidt/Indecomposable.lean`
- `RepresentationTheory/AdditiveSubcategory.lean`
- `RepresentationTheory/AlmostSplitCofinite.lean`
- `RepresentationTheory/AlmostSplitKernel.lean`
- `RepresentationTheory/AlmostSplitUniqueness.lean`
- `RepresentationTheory/AntiExchange.lean`
- `RepresentationTheory/EndomorphismRadical.lean`
- `RepresentationTheory/FacSub.lean`
- `RepresentationTheory/FiniteType.lean`
- `RepresentationTheory/FiniteTypeAlmostSplit.lean`
- `RepresentationTheory/IrreducibleCofinite.lean`
- `RepresentationTheory/SplitInjective.lean`
- `RepresentationTheory/SplitProjective.lean`
- `RepresentationTheory/SubmoduleAntiExchange.lean`
- `RepresentationTheory/Trace.lean`

These 17 byte-identical files add 6,150 lines.  The complete vendored source
now contains 59 files and 19,277 lines.  This extension proves finite-type
existence and uniqueness of minimal almost-split morphisms and the kernel
properties of a minimal right almost-split morphism.  It imports no donor
tau-translation, module mesh, covering, representation-directed, or
equidistribution endpoint layer.  Every added file was checked against the
pinned donor commit with both `cmp` and SHA-256.

The right-tau construction additionally vendors
`RepresentationTheory/IrreducibleRadicalQuotient.lean`.  Its characterization
of radical morphisms out of or into a chosen indecomposable is used to turn
the almost-split factorization properties into Iyama tau-approximation
properties.  This byte-identical 457-line addition has no further project
dependencies beyond the preceding cone.  The complete vendored source now
contains 60 files and 19,734 lines.

## Contragredient-duality extension

The two-sided tau construction additionally vendors the exact dependency cone
of `RepresentationTheory/ContragredientDuality.lean`:

- `ConvexGeometry/ClosedSets.lean`
- `ConvexGeometry/Finite.lean`
- `ConvexGeometry/LevelPolynomial.lean`
- `ConvexGeometry/Relabeling.lean`
- `RepresentationTheory/Biduality.lean`
- `RepresentationTheory/Contragredient.lean`
- `RepresentationTheory/ContragredientDuality.lean`
- `RepresentationTheory/ContragredientFunctor.lean`
- `RepresentationTheory/ContravariantTransport.lean`
- `RepresentationTheory/DualityConsequences.lean`

These 10 byte-identical files provide the finite-dimensional
contragredient duality used to transfer enough projectives to enough
injectives for finitely generated modules.  They add 1,929 lines, for 70 files
and 21,663 vendored lines in total.  This extension contains no donor
tau-category, covering, representation-directed, equidistribution, or
OP-conjecture endpoint layer.  Every added file was checked against the pinned
donor commit with both `cmp` and SHA-256.

## Literal factor-category utilities

The literal quotient construction additionally vendors two byte-identical,
Mathlib-only generic utilities:

- `CategoryTheory/LinearGeneratedHomIdeal.lean`
- `CategoryTheory/IdempotentLifting.lean`

The first equips an additive Hom-ideal quotient with its induced linear
structure.  The second transports idempotent completeness across a full
additive functor whose relevant endomorphism kernels are elementwise
nilpotent.  They add 357 lines, for 72 files and 22,020 vendored lines in
total.  The module-category quotient, its surviving Krull--Schmidt skeleton,
nilpotent radical, and kernel-nilpotence verification are implemented in the
magnitude namespace rather than copied from the donor's factor-category
stack.  Both utilities were checked against the pinned donor commit with
`cmp` and SHA-256.

## Finite additive-hull weak exactness

The mesh-presentation checkpoint additionally vendors two byte-identical,
generic matrix-category utilities from the clean donor checkout at commit
`20ee4b964a9174b15304ac96485beeb73be113d8`:

- `CategoryTheory/LinearMat.lean`
- `CategoryTheory/MatWeakExactness.lean`

The first supplies the pointwise linear structure on the finite matrix
category.  The second promotes exactness tested against singleton rows or
columns to a weak kernel or weak cokernel in the finite additive hull.  They
add 138 lines, for 74 byte-identical files and 22,158 vendored lines in total.
No tau-category, directed-representation, covering, equidistribution, or
OP-conjecture theorem layer is copied.  Both files were checked against that
donor commit with `cmp` and SHA-256.

## Cartan path-grading adaptation

The standard-mesh grading checkpoint adapts six project-local modules from
the sibling Cartan-determinant formalization at commit
`a1427785c2180f9d9ab7b6e202276a8f2647ead3`:

- `Graded/QuotientDecomposition.lean`
- `CategoryTheory/LinearPathCategory.lean`
- `CategoryTheory/PathLengthGrading.lean`
- `CategoryTheory/HomogeneousPathIdeal.lean`
- `CategoryTheory/HomogeneousRelationQuotient.lean`
- `CategoryTheory/MeshCategory.lean`

They are not byte-identical vendored files: their namespaces and imports are
adapted to this package, the generated-ideal API is identified with the
already-vendored equidistribution utility, and the magnitude development adds
the small transport and identity lemmas required by its skeleton interface.
No Cartan classification, scalar-presentation, or theorem endpoint is copied.

## Occurrence-basis adaptation

The concrete standardness construction adapts the generic core of three
modules from the clean `quotient-submodule-equidistribution` checkout at
commit `20ee4b964a9174b15304ac96485beeb73be113d8`:

- `RepresentationTheory/LinearIrreducibleHomSpace.lean`
- `RepresentationDirected/RightAROccurrenceBasis.lean`
- `RepresentationDirected/LeftAROccurrenceBasis.lean`

The adapted files live together under `RepresentationTheory/`.  They retain
only the linear `rad/rad²` quotient and the right/left occurrence-coordinate
equivalences through the scalar-endomorphism theorem.  The unavailable
`NoParallelExtOne` dependency is replaced by the exact Mathlib import which
supplies the linear module-category structure, and all later donor-specific
directed ranking, multiplicity-one, and OP-conjecture machinery is omitted.
This is a bounded source adaptation, not a byte-identical vendoring claim.

## Uniserial-module adaptation

The multiplicity-one rigidity checkpoint adapts the small generic
module-lattice layer from the clean
`quotient-submodule-equidistribution` checkout at commit
`20ee4b964a9174b15304ac96485beeb73be113d8`:

- `RepresentationTheory/LengthThreeUniserial.lean`
- `RepresentationTheory/LengthThreeUniserialSubmodule.lean`
- `RepresentationTheory/FamilyFourControl.lean`
- `RepresentationTheory/NoLoopNakayamaReduction.lean`
- `RepresentationTheory/ExtDegreeNakayamaReduction.lean`
- `RepresentationTheory/SimpleLevels.lean`
- `RepresentationTheory/BottomTwoModules.lean`

The adapted magnitude-owned module defines uniseriality as totality of the
submodule lattice and retains only closure under quotients, submodules,
embeddings, and linear equivalences; the finite-length uniqueness and
indecomposability consequences; and the simple-top/radical recursion.  It
imports the already-vendored indecomposable-module foundation, but none of the
donor's length-three classification, Gabriel-quiver, Nakayama, or
equidistribution theorem layers.  This is a bounded source adaptation, not a
byte-identical vendoring claim.
