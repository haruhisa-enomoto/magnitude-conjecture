import MagnitudeConjecture.Algebra.RightModuleInjectiveSocle
import MagnitudeConjecture.Algebra.RightModuleNakayamaARIdentification
import MagnitudeConjecture.Algebra.RightModuleNakayamaKernelIndecomposable
import MagnitudeConjecture.Algebra.RightModuleSimpleSocleAlmostSplit
import MagnitudeConjecture.Algebra.StringArrowCokernelIrreducible
import MagnitudeConjecture.CategoryTheory.AlmostSplitDuality
import MagnitudeConjecture.CategoryTheory.FiniteTauAlmostSplitMultiplicity
import MagnitudeConjecture.CategoryTheory.FiniteTauOneMiddle

/-!
# Almost-split sequences ending in string-arrow cokernels

For a displayed arrow `a : x ⟶ y`, the Auslander--Reiten translate of
`V(a)` is the kernel of `νP(x) ⟶ νP(y)`.  The source projective `P(x)`
is indecomposable, hence its Nakayama image is an indecomposable injective
with simple socle.  The nonzero Nakayama kernel therefore also has simple
socle.  This is the homological input for proving that the almost-split
middle term of `V(a)` is indecomposable.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [IsAlgClosed k]
  [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable local instance arrowAlmostSplitAlgebraFiniteDimensional
    (P : StringPresentation k A Q) :
    FiniteDimensional k P.quotientCategoryAlgebra := by
  let hP := finiteRepresentablesOfAdmissible P.toPresentation.admissible
  exact
    CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP

noncomputable local instance arrowAlmostSplitAlgebraOppositeIsNoetherian
    (P : StringPresentation k A Q) :
    IsNoetherianRing P.quotientCategoryAlgebraᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

noncomputable local instance arrowAlmostSplitEnoughProjectives
    (P : StringPresentation k A Q) :
    EnoughProjectives
      (FGModuleCat.{u} P.quotientCategoryAlgebraᵐᵒᵖ) :=
  MagnitudeConjecture.fgModuleCat_enoughProjectives
    P.quotientCategoryAlgebraᵐᵒᵖ

/-- The Nakayama kernel associated to `P(x) ⟶ P(y) ⟶ V(a)` has
simple socle. -/
theorem arrowCokernelNakayamaKernel_moduleSocle_isSimple
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    IsSimpleModule P.quotientCategoryAlgebraᵐᵒᵖ
      (moduleSocle P.quotientCategoryAlgebraᵐᵒᵖ
        ((P.arrowCokernelTwoStepMinimalProjectivePresentation a).nakayamaKernel
          (k := k))) := by
  let R := P.quotientCategoryAlgebraᵐᵒᵖ
  let T := P.arrowCokernelTwoStepMinimalProjectivePresentation a
  let K := T.nakayamaKernel (k := k)
  let I := RightModule.projectiveNakayamaFGObj (k := k)
    T.syzygyPresentation.p
  letI : EnoughProjectives (FGModuleCat.{u} R) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives R
  letI : HasExt.{u} (FGModuleCat.{u} R) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  have hKnontrivial : Nontrivial K :=
    T.nakayamaKernel_nontrivial (k := k)
      (P.arrowCokernelFGObj_not_projective a)
      (P.arrowCokernelFGObj_indecomposable a)
  letI : Nontrivial K := hKnontrivial
  have hKlength :=
    RightModule.FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := P.quotientCategoryAlgebra) K
  letI : IsArtinian R K :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hKlength).2
  letI : Projective T.syzygyPresentation.p :=
    T.syzygyPresentation.projective
  have hPind : Indecomposable T.syzygyPresentation.p := by
    exact P.representedVertexModule_indecomposable x
  have hIsocle : IsSimpleModule R (moduleSocle R I) :=
    RightModule.projectiveNakayamaFGObj_moduleSocle_isSimple
      (k := k) T.syzygyPresentation.p hPind
  let i : K ⟶ I := kernel.ι (T.nakayamaDifferential (k := k))
  have hi : Function.Injective i.hom.hom :=
    (IndecomposableSkeleton.fg_mono_iff_injective i).1 inferInstance
  exact moduleSocle_isSimple_of_injective i.hom.hom hi hIsocle

/-- The Nakayama kernel associated to a displayed arrow is indecomposable
as a module. -/
theorem arrowCokernelNakayamaKernel_isIndecomposableModule
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      P.quotientCategoryAlgebraᵐᵒᵖ
      ((P.arrowCokernelTwoStepMinimalProjectivePresentation a).nakayamaKernel
        (k := k)) := by
  let K :=
    (P.arrowCokernelTwoStepMinimalProjectivePresentation a).nakayamaKernel
      (k := k)
  have hKlength :=
    RightModule.FiniteIndecomposableSkeleton.fgModule_isFiniteLength
      (k := k) (A := P.quotientCategoryAlgebra) K
  letI : IsArtinian P.quotientCategoryAlgebraᵐᵒᵖ K :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hKlength).2
  exact isIndecomposableModule_of_simpleSocle
    (P.arrowCokernelNakayamaKernel_moduleSocle_isSimple a)

/-- The chosen complete-skeleton label of an arrow cokernel. -/
def arrowCokernelSkeletonIndex
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) {x y : Q} (a : x ⟶ y) : Fin S.n :=
  Classical.choose
    (S.fgObj_complete (P.arrowCokernelFGObj a)
      (P.arrowCokernelFGObj_indecomposable a))

/-- The literal arrow cokernel represented by its selected skeleton label. -/
def arrowCokernelSkeletonIso
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) {x y : Q} (a : x ⟶ y) :
    P.arrowCokernelFGObj a ≅
      S.fgObj (P.arrowCokernelSkeletonIndex S a) :=
  Classical.choice
    (Classical.choose_spec
      (S.fgObj_complete (P.arrowCokernelFGObj a)
        (P.arrowCokernelFGObj_indecomposable a)))

/-- The selected nonprojective skeleton label represented by a displayed
arrow cokernel. -/
def arrowCokernelNonprojectiveLabel
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) {x y : Q} (a : x ⟶ y) :
    {z : Fin S.n // ¬ Projective (S.fgObj z)} where
  val := P.arrowCokernelSkeletonIndex S a
  property := by
    intro hprojective
    apply P.arrowCokernelFGObj_not_projective a
    exact Projective.of_iso (P.arrowCokernelSkeletonIso S a).symm
      hprojective

/-- The selected Auslander--Reiten source ending at an arrow cokernel has
simple socle. -/
theorem arrowCokernelRightTranslation_moduleSocle_isSimple
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) {x y : Q} (a : x ⟶ y) :
    IsSimpleModule P.quotientCategoryAlgebraᵐᵒᵖ
      (moduleSocle P.quotientCategoryAlgebraᵐᵒᵖ
        (S.fgObj (S.rightTranslationLabel
          (P.arrowCokernelNonprojectiveLabel S a)))) := by
  let z := P.arrowCokernelNonprojectiveLabel S a
  let T := P.arrowCokernelTwoStepMinimalProjectivePresentation a
  obtain ⟨eNak⟩ :=
    S.rightTranslationIso_nakayamaKernel_of_targetIso z
      (P.arrowCokernelSkeletonIso S a) T
      (P.arrowCokernelNakayamaKernel_isIndecomposableModule a)
  exact simple_moduleSocle_congr
    (FGModuleCat.isoToLinearEquiv eNak.symm)
    (P.arrowCokernelNakayamaKernel_moduleSocle_isSimple a)

/-- Some displayed left component of the chosen Auslander--Reiten sequence
ending at an arrow cokernel is monic. -/
theorem exists_arrowCokernelRightSequenceLeftComponent_mono
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) {x y : Q} (a : x ⟶ y) :
    ∃ i : (S.minimalRightAlmostSplitAt
        (P.arrowCokernelNonprojectiveLabel S a).1).index,
      Mono ((S.rightSequenceLeftDecomposition
          (P.arrowCokernelNonprojectiveLabel S a)).component
        S.almostSplitSkeleton i) :=
  S.exists_rightSequenceLeftComponent_mono_of_simpleSocle
    (P.arrowCokernelNonprojectiveLabel S a)
    (P.arrowCokernelRightTranslation_moduleSocle_isSimple S a)

/-- The middle term of the chosen right almost-split sequence ending at an
arrow cokernel has a unique displayed indecomposable summand. -/
theorem arrowCokernelRightMiddleIndex_unique
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) {x y : Q} (a : x ⟶ y) :
    ∃ i : (S.minimalRightAlmostSplitAt
        (P.arrowCokernelNonprojectiveLabel S a).1).index,
      ∀ j, j = i := by
  let z := P.arrowCokernelNonprojectiveLabel S a
  let B := S.minimalRightAlmostSplitAt z.1
  obtain ⟨i, hi⟩ :=
    P.exists_arrowCokernelRightSequenceLeftComponent_mono S a
  refine ⟨i, fun j ↦ ?_⟩
  by_contra hji
  have hjMono : Mono (B.component S.almostSplitSkeleton j) :=
    S.rightComponent_mono_of_ne_of_leftComponent_mono z i j hji hi
  let e := P.arrowCokernelSkeletonIso S a
  let f := B.component S.almostSplitSkeleton j ≫ e.inv
  have hfIrreducible : IsIrreducibleMorphism f :=
    (B.component_irreducible S.almostSplitSkeleton j).postcomp_iso e.symm
  haveI : Nontrivial
      (S.almostSplitSkeleton.obj (B.label j)) := by
    change Nontrivial (S.fgObj (B.label j))
    exact (S.fgObj_isIndecomposableModule (B.label j)).nontrivial
  have hfMono : Mono f := by
    dsimp only [f]
    letI : Mono (B.component S.almostSplitSkeleton j) := hjMono
    infer_instance
  exact (P.not_mono_of_isIrreducibleMorphism_to_arrowCokernel
    a f hfIrreducible) hfMono

/-- The chosen right almost-split middle term ending at an arrow cokernel,
reindexed as a `Fin`-indexed indecomposable decomposition. -/
def arrowCokernelRightMiddleDecomposition
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) {x y : Q} (a : x ⟶ y) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (S.minimalRightAlmostSplitAt
        (P.arrowCokernelNonprojectiveLabel S a).1).middle := by
  classical
  let z := P.arrowCokernelNonprojectiveLabel S a
  let B := S.minimalRightAlmostSplitAt z.1
  let n := Fintype.card B.index
  let epsilon : B.index ≃ Fin n := Fintype.equivFin B.index
  let summand : Fin n →
      FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ :=
    fun i ↦ S.fgObj (B.label (epsilon.symm i))
  let eReindex :
      S.almostSplitSkeleton.sumOver B.index B.label ≅ ⨁ summand :=
    biproduct.whiskerEquiv epsilon
      (fun i ↦ eqToIso (by
        simp only [summand, Equiv.symm_apply_apply]
        change S.fgObj (B.label i) = S.fgObj (B.label i)
        rfl))
  exact {
    n := n
    summand := summand
    indecomposable := fun i ↦ S.fgObj_indecomposable _
    isoBiproduct := B.decomposition.trans eReindex }

/-- Every displayed arrow contributes a one-summand right
Auslander--Reiten middle term. -/
theorem rightMiddleArity_arrowCokernelNonprojectiveLabel
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) {x y : Q} (a : x ⟶ y) :
    FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (P.arrowCokernelNonprojectiveLabel S a).1 = 1 := by
  let z := P.arrowCokernelNonprojectiveLabel S a
  let B := S.minimalRightAlmostSplitAt z.1
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let d := P.arrowCokernelRightMiddleDecomposition S a
  have harity :=
    FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      T z.1 d B.rightAlmostSplit B.rightMinimal
  calc
    FiniteTauMatrix.rightMiddleArity T z.1 = d.n := harity
    _ = 1 := by
      change Fintype.card B.index = 1
      rw [Fintype.card_eq_one_iff]
      exact P.arrowCokernelRightMiddleIndex_unique S a

/-- The one-middle mesh selected by the Butler--Ringel arrow cokernel. -/
def displayedArrowOneMiddleMesh
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra)
    (a : DisplayedArrow Q) :
    FiniteTauMatrix.OneMiddleMesh S.finiteTauCategoryData := by
  refine ⟨(P.arrowCokernelNonprojectiveLabel S a.2.2).1, ?_,
    P.rightMiddleArity_arrowCokernelNonprojectiveLabel S a.2.2⟩
  intro hprojective
  apply (P.arrowCokernelNonprojectiveLabel S a.2.2).2
  exact (FiniteTauMatrix.isProjective_iff_projective_obj
    S.finiteTauCategoryData.toFiniteRightTauCategoryData _).mp hprojective

/-- Distinct displayed arrows select distinct one-middle meshes.  This is the
injective half of the Butler--Ringel correspondence, expressed on the chosen
finite indecomposable skeleton. -/
theorem displayedArrowOneMiddleMesh_injective
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    Function.Injective (P.displayedArrowOneMiddleMesh S) := by
  intro a b hab
  have hlabel :
      (P.arrowCokernelNonprojectiveLabel S a.2.2).1 =
        (P.arrowCokernelNonprojectiveLabel S b.2.2).1 :=
    congrArg
      (fun z : FiniteTauMatrix.OneMiddleMesh S.finiteTauCategoryData ↦ z.1)
      hab
  let e : P.displayedArrowCokernelFGObj a ≅
      P.displayedArrowCokernelFGObj b :=
    (P.arrowCokernelSkeletonIso S a.2.2).trans
      ((eqToIso (congrArg S.fgObj hlabel)).trans
        (P.arrowCokernelSkeletonIso S b.2.2).symm)
  exact P.displayedArrow_eq_of_arrowCokernel_iso a b e

/-- The displayed-arrow family gives a lower bound for the number of
one-middle meshes. -/
theorem natCard_displayedArrow_le_oneMiddleMeshCount
    (P : StringPresentation k A Q)
    (S : RightModule.FiniteIndecomposableSkeleton
      k P.quotientCategoryAlgebra) :
    Nat.card (DisplayedArrow Q) ≤
      FiniteTauMatrix.oneMiddleMeshCount S.finiteTauCategoryData := by
  rw [FiniteTauMatrix.oneMiddleMeshCount]
  exact Nat.card_le_card_of_injective
    (P.displayedArrowOneMiddleMesh S)
    (P.displayedArrowOneMiddleMesh_injective S)

end StringPresentation

end MagnitudeConjecture.BoundQuiver
