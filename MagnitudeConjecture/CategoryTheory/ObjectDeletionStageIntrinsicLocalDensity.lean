import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownIntrinsicLocalDensity
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStages
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStagePushdown

/-!
# Intrinsic local density under deletion-stage push-down

The literal three-step control window at a deletion stage computes the
downstairs occurrence density as the intrinsic local density of every
indecomposable endpoint in the fixed upstairs two-step core.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v w

variable {k : Type v} [Field k] [IsAlgClosed k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]

/-- At a literal deletion stage, the finite push-down occurrence density of
each endpoint in the fixed two-step core is its intrinsic local density in
the current stage category. -/
theorem stage_finiteOrbitPushdown_intrinsicLocalDensity
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G)) :
    let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
    letI := stageMulAction (k := k) (N : Subgroup G) R.representative x i.castSucc
    letI := stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    let hrepStage := isLocallyRepresentationFinite_deletion (k := k) C S hrep
    let W := deletionSurvivingModuleFamily (k := k) C
      (finiteThreeStepControlFamily hrep (R.representative i • x)) S
    let Core := deletionTwoStepModuleCore (k := k) C hrep
      (R.representative i • x) S
    ∀ (Y : CoveringSeparation.WindowCategory W.additiveClosure)
      (hYind : Indecomposable Y.1) (_hYCore : Y.1 ∈ Core),
      letI := Dstage.hasShift
      letI := Dstage.additiveShift
      letI := Dstage.linearShift (k := k)
      letI := isLinearModule_stableUnderShift (k := k) Dstage.core
      letI := linearModuleCategoryHasShift (k := k) Dstage.core
      letI := linearModuleCategoryAdditiveShift (R := k) Dstage.core
      letI := linearModuleCategoryLinearShift (R := k) Dstage.core
      letI := trivialHasShift
        (LinearModuleCategory.{u, v, v, v}
          (C := ShiftOrbitCategory
            (StageCategory (k := k) (N : Subgroup G)
              R.representative x i.castSucc)
            (Additive (N : Subgroup G))) k)
        (Additive (N : Subgroup G))
      ∀ {Ind : Type w} [Fintype Ind]
        (T : QuotientSubmoduleEquidistribution.Iyama.FiniteRightTauCategoryData
          (FiniteDimensionalModuleCategory.{u, v, v, v}
            (C := DeckOrbitSkeleton
              (StageCategory (k := k) (N : Subgroup G)
                R.representative x i.castSucc)
              (N : Subgroup G)) k) Ind)
        [DecidablePred T.IsProjective]
        (y : Ind)
        (_eY :
          ((Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow
            (k := k) W.additiveClosure).obj Y) ≅ T.obj y),
        CoveringAction.occurrenceLocalDensity
            (MagnitudeConjecture.FiniteTauMatrix.rightArrowTarget T)
            T.IsProjective y =
          finiteModuleLocalDensity hrepStage Y.1 hYind := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G) R.representative x i.castSucc
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  let hrepStage := isLocallyRepresentationFinite_deletion (k := k) C S hrep
  let W := deletionSurvivingModuleFamily (k := k) C
    (finiteThreeStepControlFamily hrep (R.representative i • x)) S
  let Core := deletionTwoStepModuleCore (k := k) C hrep
    (R.representative i • x) S
  have hCoreWindow : CoveringSeparation.interactionNeighborhood
      (fun M Q ↦ Indecomposable Q ∧
        CoveringSeparation.homInteraction M Q) Core ⊆
      W.additiveClosure :=
    deletionTwoStepModuleCore_interactionNeighborhood_subset
      (k := k) C hrep (R.representative i • x) S
  have hcomparison :=
    stage_finiteOrbitPushdown_threeStepControl (k := k) C D hC
      hP hI hlocal hrep N R.representative x
        (R.representative i • x) i.castSucc havoid
  exact Dstage.finiteOrbitPushdown_arbitraryControlWindow_localDensity
    hrepStage Core W hCoreWindow hcomparison

end MagnitudeConjecture.ObjectDeletion
