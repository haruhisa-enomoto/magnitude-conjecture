import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownArbitraryControlWindow
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteOrbit
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStructure
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageControlWindow

/-!
# Finite push-down at an object-deletion stage

The ambient locally bounded data, the surviving three-step control family,
and one residual avoidance certificate supply every hypothesis of the
arbitrary-control push-down theorem for each literal deletion stage.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]

/-- At every accumulated subgroup-orbit deletion stage, the descended
surviving three-step family controls irreducibility, almost-split maps,
projectivity, and incoming local density under finite push-down. -/
theorem stage_finiteOrbitPushdown_threeStepControl
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
    {m : ℕ} (N : FiniteIndexNormalSubgroup G)
    (representative : Fin m → G) (x y : C) (j : Fin (m + 1))
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep y),
      g ∉ (N : Subgroup G)) :
    letI := stageMulAction (k := k) (N : Subgroup G) representative x j
    letI := stageIsCancelSMul (k := k)
      (N : Subgroup G) representative x j
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) representative x j
    Dstage.ArbitraryControlWindowComparison
      (deletionTwoStepModuleCore (k := k) C hrep y
        (stageDeletedSet (N : Subgroup G) representative x j))
      (deletionSurvivingModuleFamily (k := k) C
        (finiteThreeStepControlFamily hrep y)
        (stageDeletedSet (N : Subgroup G) representative x j)) := by
  let S := stageDeletedSet (N : Subgroup G) representative x j
  letI := stageMulAction (k := k) (N : Subgroup G) representative x j
  haveI : IsCancelSMul (N : Subgroup G) C := inferInstance
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G) representative x j) :=
    stageIsCancelSMul (k := k) (N : Subgroup G) representative x j
  letI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G) C) :=
    CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  letI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G)
        (StageCategory (k := k) (N : Subgroup G) representative x j)) :=
    finite_deletionOrbitQuotient (k := k) C S
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) representative x j)
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) representative x j
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC (N : Subgroup G) representative x j a
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC (N : Subgroup G) representative x j a
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hIstage := fun X ↦
    deletion_dualLinearYoneda_isFiniteDimensional (k := k) C hI S X
  let hlocalStage := fun X ↦
    deletion_end_isLocalRing (k := k) C hC hlocal S X
  let hrepStage := isLocallyRepresentationFinite_deletion
    (k := k) C S hrep
  let W := deletionSurvivingModuleFamily (k := k) C
    (finiteThreeStepControlFamily hrep y) S
  let Core := deletionTwoStepModuleCore (k := k) C hrep y S
  have hCoreWindow : CoveringSeparation.interactionNeighborhood
      (fun M N ↦ Indecomposable N ∧
        CoveringSeparation.homInteraction M N) Core ⊆
      W.additiveClosure :=
    deletionTwoStepModuleCore_interactionNeighborhood_subset
      (k := k) C hrep y S
  have horthogonal : Dstage.FiniteModuleWindowShiftHomOrthogonal
      (k := k) W.additiveClosure :=
    stage_survivingModuleFamily_shiftHomOrthogonal_of_ambient_avoids
      (k := k) C D hC (N : Subgroup G) representative x j
        (finiteThreeStepControlFamily hrep y) havoid
  exact Dstage.finiteOrbitPushdown_arbitraryControlWindow
    hPstage hIstage hlocalStage hrepStage Core W
      hCoreWindow horthogonal

end MagnitudeConjecture.ObjectDeletion
