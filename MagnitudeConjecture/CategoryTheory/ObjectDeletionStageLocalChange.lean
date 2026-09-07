import MagnitudeConjecture.CategoryTheory.ObjectDeletionAffectedSupport
import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalChangeSum
import MagnitudeConjecture.CategoryTheory.FiniteConvexLocalChange

/-!
# Intrinsic local change at the finite deletion stages

At step `i`, the local change is the singleton deletion at the surviving
object represented by `g_i x` in the current stage.  Its finite summation
family is the surviving part of the fixed ambient two-step control family.
The preceding support theorem makes every pointwise term outside that family
zero.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable {N : Subgroup G} [N.Normal]

/-- The finite family representing the fixed ambient two-step core which
survives to the stage immediately before deletion `i`. -/
def stageTwoStepModuleFamily
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m) :
    FiniteIndecomposableModuleFamily
      (k := k)
      (C := StageCategory (k := k) N R.representative x i.castSucc) :=
  deletionSurvivingModuleFamily (k := k) C
    ((finiteFiberControlSeed hrep (R.representative i • x)).iterateHomNeighborhood
      hrep 2)
    (stageDeletedSet N R.representative x i.castSucc)

/-- The literal stagewise local change in the covering average: sum the
singleton-deletion density change over the surviving fixed two-step core,
once per represented isomorphism class. -/
noncomputable def stageLocalChange
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m) : ℤ :=
  let S := stageDeletedSet N R.representative x i.castSucc
  finiteDeletionLocalChangeSum
    (k := k) (StageCategory (k := k) N R.representative x i.castSucc)
    (isLocallyRepresentationFinite_deletion (k := k) C S hrep)
    ({stageNextObject (k := k) R x i} :
      Set (StageCategory (k := k) N R.representative x i.castSucc))
    (stageTwoStepModuleFamily (k := k) hrep R x i)

omit [IsCancelSMul G C] in
/-- Membership in the stage summation family is exactly membership in the
fixed ambient two-step endpoint core. -/
theorem mem_stageTwoStepModuleFamily_isoClosure_iff
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := StageCategory (k := k) N R.representative x i.castSucc) k) :
    M ∈ (stageTwoStepModuleFamily (k := k) hrep R x i).isoClosure ↔
      M ∈ deletionTwoStepModuleCore (k := k) C hrep
        (R.representative i • x)
        (stageDeletedSet N R.representative x i.castSucc) := by
  exact mem_deletionSurvivingModuleFamily_isoClosure_iff
    (k := k) C
      ((finiteFiberControlSeed hrep (R.representative i • x)).iterateHomNeighborhood
        hrep 2)
      (stageDeletedSet N R.representative x i.castSucc) M

/-- Every pointwise singleton-deletion change outside the literal stage
summation family is zero. -/
theorem stageLocalChangeAt_eq_zero_of_not_mem_twoStepModuleFamily
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := StageCategory (k := k) N R.representative x i.castSucc) k)
    (hM : Indecomposable M)
    (houtside : M ∉
      (stageTwoStepModuleFamily (k := k) hrep R x i).isoClosure) :
    finiteDeletionLocalChangeAt
      (k := k) (StageCategory (k := k) N R.representative x i.castSucc)
      (isLocallyRepresentationFinite_deletion
        (k := k) C
        (stageDeletedSet N R.representative x i.castSucc) hrep)
      ({stageNextObject (k := k) R x i} :
        Set (StageCategory (k := k) N R.representative x i.castSucc))
      M hM = 0 := by
  let S := stageDeletedSet N R.representative x i.castSucc
  let y := R.representative i • x
  let hy := R.representative_smul_not_mem_stageDeletedSet x i
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  have houtsideCore : M ∉
      deletionTwoStepModuleCore (k := k) C hrep y S := by
    simpa only [S, y,
      mem_stageTwoStepModuleFamily_isoClosure_iff
        (k := k) hrep R x i M] using houtside
  exact
    finiteDeletionLocalChangeAt_eq_zero_of_not_mem_deletionTwoStepModuleCore
      (k := k) C hrep y S hy hPstage M hM houtsideCore

/-- The intrinsic two-step Hom neighborhood of a deletion stage is contained
in the surviving ambient two-step family used by the covering construction. -/
theorem intrinsicTwoStep_isoClosure_subset_stageTwoStepModuleFamily
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m) :
    let S := stageDeletedSet N R.representative x i.castSucc
    let hy := R.representative_smul_not_mem_stageDeletedSet x i
    let hrepStage := isLocallyRepresentationFinite_deletion
      (k := k) C S hrep
    ((finiteFiberControlSeed hrepStage
        (survivingObj (k := k) C S hy)).iterateHomNeighborhood
      hrepStage 2).isoClosure ⊆
      (stageTwoStepModuleFamily (k := k) hrep R x i).isoClosure := by
  let S := stageDeletedSet N R.representative x i.castSucc
  let y := R.representative i • x
  let hy := R.representative_smul_not_mem_stageDeletedSet x i
  let hrepStage := isLocallyRepresentationFinite_deletion
    (k := k) C S hrep
  dsimp only
  intro M hMcore
  have hMind : Indecomposable M := by
    obtain ⟨j, ⟨e⟩⟩ := hMcore
    exact (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).1
      (((finiteFiberControlSeed hrepStage
        (survivingObj (k := k) C S hy)).iterateHomNeighborhood
          hrepStage 2).indecomposable j)
  have hExt := iterateHomNeighborhood_extensionByZero_mem
    (k := k) C hrep y S hy 2 M hMind hMcore
  exact (mem_deletionSurvivingModuleFamily_isoClosure_iff
    (k := k) C
      ((finiteFiberControlSeed hrep y).iterateHomNeighborhood hrep 2)
      S M).2 hExt

/-- The covering-stage summation family computes exactly the intrinsic local
change of the current admissible deletion stage. -/
theorem stageLocalChange_eq_finiteDeletionLocalChange
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m) :
    stageLocalChange (k := k) hrep R x i =
      finiteDeletionLocalChange
        (k := k)
        (StageCategory (k := k) N R.representative x i.castSucc)
        (isLocallyRepresentationFinite_deletion
          (k := k) C
          (stageDeletedSet N R.representative x i.castSucc) hrep)
        (stageNextObject (k := k) R x i) := by
  let S := stageDeletedSet N R.representative x i.castSucc
  let y := R.representative i • x
  let hy := R.representative_smul_not_mem_stageDeletedSet x i
  let D := StageCategory (k := k) N R.representative x i.castSucc
  let yS := stageNextObject (k := k) R x i
  let hrepStage := isLocallyRepresentationFinite_deletion
    (k := k) C S hrep
  let W := (finiteFiberControlSeed hrepStage yS).iterateHomNeighborhood
    hrepStage 2
  let U := stageTwoStepModuleFamily (k := k) hrep R x i
  have hsubset : W.isoClosure ⊆ U.isoClosure :=
    intrinsicTwoStep_isoClosure_subset_stageTwoStepModuleFamily
      (k := k) hrep R x i
  have hPstage := fun X ↦ deletion_linearCoyoneda_isFiniteDimensional
    (k := k) C hP S X
  have houtside : ∀ j : Fin U.n, U.obj j ∉ W.isoClosure →
      finiteDeletionLocalChangeAt
        (k := k) D hrepStage ({yS} : Set D)
          (U.obj j) (U.indecomposable j) = 0 := by
    intro j hj
    exact finiteDeletionLocalChangeAt_eq_zero_of_not_mem_twoStep
      (k := k) D hPstage hrepStage yS (U.obj j) (U.indecomposable j) hj
  have hsum := finiteDeletionLocalChangeSum_eq_of_isoClosure_subset
    (k := k) D hrepStage ({yS} : Set D) W U hsubset houtside
  change finiteDeletionLocalChangeSum
      (k := k) D hrepStage ({yS} : Set D) U =
    finiteDeletionLocalChangeSum
      (k := k) D hrepStage ({yS} : Set D) W
  exact hsum.symm

variable [IsAlgClosed k]

/-- Every local-change summand in the finite covering telescope is
nonnegative because its deletion stage is admissible. -/
theorem stageLocalChange_nonneg
    (H : IsAdmissible (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m) :
    0 ≤ stageLocalChange
      (k := k) H.locallyRepresentationFinite R x i := by
  let S := stageDeletedSet N R.representative x i.castSucc
  let D := StageCategory (k := k) N R.representative x i.castSucc
  let yS := stageNextObject (k := k) R x i
  let HD := isAdmissible_deletion (k := k) (C := C) S H
  rw [stageLocalChange_eq_finiteDeletionLocalChange
    (k := k) H.locallyBounded.finiteCovariantRepresentables
      H.locallyRepresentationFinite R x i]
  exact admissible_finiteDeletionLocalChange_nonneg (k := k) D HD yS

/-- Equality of one covering-stage local change has the same
one-dimensional-fibre rigidity as intrinsic admissible deletion. -/
theorem stageLocalChange_rigidity
    (H : IsAdmissible (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m)
    (hzero : stageLocalChange
      (k := k) H.locallyRepresentationFinite R x i = 0)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := StageCategory (k := k) N R.representative x i.castSucc) k)
    (hM : Indecomposable M)
    (hMy : ¬ IsZero (M.obj.obj.obj (stageNextObject (k := k) R x i))) :
    Module.finrank k
      (M.obj.obj.obj (stageNextObject (k := k) R x i)) = 1 := by
  let S := stageDeletedSet N R.representative x i.castSucc
  let D := StageCategory (k := k) N R.representative x i.castSucc
  let yS := stageNextObject (k := k) R x i
  let HD := isAdmissible_deletion (k := k) (C := C) S H
  have hIntrinsic : finiteDeletionLocalChange
      (k := k) D HD.locallyRepresentationFinite yS = 0 := by
    rw [← stageLocalChange_eq_finiteDeletionLocalChange
      (k := k) H.locallyBounded.finiteCovariantRepresentables
        H.locallyRepresentationFinite R x i]
    exact hzero
  exact admissible_finiteDeletionLocalChange_rigidity
    (k := k) D HD yS hIntrinsic M hM hMy

/-- The first equality stage of the covering telescope is the undeleted
ambient category.  Hence its rigidity conclusion applies directly to every
ambient indecomposable module which is nonzero at the chosen object. -/
theorem firstStageLocalChange_rigidity
    (H : IsAdmissible (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C)
    (hzero : stageLocalChange
      (k := k) H.locallyRepresentationFinite R x R.firstIndex = 0)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hMx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 := by
  let S := stageDeletedSet N R.representative x R.firstIndex.castSucc
  have hS : S = ∅ := by
    change stageDeletedSet N R.representative x 0 = ∅
    exact stageDeletedSet_zero N R.representative x
  have hvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj := by
    intro Y hY
    rw [hS] at hY
    exact False.elim hY
  let RM := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C S M hvanish
  have hRM : Indecomposable RM :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C S M hM hvanish
  have hRMx : ¬ IsZero
      (RM.obj.obj.obj (stageNextObject (k := k) R x R.firstIndex)) := by
    change ¬ IsZero
      (M.obj.obj.obj (R.representative R.firstIndex • x))
    simpa using hMx
  have hdim := stageLocalChange_rigidity
    (k := k) H R x R.firstIndex hzero RM hRM hRMx
  change Module.finrank k
    (M.obj.obj.obj (R.representative R.firstIndex • x)) = 1 at hdim
  rw [R.representative_first, one_smul] at hdim
  exact hdim

end MagnitudeConjecture.ObjectDeletion
