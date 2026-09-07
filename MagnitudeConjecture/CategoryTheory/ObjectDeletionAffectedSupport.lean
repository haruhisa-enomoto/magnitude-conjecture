import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStages
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageControlWindow

/-!
# The deleted-module part of the stagewise affected support

At a successor step, the chosen coset representative is a surviving object
of the current stage.  Every indecomposable module which fails to survive its
deletion is nonzero there and hence belongs to the two-step endpoint core.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable {N : Subgroup G} [N.Normal]

/-- The object deleted at step `i`, viewed as a surviving object of the stage
before that deletion. -/
def stageNextObject
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m) :
    StageCategory (k := k) N R.representative x i.castSucc :=
  survivingObj (k := k) C
    (stageDeletedSet N R.representative x i.castSucc)
    (R.representative_smul_not_mem_stageDeletedSet x i)

/-- Every indecomposable current-stage module nonzero at the next object to
be deleted lies in the two-step control core centered at that object. -/
theorem mem_deletionTwoStepModuleCore_of_nontrivial_at_stageNextObject
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := StageCategory (k := k) N R.representative x i.castSucc) k)
    (hM : Indecomposable M)
    (hMi : Nontrivial (M.obj.obj.obj (stageNextObject (k := k) R x i))) :
    M ∈ deletionTwoStepModuleCore (k := k) C hrep
      (R.representative i • x)
      (stageDeletedSet N R.representative x i.castSucc) :=
  mem_deletionTwoStepModuleCore_of_nontrivial_at (k := k) C hrep
    (R.representative i • x)
    (stageDeletedSet N R.representative x i.castSucc)
    (R.representative_smul_not_mem_stageDeletedSet x i) M hM hMi

end MagnitudeConjecture.ObjectDeletion
