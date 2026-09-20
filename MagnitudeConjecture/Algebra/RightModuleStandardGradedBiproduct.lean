import MagnitudeConjecture.Algebra.RightModuleStandardGradedIncoming
import MagnitudeConjecture.CategoryTheory.GradedMatrixBicone

/-! # The actual graded direct-sum decomposition of each standard-form matrix object -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance gradedBiproductHomFinite (X Y : S.StandardFormMeshCategory) :
    FiniteDimensional k (X ⟶ Y) := S.standardFormMeshHomFinite X Y

/-- The actual matrix direct sum, with its degree-zero coordinate maps. -/
def standardFormGradedMatrixBicone (X : Mat_ S.StandardFormMeshCategory) (t : ℤ) :
    Bicone (fun i ↦ (⟨S.standardFormGradedVertexFunctor.obj (X.X i), t⟩ :
      Graded.FiniteGradedModule.ShiftedModule)) :=
  Graded.FiniteGradedModule.homGrading.shiftedBicone
    (S.standardFormGradedFunctor.mapBicone (GradedCategory.HomGrading.matrixBicone X))
    (fun i ↦ S.standardFormGradedMap_homogeneous S.standardFormMeshHomFinite
      (S.standardFormIntegerHomGrading.matrixBicone_π_homogeneous X i))
    (fun i ↦ S.standardFormGradedMap_homogeneous S.standardFormMeshHomFinite
      (S.standardFormIntegerHomGrading.matrixBicone_ι_homogeneous X i)) t

/-- The coordinate maps still sum to the identity after graded realization. -/
def standardFormGradedMatrixBicone_isBilimit (X : Mat_ S.StandardFormMeshCategory) (t : ℤ) :
    (S.standardFormGradedMatrixBicone X t).IsBilimit := by
  apply Graded.FiniteGradedModule.homGrading.shiftedBiconeIsBilimit
  simp only [Functor.mapBicone, ← Functor.map_comp, ← Functor.map_sum]
  exact (congrArg S.standardFormGradedFunctor.map
    (GradedCategory.HomGrading.matrixBicone_total X)).trans (S.standardFormGradedFunctor.map_id X)

/-- The shift of an actual represented matrix object is the biproduct of
its represented entries at that same shift, retaining every occurrence. -/
def standardFormGradedMatrixBiproductIso (X : Mat_ S.StandardFormMeshCategory) (t : ℤ) :
    (⟨S.standardFormGradedFunctor.obj X, t⟩ : Graded.FiniteGradedModule.ShiftedModule) ≅
      ⨁ (fun i ↦ (⟨S.standardFormGradedVertexFunctor.obj (X.X i), t⟩ :
        Graded.FiniteGradedModule.ShiftedModule)) :=
  biproduct.uniqueUpToIso _ (S.standardFormGradedMatrixBicone_isBilimit X t)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
