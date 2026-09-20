import MagnitudeConjecture.Algebra.RightModuleStandardGradedFGRecovery
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalControlHeight
import MagnitudeConjecture.CategoryTheory.MeshPositiveTail

/-! # The actual degree-one incoming maps and their interval support -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance incomingGradedQuiver : Quiver (Fin S.n) := S.standardFormQuiver
local instance incomingGradedArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- The actual incoming-arrow sum, in the raw mesh additive envelope. -/
def standardGradedIncomingObject (z : Fin S.n) : Mat_ S.StandardFormMeshCategory :=
  (S.standardFormMeshRawFunctor (k := k)).mapMat_.obj
    (S.standardFormRightMeshData.additiveIncomingObj (k := k) z)

/-- The literal incoming matrix, whose columns are the incoming mesh arrows. -/
def standardGradedIncomingMap (z : Fin S.n) :
    S.standardGradedIncomingObject z ⟶
      (Mat_.embedding _).obj (MeshCategory.obj (k := k) S.standardFormRightMeshData z) :=
  (S.standardFormMeshRawFunctor (k := k)).mapMat_.map
    (S.standardFormRightMeshData.additiveIncomingMap (k := k) z)

/-- All entries of the incoming matrix have degree one. -/
theorem standardGradedIncomingMap_homogeneous (z : Fin S.n) :
    S.standardGradedIncomingMap z ∈
      (S.standardFormAdditiveHomGrading S.standardFormMeshHomFinite).component _ _ 1 := by
  intro i hi j hj
  change S.standardFormRightMeshData.incomingArrowHom (k := k) i ∈
    Graded.integerComponent (MeshCategory.lengthComponent S.standardFormRightMeshData i.1 z) 1
  simpa [Graded.integerComponent] using
    S.standardFormRightMeshData.incomingArrowHom_mem_lengthComponent_one (k := k) i

/-- The canonical incoming map, with its middle shifted one degree above its target. -/
def standardFormGradedIncomingMap (z : Fin S.n) (t : ℤ) :
    (⟨S.standardFormGradedFunctor.obj (S.standardGradedIncomingObject z), t + 1⟩ :
      Graded.FiniteGradedModule.ShiftedModule) ⟶ ⟨S.standardFormGradedFamily z, t⟩ :=
  ⟨S.standardFormGradedFunctor.map (S.standardGradedIncomingMap z), by
    have h := S.standardFormGradedMap_homogeneous S.standardFormMeshHomFinite
      (S.standardGradedIncomingMap_homogeneous z)
    have hd : t + 1 - t = (1 : ℤ) := by omega
    change S.standardFormGradedFunctor.map (S.standardGradedIncomingMap z) ∈
      Graded.FiniteGradedModule.homGrading.component _ _ (t + 1 - t)
    rw [hd]
    exact h⟩

/-- The common mesh degree bound controls every finite sum of the actual representatives. -/
theorem standardFormGradedObject_support_control (X : Mat_ S.StandardFormMeshCategory)
    (d : ℤ) (hd : d ∈ (S.standardFormGradedFunctor.obj X).grading.toVectorGrading.support) :
    0 ≤ d ∧ d ≤ S.standardFormIntervalControlHeight := by
  have hn := ((S.standardFormGradedFunctor.obj X).grading.toVectorGrading.mem_support_iff d).mp hd
  by_contra hout
  have hb : d < 0 ∨ (S.standardFormIntervalControlHeight : ℤ) < d := by omega
  exact hn (S.standardFormGradedObject_component_eq_bot d
    (fun U V ↦ S.standardFormIntervalControlHeight_hom_bound U V d hb) X)

/-- Any nonnegative shift of a represented finite sum fits in the predicted interval. -/
theorem standardFormGradedObject_shifted_supported (X : Mat_ S.StandardFormMeshCategory)
    (t : ℤ) (m : ℕ) (ht : 0 ≤ t) (hm : (S.standardFormIntervalControlHeight : ℤ) + t ≤ m) :
    Graded.FiniteGradedModule.SupportedIn m
      (⟨S.standardFormGradedFunctor.obj X, t⟩ : Graded.FiniteGradedModule.ShiftedModule) := by
  intro d hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
  have hb := S.standardFormGradedObject_support_control X e he
  change 0 ≤ e + t ∧ e + t ≤ (m : ℤ)
  omega

/-- Both the ordinary incoming map and its next shift lie in the one interval [0,h+2]. -/
theorem standardFormGradedIncomingMap_supported (z : Fin S.n) (t : ℤ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Graded.FiniteGradedModule.SupportedIn (S.standardFormIntervalControlHeight + 2)
      (⟨S.standardFormGradedFunctor.obj (S.standardGradedIncomingObject z), t + 1⟩ :
        Graded.FiniteGradedModule.ShiftedModule) ∧
    Graded.FiniteGradedModule.SupportedIn (S.standardFormIntervalControlHeight + 2)
      (⟨S.standardFormGradedFamily z, t⟩ : Graded.FiniteGradedModule.ShiftedModule) := by
  constructor
  · exact S.standardFormGradedObject_shifted_supported _ (t + 1) _ (by omega) (by omega)
  · exact S.standardFormGradedObject_shifted_supported _ t _ ht0 (by omega)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
