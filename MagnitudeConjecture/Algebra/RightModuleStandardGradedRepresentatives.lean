import MagnitudeConjecture.Algebra.RightModuleStandardGradedObjects
import MagnitudeConjecture.CategoryTheory.GradedModuleClassification

/-! # Underlying representatives of the standard-form graded modules -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance rdGradedRepresentativesQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance rdGradedRepresentativesArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- Forgetting the grading recovers the existing represented right module. -/
def standardFormGradedObjectUnderlyingIso (X : Mat_ S.StandardFormMeshCategory) :
    (S.standardFormGradedObject S.standardFormMeshHomFinite X).module ≅
      ((S.standardFormProjectiveVertexModuleAlgebraEquivalence.functor.obj
        (S.standardGradedRecovery.obj X))).obj :=
  (MagnitudeConjecture.CategoryTheory.representedModuleEquivOverTarget (k := k)
    S.standardGradedRecovery S.standardGradedRecoveryGeneratorIso X).toModuleIso

/-- The graded representatives, with the labels of the original finite skeleton. -/
def standardFormGradedFamily (i : Fin S.n) :
    Graded.FiniteGradedModule (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite) :=
  S.standardFormGradedVertex S.standardFormMeshHomFinite
    (MeshCategory.obj (k := k) S.standardFormRightMeshData i)

/-- The underlying graded representatives are the existing algebra skeleton. -/
def standardFormGradedFamilyIso (i : Fin S.n) :
    (S.standardFormGradedFamily i).module ≅
      S.standardFormAlgebraIndecomposableSkeleton.obj i := by
  let e := S.standardGradedRecoverySingletonIso
    (MeshCategory.obj (k := k) S.standardFormRightMeshData i)
  let e' := S.standardFormProjectiveVertexModuleAlgebraEquivalence.functor.mapIso e
  exact (S.standardFormGradedObjectUnderlyingIso
    ((Mat_.embedding _).obj (MeshCategory.obj (k := k) S.standardFormRightMeshData i))).trans
    ((forget₂ (RightModule.FinitelyGeneratedCategory
        (S.standardFormAlgebra S.standardFormMeshHomFinite))
      (RightModule.Category (S.standardFormAlgebra S.standardFormMeshHomFinite))).mapIso e')

/-- Each graded representative is indecomposable after forgetting its grading. -/
theorem standardFormGradedFamily_indecomposable (i : Fin S.n) :
    Indecomposable (S.standardFormGradedFamily i).module :=
  (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso
    (S.standardFormGradedFamilyIso i)).2
      (S.standardFormAlgebraIndecomposableSkeleton.obj_indecomposable i)

/-- Every finite ungraded indecomposable has one of these gradings. -/
theorem standardFormGradedFamily_complete
    (M : RightModule.Category (S.standardFormAlgebra S.standardFormMeshHomFinite))
    (hfin : Module.Finite k M) (hM : Indecomposable M) :
    ∃ i, Nonempty (M ≅ (S.standardFormGradedFamily i).module) := by
  obtain ⟨i, ⟨e⟩⟩ := S.standardFormAlgebraIndecomposableSkeleton.complete M ⟨hfin, hM⟩
  exact ⟨i, ⟨e.trans (S.standardFormGradedFamilyIso i).symm⟩⟩

/-- The underlying representatives have no duplicate labels. -/
theorem standardFormGradedFamily_skeletal (i j : Fin S.n)
    (h : Nonempty ((S.standardFormGradedFamily i).module ≅
      (S.standardFormGradedFamily j).module)) : i = j := by
  obtain ⟨e⟩ := h
  exact S.standardFormAlgebraIndecomposableSkeleton.eq_of_iso
    ⟨(S.standardFormGradedFamilyIso i).symm.trans (e.trans (S.standardFormGradedFamilyIso j))⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
