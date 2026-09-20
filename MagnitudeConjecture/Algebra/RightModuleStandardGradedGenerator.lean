import MagnitudeConjecture.Algebra.RightModuleStandardFormMesh
import MagnitudeConjecture.CategoryTheory.MeshHomGrading
import MagnitudeConjecture.CategoryTheory.GradedAdditiveEnvelope
import MagnitudeConjecture.CategoryTheory.GradedGeneratorModule

/-! # Graded generator modules for the standard-form mesh category -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The actual mesh Hom grading supplied by the standard-form translation quiver. -/
def standardFormIntegerHomGrading : GradedCategory.HomGrading k S.StandardFormMeshCategory := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) := fun x y ↦ S.standardFormArrowFintype x y
  exact MeshCategory.homGrading S.standardFormRightMeshData

/-- The projective vertices, viewed in the additive envelope of the mesh category. -/
def standardGradedProjectiveFamily (p : S.StandardFormProjectiveMeshCategory) :
    Mat_ S.StandardFormMeshCategory :=
  (Mat_.embedding S.StandardFormMeshCategory).obj (S.standardFormProjectiveMeshInclusion.obj p)

variable (hfinite : S.StandardFormMeshHomFinite)

/-- The mesh grading extended to the additive envelope. -/
def standardFormAdditiveHomGrading : GradedCategory.HomGrading k (Mat_ S.StandardFormMeshCategory) := by
  letI : ∀ X Y : S.StandardFormMeshCategory, FiniteDimensional k (X ⟶ Y) := hfinite
  exact S.standardFormIntegerHomGrading.additiveEnvelope

/-- The opposite endomorphism algebra of the projective sum in the mesh additive envelope. -/
abbrev StandardGradedGeneratorAlgebra := (End (⨁ S.standardGradedProjectiveFamily))ᵐᵒᵖ

/-- The internal algebra grading for the standard-form projective generator. -/
def standardGradedGeneratorAlgebraGrading : Graded.VectorGrading k S.StandardGradedGeneratorAlgebra := by
  letI : ∀ X Y : S.StandardFormMeshCategory, FiniteDimensional k (X ⟶ Y) := hfinite
  exact (S.standardFormAdditiveHomGrading hfinite).generatorAlgebraGrading S.standardGradedProjectiveFamily

/-- Every object of the mesh additive envelope yields an actual graded right module. -/
def standardGradedGeneratorModule (X : Mat_ S.StandardFormMeshCategory) :
    Graded.ModuleGrading (M := (⨁ S.standardGradedProjectiveFamily ⟶ X))
      (S.standardGradedGeneratorAlgebraGrading hfinite) := by
  letI : ∀ X Y : S.StandardFormMeshCategory, FiniteDimensional k (X ⟶ Y) := hfinite
  exact (S.standardFormAdditiveHomGrading hfinite).generatorModuleGrading S.standardGradedProjectiveFamily X

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
