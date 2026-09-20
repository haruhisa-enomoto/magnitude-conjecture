import MagnitudeConjecture.CategoryTheory.MeshCategory
import MagnitudeConjecture.CategoryTheory.GradedDegreeCategory

/-! # The integer Hom grading of the literal mesh category -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.MeshCategory
universe u v w
variable {k : Type u} [Field k] {Q : Type v} [Quiver.{w} Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

/-- Mesh path length, extended by zero to negative degrees. -/
def homGrading (T : RightMeshData Q) : GradedCategory.HomGrading k (RawCategory (k := k) T) :=
  GradedCategory.HomGrading.ofNat
    (fun X Y ↦ lengthComponent T X.as Y.as)
    (fun X Y ↦ lengthComponent_isInternal T X.as Y.as)
    (fun X ↦ id_mem_lengthComponent_zero T X.as)
    (fun hf hg ↦ comp_mem_lengthComponent T hf hg)

end MagnitudeConjecture.MeshCategory
