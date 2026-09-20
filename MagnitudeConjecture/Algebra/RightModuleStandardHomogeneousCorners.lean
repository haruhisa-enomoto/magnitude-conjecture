import MagnitudeConjecture.Algebra.RightModuleStandardHomogeneousIdempotents
import MagnitudeConjecture.CategoryTheory.GradedGeneratorCorners
import MagnitudeConjecture.CategoryTheory.GradedAdditiveEmbeddingHom
import MagnitudeConjecture.Graded.CornerTransport

/-! # Degree-zero corners of the actual standard-form algebra -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance standardCornerMeshHomFinite (X Y : S.StandardFormMeshCategory) :
    FiniteDimensional k (X ⟶ Y) := S.standardFormMeshHomFinite X Y
local instance standardCornerQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance standardCornerArrowFintype (x y : Fin S.n) :
    Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- Homogeneous corners of the standard algebra are exactly the mesh Hom
components between the selected projective vertices. -/
def standardFormHomogeneousCornerEquiv
    (p q : S.StandardFormProjectiveMeshCategory) (d : ℤ) :
    Graded.cornerComponent (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
      (S.standardFormHomogeneousIdempotent p) (S.standardFormHomogeneousIdempotent q) d ≃ₗ[k]
      S.standardFormIntegerHomGrading.component
        (S.standardFormProjectiveMeshInclusion.obj p)
        (S.standardFormProjectiveMeshInclusion.obj q) d :=
  (Graded.cornerComapEquiv (S.standardGradedGeneratorAlgebraGrading S.standardFormMeshHomFinite)
    (S.standardFormOppositeGeneratorAlgEquiv S.standardFormMeshHomFinite)
    (GradedCategory.HomGrading.generatorIdempotent S.standardGradedProjectiveFamily p)
    (GradedCategory.HomGrading.generatorIdempotent S.standardGradedProjectiveFamily q) d).trans
      (((S.standardFormAdditiveHomGrading S.standardFormMeshHomFinite).generatorCornerEquiv
        S.standardGradedProjectiveFamily p q d).trans
          (S.standardFormIntegerHomGrading.additiveEmbeddingComponentEquiv _ _ d))

/-- Every diagonal degree-zero corner is one-dimensional. -/
theorem standardFormHomogeneousCorner_diagonal
    (p : S.StandardFormProjectiveMeshCategory) :
    Module.finrank k
      (Graded.cornerComponent (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
        (S.standardFormHomogeneousIdempotent p) (S.standardFormHomogeneousIdempotent p) 0) = 1 := by
  rw [(S.standardFormHomogeneousCornerEquiv p p 0).finrank_eq]
  have hz : S.standardFormIntegerHomGrading.component
      (S.standardFormProjectiveMeshInclusion.obj p)
      (S.standardFormProjectiveMeshInclusion.obj p) 0 =
      k ∙ (𝟙 (MeshCategory.obj (k := k) S.standardFormRightMeshData p.1)) := by
    change Graded.integerComponent
      (MeshCategory.lengthComponent S.standardFormRightMeshData p.1 p.1) 0 = _
    simpa only [Graded.integerComponent, le_refl, if_true, Int.toNat_zero] using
      MeshCategory.lengthComponent_zero_self (k := k) S.standardFormRightMeshData p.1
  exact (LinearEquiv.ofEq _ _ hz).finrank_eq.trans
    (finrank_span_singleton (MeshCategory.id_ne_zero (k := k) S.standardFormRightMeshData p.1))

/-- Distinct primitive labels have no degree-zero corner maps. -/
theorem standardFormHomogeneousCorner_off_diagonal
    (p q : S.StandardFormProjectiveMeshCategory) (hpq : p ≠ q) :
    Graded.cornerComponent (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
      (S.standardFormHomogeneousIdempotent p) (S.standardFormHomogeneousIdempotent q) 0 = ⊥ := by
  have hn : S.standardFormProjectiveMeshInclusion.obj p ≠
      S.standardFormProjectiveMeshInclusion.obj q := by
    intro h
    apply hpq
    apply Subtype.ext
    exact congrArg (fun X : S.StandardFormMeshCategory ↦ X.as) h
  have hz := S.standardFormGraded_zero_of_ne _ _ hn
  apply bot_unique
  intro a ha
  let E := S.standardFormHomogeneousCornerEquiv p q 0
  have h : E ⟨a, ha⟩ = 0 := by
    apply Subtype.ext
    exact hz.le (E ⟨a, ha⟩).property
  have h' := E.injective (h.trans (map_zero E).symm)
  exact congrArg Subtype.val h'

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
