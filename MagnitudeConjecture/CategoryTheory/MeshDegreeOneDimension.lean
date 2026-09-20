import MagnitudeConjecture.CategoryTheory.MeshCategory
import MagnitudeConjecture.CategoryTheory.RelationQuotientComponent
import MagnitudeConjecture.CategoryTheory.PathLengthOneDimension

/-! # Degree-one mesh morphisms count arrows -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.MeshCategory
universe u v w
variable {k : Type u} [Field k] {Q : Type v} [Quiver.{w} Q]
variable [∀ x : Q, Fintype (Σ y : Q, x ⟶ y)]

/-- Composing a quadratic mesh relation with paths never produces degree one. -/
theorem RightMeshData.basisCompositeSet_degree_ne_one (T : RightMeshData Q)
    (X Y : LinearPathCategory.Category k Q) (f : X ⟶ Y)
    (hf : f ∈ LinearPathCategory.basisCompositeSet (T.meshGeneratorSet (k := k)) X Y) :
    ∃ n, n ≠ 1 ∧ f ∈ LinearPathCategory.lengthComponent X Y n := by
  rcases hf with ⟨A, B, r, hr, p, q, rfl⟩
  have hp := (LinearPathCategory.pathHom_mem_lengthComponent_iff p p.length).2 rfl
  have hr' := T.meshGeneratorSet_mem_lengthComponent_two (k := k) A B r hr
  have hq := (LinearPathCategory.pathHom_mem_lengthComponent_iff q q.length).2 rfl
  refine ⟨p.length + 2 + q.length, by omega, ?_⟩
  exact CategoricalGrading.comp_comp_mem
    (fun X Y ↦ LinearPathCategory.lengthComponent X Y)
    (fun ha hb ↦ LinearPathCategory.comp_mem_lengthComponent ha hb) hp hr' hq

/-- The mesh quotient leaves the free degree-one space unchanged. -/
def degreeOneFreeEquiv (T : RightMeshData Q) (x y : Q) :
    LinearPathCategory.lengthComponent (LinearPathCategory.obj k Q x)
      (LinearPathCategory.obj k Q y) 1 ≃ₗ[k] lengthComponent (k := k) T x y 1 :=
  LinearPathCategory.HomogeneousQuotient.componentEquiv _ _ _ 1
    (T.basisCompositeSet_degree_ne_one _ _)

/-- Degree-one mesh morphisms from x to y count quiver arrows from y to x. -/
theorem lengthComponent_one_finrank (T : RightMeshData Q) (x y : Q)
    [Fintype (y ⟶ x)] :
    Module.finrank k (lengthComponent (k := k) T x y 1) = Fintype.card (y ⟶ x) := by
  letI : Fintype (LinearPathCategory.vertex (LinearPathCategory.obj k Q y) ⟶
      LinearPathCategory.vertex (LinearPathCategory.obj k Q x)) :=
    (inferInstance : Fintype (y ⟶ x))
  exact (degreeOneFreeEquiv (k := k) T x y).symm.finrank_eq.trans
    (LinearPathCategory.lengthComponent_one_finrank _ _)

end MagnitudeConjecture.MeshCategory
