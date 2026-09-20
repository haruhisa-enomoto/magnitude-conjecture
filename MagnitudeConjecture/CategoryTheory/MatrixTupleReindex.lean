import MagnitudeConjecture.CategoryTheory.LinearMatrixFunctor

/-! # Reindexing finite matrix tuples -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CategoryTheory
universe u v
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {I J : Type} [Fintype I] [Fintype J]

/-- A change of finite index set gives an isomorphism of matrix tuples. -/
def matrixTupleReindexIso (e : J ≃ I) (X : I → C) :
    (⟨J, X ∘ e⟩ : Mat_ C) ≅ (⟨I, X⟩ : Mat_ C) :=
  Mat_.isoBiproductEmbedding (⟨J, X ∘ e⟩ : Mat_ C) ≪≫
    biproduct.reindex e (fun i ↦ (Mat_.embedding C).obj (X i)) ≪≫
      (Mat_.isoBiproductEmbedding (⟨I, X⟩ : Mat_ C)).symm

/-- Reindexing a finite tuple preserves its endomorphism algebra. -/
def matrixTupleReindexEndAlgEquiv (e : J ≃ I) (X : I → C) :
    End (⟨J, X ∘ e⟩ : Mat_ C) ≃ₐ[k] End (⟨I, X⟩ : Mat_ C) :=
  Iso.endAlgEquiv (matrixTupleReindexIso e X)

end MagnitudeConjecture.CategoryTheory
