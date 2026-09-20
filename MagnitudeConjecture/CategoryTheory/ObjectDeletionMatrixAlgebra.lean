import MagnitudeConjecture.CategoryTheory.CategoryAlgebraMatrixEquivalence
import MagnitudeConjecture.CategoryTheory.ObjectDeletionConvexComparison

/-! # Matrix algebras of deletions with no surviving factorization relation -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.ObjectDeletion
universe v
variable {k : Type v} [Field k]
variable (C : Type) [Category.{v} C] [Preadditive C] [Linear k C]
variable (S : Set C)

/-- Deletion changes morphisms but keeps exactly the surviving object set. -/
theorem deletionFunctor_obj_bijective :
    Function.Bijective (functor (k := k) C S).obj := by
  constructor
  · intro X Y h
    apply ObjectProperty.FullSubcategory.ext
    exact congrArg (fun Z : DeletionCategory (k := k) C S ↦ Z.obj.as) h
  · intro X
    refine ⟨⟨X.obj.as, X.property⟩, ?_⟩
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    rfl

/-- The surviving and deleted categories have the same object coordinates. -/
def deletionObjectEquiv : SurvivingCategory C S ≃ DeletionCategory (k := k) C S :=
  Equiv.ofBijective _ (deletionFunctor_obj_bijective (k := k) C S)

instance deletionMatrixFintype [Fintype (SurvivingCategory C S)] :
    Fintype (DeletionCategory (k := k) C S) :=
  Fintype.ofEquiv _ (deletionObjectEquiv (k := k) C S)

/-- If no nonzero composite between survivors passes through a deleted object,
the finite deletion algebra equals the surviving full-category algebra. -/
def survivingDeletionMatrixAlgEquiv [Fintype (SurvivingCategory C S)]
    (hS : NoDeletedFactorization C S) :
    End (CoveringHom.categoryAlgebraTuple (C := SurvivingCategory C S)) ≃ₐ[k]
      End (CoveringHom.categoryAlgebraTuple (C := DeletionCategory (k := k) C S)) := by
  letI := functor_faithful_of_noDeletedFactorization (k := k) C S hS
  exact CoveringHom.categoryAlgebraMatrixEquiv (functor (k := k) C S)
    (deletionFunctor_obj_bijective (k := k) C S)

end MagnitudeConjecture.ObjectDeletion
