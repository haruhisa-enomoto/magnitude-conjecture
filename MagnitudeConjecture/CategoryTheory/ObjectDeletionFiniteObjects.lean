import MagnitudeConjecture.CategoryTheory.ObjectDeletionComparison
import Mathlib.Data.Fintype.Card

/-! # Finite object counts under deletion -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.ObjectDeletion
universe u v
variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- Distinct surviving quotient objects have distinct original labels. -/
theorem deletionUnderlying_injective (S : Set C) :
    Function.Injective (fun X : DeletionCategory (k := k) C S ↦ X.obj.as) := by
  intro X Y h
  apply ObjectProperty.FullSubcategory.ext
  exact CategoryTheory.Quotient.ext h

instance finiteDeletionFintype [Fintype C] (S : Set C) :
    Fintype (DeletionCategory (k := k) C S) :=
  Fintype.ofInjective _ (deletionUnderlying_injective (k := k) C S)

/-- Deleting any specified object strictly reduces the finite object count. -/
theorem deletion_card_lt [Fintype C] (S : Set C) {x : C} (hx : x ∈ S) :
    Fintype.card (DeletionCategory (k := k) C S) < Fintype.card C := by
  apply Fintype.card_lt_of_injective_of_notMem
    (fun X : DeletionCategory (k := k) C S ↦ X.obj.as)
    (deletionUnderlying_injective (k := k) C S) (b := x)
  rintro ⟨X, rfl⟩
  exact X.property hx

end MagnitudeConjecture.ObjectDeletion
