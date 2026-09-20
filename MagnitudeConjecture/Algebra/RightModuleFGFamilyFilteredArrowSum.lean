import MagnitudeConjecture.Algebra.RightModuleFGFamilyIncomingSum
import Mathlib.Data.Fintype.BigOperators

/-! # Filtered arrow sums for a numbered family under an equivalence -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra BigOperators
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u v
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {ι : Type} [Fintype ι]
variable {C : Type v} [CategoryTheory.Category.{u} C] [Preadditive C] [Linear k C]
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- Filtering targets commutes with transferring the numbered arrow sum. -/
theorem ofFGFamily_inverse_filtered_arrow_sum_eq
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ C) [E.functor.Additive] [E.functor.Linear k]
    (H : ι → C)
    (hi : ∀ i, Indecomposable (E.inverse.obj (H i)))
    (hc : ∀ X : RightModule.FinitelyGeneratedCategory.{u} A, Indecomposable X →
      ∃ i, Nonempty (X ≅ E.inverse.obj (H i)))
    (hs : ∀ i j, Nonempty (E.inverse.obj (H i) ≅ E.inverse.obj (H j)) → i = j)
    (P : ι → Prop) [DecidablePred P] :
    (∑ j : {j : Fin (Fintype.card ι) // P ((Fintype.equivFin ι).symm j)},
      ∑ i : Fin (Fintype.card ι), FiniteTauMatrix.arrowMultiplicity
        (ofFGFamily (k := k) (fun a ↦ E.inverse.obj (H a)) hi hc hs).finiteTauCategoryData.toFiniteRightTauCategoryData i j.val) =
      ∑ b : {b : ι // P b}, ∑ a : ι,
        Module.finrank k (CategoricalIrreducible.Space k (H a) (H b.val)) := by
  calc
    _ = ∑ j : {j : Fin (Fintype.card ι) // P ((Fintype.equivFin ι).symm j)},
        ∑ a : ι, Module.finrank k (CategoricalIrreducible.Space k
          (H a) (H ((Fintype.equivFin ι).symm j.val))) :=
      Finset.sum_congr rfl (fun j _ ↦ ofFGFamily_inverse_incoming_sum_eq
        (k := k) E H hi hc hs j.val)
    _ = _ := (Equiv.subtypeEquivOfSubtype (p := P) (Fintype.equivFin ι).symm).sum_comp
      (fun b ↦ ∑ a : ι, Module.finrank k (CategoricalIrreducible.Space k (H a) (H b.val)))

/-- A known filtered quotient sum supplies the numbered arrow sum directly. -/
theorem ofFGFamily_inverse_filtered_arrow_sum_eq_of_sum
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ C) [E.functor.Additive] [E.functor.Linear k]
    (H : ι → C)
    (hi : ∀ i, Indecomposable (E.inverse.obj (H i)))
    (hc : ∀ X : RightModule.FinitelyGeneratedCategory.{u} A, Indecomposable X →
      ∃ i, Nonempty (X ≅ E.inverse.obj (H i)))
    (hs : ∀ i j, Nonempty (E.inverse.obj (H i) ≅ E.inverse.obj (H j)) → i = j)
    (P : ι → Prop) [DecidablePred P] (N : ℕ)
    (hN : (∑ b : {b : ι // P b}, ∑ a : ι,
      Module.finrank k (CategoricalIrreducible.Space k (H a) (H b.val))) = N) :
    (∑ j : {j : Fin (Fintype.card ι) // P ((Fintype.equivFin ι).symm j)},
      ∑ i : Fin (Fintype.card ι), FiniteTauMatrix.arrowMultiplicity
        (ofFGFamily (k := k) (fun a ↦ E.inverse.obj (H a)) hi hc hs).finiteTauCategoryData.toFiniteRightTauCategoryData i j.val) = N :=
  (ofFGFamily_inverse_filtered_arrow_sum_eq (k := k) E H hi hc hs P).trans hN

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
