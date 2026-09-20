import MagnitudeConjecture.Algebra.RightModuleFGFamilyArrowMultiplicity
import Mathlib.Data.Fintype.BigOperators

/-! # Incoming arrow sums for a numbered family under an equivalence -/
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

/-- Summing the numbered arrows of an inverse-image family gives the incoming
irreducible dimension sum in the original category. -/
theorem ofFGFamily_inverse_incoming_sum_eq
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ C) [E.functor.Additive] [E.functor.Linear k]
    (H : ι → C)
    (hi : ∀ i, Indecomposable (E.inverse.obj (H i)))
    (hc : ∀ X : RightModule.FinitelyGeneratedCategory.{u} A, Indecomposable X →
      ∃ i, Nonempty (X ≅ E.inverse.obj (H i)))
    (hs : ∀ i j, Nonempty (E.inverse.obj (H i) ≅ E.inverse.obj (H j)) → i = j)
    (j : Fin (Fintype.card ι)) :
    (∑ i : Fin (Fintype.card ι), FiniteTauMatrix.arrowMultiplicity
      (ofFGFamily (k := k) (fun a ↦ E.inverse.obj (H a)) hi hc hs).finiteTauCategoryData.toFiniteRightTauCategoryData i j) =
      ∑ a : ι, Module.finrank k (CategoricalIrreducible.Space k
        (H a) (H ((Fintype.equivFin ι).symm j))) := by
  calc
    _ = ∑ i : Fin (Fintype.card ι), Module.finrank k (CategoricalIrreducible.Space k
        (H ((Fintype.equivFin ι).symm i)) (H ((Fintype.equivFin ι).symm j))) :=
      Finset.sum_congr rfl (fun i _ ↦ ofFGFamily_inverse_arrowMultiplicity_eq
        (k := k) E H hi hc hs i j)
    _ = _ := (Fintype.equivFin ι).symm.sum_comp
      (fun a ↦ Module.finrank k (CategoricalIrreducible.Space k
        (H a) (H ((Fintype.equivFin ι).symm j))))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
