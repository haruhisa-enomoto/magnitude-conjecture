import MagnitudeConjecture.Algebra.RightModuleSkeletonOfFGFamily
import MagnitudeConjecture.Algebra.RightModuleIntrinsicArrowMultiplicity
import MagnitudeConjecture.CategoryTheory.IrreducibleSpaceIso

/-! # Arrow multiplicities for a numbered finite module family -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {ι : Type} [Fintype ι]
variable (F : ι → RightModule.FinitelyGeneratedCategory.{u} A)
variable (hF : ∀ i, Indecomposable (F i))
variable (hc : ∀ X : RightModule.FinitelyGeneratedCategory.{u} A, Indecomposable X →
  ∃ i, Nonempty (X ≅ F i))
variable (hs : ∀ i j, Nonempty (F i ≅ F j) → i = j)

/-- Rebundling a family as a numbered skeleton preserves each representative. -/
def ofFGFamily_fgObjIso (i : Fin (ofFGFamily (k := k) F hF hc hs).n) :
    (ofFGFamily (k := k) F hF hc hs).fgObj i ≅ F ((Fintype.equivFin ι).symm i) :=
  ObjectProperty.isoMk _ (Iso.refl _)

variable [IsAlgClosed k]
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- Numbering a finite family computes arrows by its original quotient spaces. -/
theorem ofFGFamily_arrowMultiplicity_eq (i j : Fin (ofFGFamily (k := k) F hF hc hs).n) :
    FiniteTauMatrix.arrowMultiplicity
      (ofFGFamily (k := k) F hF hc hs).finiteTauCategoryData.toFiniteRightTauCategoryData i j =
        Module.finrank k (CategoricalIrreducible.Space k
          (F ((Fintype.equivFin ι).symm i)) (F ((Fintype.equivFin ι).symm j))) :=
  ((ofFGFamily (k := k) F hF hc hs).intrinsicIrreducible_finrank_eq_arrowMultiplicity i j).symm.trans
    (CategoricalIrreducible.spaceIsoEquiv k (ofFGFamily_fgObjIso F hF hc hs i)
      (ofFGFamily_fgObjIso F hF hc hs j)).finrank_eq

variable {C : Type v} [CategoryTheory.Category.{u} C] [Preadditive C] [Linear k C]

/-- For a family realized by inverse images, numbering computes arrows on
the original objects of the equivalent category. -/
theorem ofFGFamily_inverse_arrowMultiplicity_eq
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ C) [E.functor.Additive] [E.functor.Linear k]
    (H : ι → C)
    (hi : ∀ i, Indecomposable (E.inverse.obj (H i)))
    (hcomplete : ∀ X : RightModule.FinitelyGeneratedCategory.{u} A, Indecomposable X →
      ∃ i, Nonempty (X ≅ E.inverse.obj (H i)))
    (hskeletal : ∀ i j, Nonempty (E.inverse.obj (H i) ≅ E.inverse.obj (H j)) → i = j)
    (i j : Fin (Fintype.card ι)) :
    FiniteTauMatrix.arrowMultiplicity
      (ofFGFamily (k := k) (fun a ↦ E.inverse.obj (H a)) hi hcomplete hskeletal).finiteTauCategoryData.toFiniteRightTauCategoryData i j =
        Module.finrank k (CategoricalIrreducible.Space k
          (H ((Fintype.equivFin ι).symm i)) (H ((Fintype.equivFin ι).symm j))) :=
  (ofFGFamily_arrowMultiplicity_eq (k := k) (fun a ↦ E.inverse.obj (H a))
    hi hcomplete hskeletal i j).trans
      (CategoricalIrreducible.spaceInverseEquivalence k E
        (H ((Fintype.equivFin ι).symm i)) (H ((Fintype.equivFin ι).symm j))).finrank_eq

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
