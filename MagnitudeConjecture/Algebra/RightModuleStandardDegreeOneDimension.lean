import MagnitudeConjecture.Algebra.RightModuleStandardGradedGenerator
import MagnitudeConjecture.CategoryTheory.MeshDegreeOneDimension

/-! # The degree-one standard-form component has the ordinary arrow multiplicity -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The degree-one Hom dimension is the ordinary skeleton's arrow multiplicity,
with source and target in the module-category orientation. -/
theorem standardFormIntegerHomGrading_one_finrank (X Y : S.StandardFormMeshCategory) :
    Module.finrank k (S.standardFormIntegerHomGrading.component X Y 1) =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData X.as Y.as := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) := fun x y ↦ S.standardFormArrowFintype x y
  change Module.finrank k
    (MeshCategory.lengthComponent (k := k) S.standardFormRightMeshData X.as Y.as 1) = _
  rw [MeshCategory.lengthComponent_one_finrank]
  exact Fintype.card_fin _

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
