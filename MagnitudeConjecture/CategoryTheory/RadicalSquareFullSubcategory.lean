import MagnitudeConjecture.CategoryTheory.HomIdealProductFullSubcategory
import QuotientSubmoduleEquidistribution.CategoryTheory.CategoricalRadicalIdeal

/-! # Intrinsic radical-square comparison at an incoming-closed target -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open QuotientSubmoduleEquidistribution.CategoricalRadical
namespace MagnitudeConjecture
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (P : ObjectProperty C)

/-- The intrinsic radical in a full subcategory is the restricted ambient radical. -/
theorem radical_comap_fullSubcategory :
    (homIdeal : HomIdeal C).comap P.ι = (homIdeal : HomIdeal P.FullSubcategory) := by
  apply HomIdeal.ext_hom
  intro X Y
  ext f
  exact (isRadicalMorphism_iff_map_of_fullyFaithful P.ι P.fullyFaithfulι f).symm

variable [HasBinaryBiproducts C] [HasFiniteBiproducts C]

/-- If all nonzero incoming indecomposables to the target lie in the full
subcategory, its intrinsic radical square agrees with the ambient one. -/
theorem radicalSquare_fullSubcategory_iff
    (hdec : ∀ M : C, Nonempty (CategoryTheory.FiniteIndecomposableDecomposition M))
    (X Y : P.FullSubcategory)
    (hY : ∀ Z : C, Indecomposable Z → ∀ b : Z ⟶ Y.obj, b ≠ 0 → P Z)
    (f : X ⟶ Y) :
    f.hom ∈ ((homIdeal : HomIdeal C) ⋆ᵢ homIdeal).hom X.obj Y.obj ↔
      f ∈ ((homIdeal : HomIdeal P.FullSubcategory) ⋆ᵢ homIdeal).hom X Y := by
  have h := homIdealProduct_fullSubcategory_iff P hdec homIdeal homIdeal X Y hY f
  rwa [radical_comap_fullSubcategory P] at h

end MagnitudeConjecture
