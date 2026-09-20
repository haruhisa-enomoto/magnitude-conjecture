import MagnitudeConjecture.CategoryTheory.CategoricalIrreducibleSpace
import MagnitudeConjecture.CategoryTheory.RadicalSquareFullSubcategory

/-! # Irreducible quotient spaces across an incoming-closed full subcategory -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CategoricalIrreducible
universe u v w
variable (k : Type u) [Field k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
variable (P : ObjectProperty C)

/-- Fullness identifies the intrinsic radical numerator with the ambient one. -/
def radicalFullSubcategoryEquiv (X Y : P.FullSubcategory) :
    radical k X.obj Y.obj ≃ₗ[k] radical k X Y where
  toFun f := ⟨⟨f.val⟩,
    (isRadicalMorphism_iff_map_of_fullyFaithful P.ι P.fullyFaithfulι ⟨f.val⟩).mpr f.property⟩
  invFun f := ⟨f.val.hom,
    (isRadicalMorphism_iff_map_of_fullyFaithful P.ι P.fullyFaithfulι f.val).mp f.property⟩
  left_inv _ := rfl
  right_inv f := by
    apply Subtype.ext
    apply ObjectProperty.hom_ext
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [HasBinaryBiproducts C] [HasFiniteBiproducts C]
variable (hdec : ∀ M : C, Nonempty (CategoryTheory.FiniteIndecomposableDecomposition M))
variable (X Y : P.FullSubcategory)
variable (hY : ∀ Z : C, Indecomposable Z → ∀ b : Z ⟶ Y.obj, b ≠ 0 → P Z)

include hdec hY in
/-- The numerator equivalence carries the intrinsic radical-square denominator
onto the full-subcategory denominator at an incoming-closed target. -/
theorem denominator_map_fullSubcategory :
    (denominator k X.obj Y.obj).map (radicalFullSubcategoryEquiv k P X Y).toLinearMap =
      denominator k X Y := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (radicalSquare_fullSubcategory_iff P hdec X Y hY ⟨g.val⟩).mp hg
  · intro hf
    refine ⟨(radicalFullSubcategoryEquiv k P X Y).symm f, ?_,
      (radicalFullSubcategoryEquiv k P X Y).apply_symm_apply f⟩
    exact (radicalSquare_fullSubcategory_iff P hdec X Y hY f.val).mpr hf

/-- Interior restriction identifies the actual linear irreducible quotient
spaces, not just the existence of irreducible maps. -/
def spaceFullSubcategoryEquiv : Space k X.obj Y.obj ≃ₗ[k] Space k X Y :=
  Submodule.Quotient.equiv _ _ (radicalFullSubcategoryEquiv k P X Y)
    (denominator_map_fullSubcategory k P hdec X Y hY)

end MagnitudeConjecture.CategoricalIrreducible
