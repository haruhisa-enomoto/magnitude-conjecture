import MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd

/-! # Transporting a complete indecomposable family through an equivalence -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CategoryTheory
universe u v u' v' w
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D]
variable (E : C ≌ D) [E.functor.Additive]
variable {ι : Type w} (F : ι → D)

/-- Completeness transfers without unfolding the construction of the equivalence. -/
theorem complete_indecomposable_family_of_equivalence
    (hF : ∀ Y : D, Indecomposable Y → ∃ i, Nonempty (Y ≅ F i))
    (X : C) (hX : Indecomposable X) :
    ∃ i, Nonempty (X ≅ E.inverse.obj (F i)) := by
  have hEX := (indecomposable_map_iff_of_equivalence E.functor X).mpr hX
  obtain ⟨i, ⟨e⟩⟩ := hF (E.functor.obj X) hEX
  exact ⟨i, ⟨E.functor.preimageIso (e ≪≫ (E.counitIso.app (F i)).symm)⟩⟩

end MagnitudeConjecture.CategoryTheory
