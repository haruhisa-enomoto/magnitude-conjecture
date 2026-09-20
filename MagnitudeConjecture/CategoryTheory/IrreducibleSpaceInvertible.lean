import MagnitudeConjecture.CategoryTheory.CategoricalIrreducibleSpace

/-! # Vanishing when every nonzero morphism is invertible -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.CategoricalRadical
namespace MagnitudeConjecture.CategoricalIrreducible
universe u v w
variable (k : Type u) [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C]

/-- A Hom space with only invertible nonzero morphisms has zero radical. -/
theorem radical_eq_bot_of_nonzero_isIso (X Y : C)
    (h : ∀ f : X ⟶ Y, f ≠ 0 → IsIso f) : radical k X Y = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  by_contra hn
  letI := h f hn
  have hr : IsRadicalMorphism f := hf
  letI : IsIso (0 : X ⟶ X) := by
    simpa only [IsIso.hom_inv_id, sub_self] using hr (inv f)
  have hz : 𝟙 X = 0 := by
    simpa only [zero_comp] using (IsIso.hom_inv_id (0 : X ⟶ X)).symm
  have he := Category.id_comp f
  rw [hz, zero_comp] at he
  exact hn he.symm

/-- A zero radical numerator has zero irreducible quotient dimension. -/
theorem finrank_eq_zero_of_radical_eq_bot (X Y : C) (h : radical k X Y = ⊥) :
    Module.finrank k (Space k X Y) = 0 := by
  letI : Subsingleton (radical k X Y) := by
    rw [h]
    infer_instance
  letI : Subsingleton (Space k X Y) := inferInstance
  exact Module.finrank_zero_of_subsingleton

end MagnitudeConjecture.CategoricalIrreducible
