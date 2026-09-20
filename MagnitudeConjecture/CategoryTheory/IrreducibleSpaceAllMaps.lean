import MagnitudeConjecture.CategoryTheory.CategoricalIrreducibleSpace
import QuotientSubmoduleEquidistribution.RepresentationTheory.IrreducibleCofinite

/-! # Quotients when every nonzero map is irreducible -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open QuotientSubmoduleEquidistribution.CategoricalRadical
namespace MagnitudeConjecture.CategoricalIrreducible
universe u v w
variable (k : Type u) [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C]

/-- No reverse maps implies that every forward map is radical. -/
theorem radical_eq_top_of_no_reverse (X Y : C) (h : ∀ g : Y ⟶ X, g = 0) :
    radical k X Y = ⊤ := by
  apply top_unique
  intro f _
  change IsRadicalMorphism f
  intro g
  rw [h g, comp_zero, sub_zero]
  infer_instance

private theorem id_eq_zero_of_radical_id (X : C) (h : IsRadicalMorphism (𝟙 X)) :
    𝟙 X = 0 := by
  letI : IsIso (0 : X ⟶ X) := by simpa using h (𝟙 X)
  simpa only [zero_comp] using (IsIso.hom_inv_id (0 : X ⟶ X)).symm

/-- A Hom space consisting of zero and irreducible maps has zero radical square. -/
theorem radicalSquare_eq_bot_of_all_nonzero_irreducible (X Y : C)
    (hi : ∀ f : X ⟶ Y, f ≠ 0 → IsIrreducibleMorphism f) :
    radicalSquare k X Y = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  change f ∈ ((homIdeal : HomIdeal C) ⋆ᵢ homIdeal).hom X Y at hf
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
      obtain ⟨M, a, b, ha, hb, rfl⟩ := hf
      by_contra hn
      rcases (hi (a ≫ b) hn).factorization a b rfl with hs | hs
      · letI := hs
        have hr : IsRadicalMorphism (𝟙 X) := by
          simpa only [IsSplitMono.id] using isRadicalMorphism_postcomp (retraction a) ha
        have hz := id_eq_zero_of_radical_id X hr
        have he := Category.id_comp (a ≫ b)
        rw [hz, zero_comp] at he
        exact hn he.symm
      · letI := hs
        have hr : IsRadicalMorphism (𝟙 Y) := by
          simpa only [IsSplitEpi.id] using isRadicalMorphism_precomp (section_ b) hb
        have hz := id_eq_zero_of_radical_id Y hr
        have he := Category.comp_id (a ≫ b)
        rw [hz, comp_zero] at he
        exact hn he.symm
  | zero => rfl
  | add f g _ _ hf hg => simp only [hf, hg, add_zero]
  | neg f _ hf => simp only [hf, neg_zero]

/-- If the radical is all of Hom and its square is zero, the intrinsic
irreducible quotient is linearly equivalent to Hom itself. -/
def spaceEquivHom (X Y : C) (hr : radical k X Y = ⊤)
    (hs : radicalSquare k X Y = ⊥) : Space k X Y ≃ₗ[k] (X ⟶ Y) := by
  have hd : denominator k X Y = ⊥ := by
    ext f
    simp [denominator, hs]
  exact (Submodule.quotEquivOfEqBot (denominator k X Y) hd).trans
    ((LinearEquiv.ofEq _ _ hr).trans Submodule.topEquiv)

end MagnitudeConjecture.CategoricalIrreducible
