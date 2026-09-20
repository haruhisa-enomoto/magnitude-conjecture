import MagnitudeConjecture.CategoryTheory.CategoricalIrreducibleSpace
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Bounding total incoming irreducible dimension -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped BigOperators
namespace MagnitudeConjecture.CategoricalIrreducible
universe u v w z
variable (k : Type u) [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- A zero Hom space has zero intrinsic irreducible dimension. -/
theorem finrank_eq_zero_of_hom_eq_zero (X Y : C) (h : ∀ f : X ⟶ Y, f = 0) :
    Module.finrank k (Space k X Y) = 0 := by
  letI : Subsingleton (X ⟶ Y) := ⟨fun f g ↦ (h f).trans (h g).symm⟩
  letI : Subsingleton (radical k X Y) := inferInstance
  letI : Subsingleton (Space k X Y) := inferInstance
  exact Module.finrank_zero_of_subsingleton

/-- A uniform quotient bound only needs to be counted over sources with a
nonzero incoming morphism. -/
theorem sum_finrank_le_incoming_card_mul {ι : Type z} [Fintype ι]
    (F : ι → C) (Y : C) (D : ℕ)
    (hD : ∀ i, Module.finrank k (Space k (F i) Y) ≤ D) :
    (∑ i, Module.finrank k (Space k (F i) Y)) ≤
      Nat.card {i : ι // ∃ f : F i ⟶ Y, f ≠ 0} * D := by
  classical
  calc
    (∑ i, Module.finrank k (Space k (F i) Y)) ≤
        ∑ i, if ∃ f : F i ⟶ Y, f ≠ 0 then D else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact hD i
      · have hz : ∀ f : F i ⟶ Y, f = 0 := by
          intro f
          by_contra hf
          exact hi ⟨f, hf⟩
        rw [finrank_eq_zero_of_hom_eq_zero k (F i) Y hz]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

end MagnitudeConjecture.CategoricalIrreducible
