import MagnitudeConjecture.CategoryTheory.IrreducibleFromIndecomposableFactors
import Mathlib.CategoryTheory.Linear.Basic

/-! # A linear subspace of factorizations with no reverse maps -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.CategoryTheory
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C] [HasBinaryBiproducts C] [HasFiniteBiproducts C]

/-- Maps factoring through an object with no maps back to the source or from
the target. Finite biproducts make these maps a linear subspace. -/
def noBackwardFactorizations (X Y : C) : Submodule k (X ⟶ Y) where
  carrier := {f | ∃ M : C, ∃ g : X ⟶ M, ∃ h : M ⟶ Y,
    g ≫ h = f ∧ (∀ r : M ⟶ X, r = 0) ∧ (∀ r : Y ⟶ M, r = 0)}
  zero_mem' := by
    refine ⟨0, 0, 0, by simp, ?_, ?_⟩
    · intro r; exact (isZero_zero C).eq_of_src r 0
    · intro r; exact (isZero_zero C).eq_of_tgt r 0
  add_mem' := by
    rintro f f' ⟨M, g, h, hg, hr, hs⟩ ⟨N, g', h', hg', hr', hs'⟩
    refine ⟨M ⊞ N, biprod.lift g g', biprod.desc h h', ?_, ?_, ?_⟩
    · simp only [biprod.lift_desc, hg, hg']
    · intro r
      apply biprod.hom_ext'
      · simpa only [comp_zero] using hr (biprod.inl ≫ r)
      · simpa only [comp_zero] using hr' (biprod.inr ≫ r)
    · intro r
      apply biprod.hom_ext
      · simpa only [zero_comp] using hs (r ≫ biprod.fst)
      · simpa only [zero_comp] using hs' (r ≫ biprod.snd)
  smul_mem' := by
    rintro c f ⟨M, g, h, hg, hr, hs⟩
    exact ⟨M, c • g, h, by rw [Linear.smul_comp, hg], hr, hs⟩

/-- A nonzero map in this subspace has a factorization with neither factor split. -/
theorem not_irreducible_of_noBackwardFactorization {X Y : C} {f : X ⟶ Y}
    (hf : f ≠ 0) (h : f ∈ noBackwardFactorizations (k := k) X Y) :
    ¬ IsIrreducibleMorphism f := by
  obtain ⟨M, a, b, hab, hback, hforward⟩ := h
  have ha : a ≠ 0 := by intro hz; apply hf; rw [← hab, hz, zero_comp]
  have hb : b ≠ 0 := by intro hz; apply hf; rw [← hab, hz, comp_zero]
  intro hi
  rcases hi.factorization a b hab with hs | hs
  · let := hs
    exact retraction_ne_zero_of_ne_zero a ha (hback (retraction a))
  · let := hs
    exact section_ne_zero_of_ne_zero b hb (hforward (section_ b))

end MagnitudeConjecture.CategoryTheory
