import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Scalar endomorphisms imply indecomposability

A nonzero object in a linear category whose endomorphisms are all scalar is
indecomposable.  This is the categorical Schur argument used when transporting
the concrete factor grading across the poset-space equivalence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CategoryTheory

universe s v u

variable {k : Type s} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear k C] [HasBinaryBiproducts C]

/-- A nonzero object with only scalar endomorphisms cannot split as a
biproduct of two nonzero objects. -/
theorem indecomposable_of_endomorphism_eq_smul_id
    (X : C) (hX : ¬ IsZero X)
    (hscalar : ∀ f : X ⟶ X, ∃ c : k, c • 𝟙 X = f) :
    Indecomposable X := by
  refine ⟨hX, ?_⟩
  intro Y Z e
  let p : X ⟶ X :=
    e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv
  obtain ⟨c, hc⟩ := hscalar p
  have hp_idempotent : p ≫ p = p := by
    dsimp only [p]
    simp only [Category.assoc]
    simp
  have hcid : c * c = c := by
    have hzero : (c * c - c) • 𝟙 X = 0 := by
      calc
        (c * c - c) • 𝟙 X =
            (c • 𝟙 X) ≫ (c • 𝟙 X) - c • 𝟙 X := by
          rw [sub_smul, mul_smul]
          simp
        _ = p ≫ p - p := by rw [hc]
        _ = 0 := by rw [hp_idempotent, sub_self]
    have hid : (𝟙 X : X ⟶ X) ≠ 0 := by
      intro h
      exact hX ((IsZero.iff_id_eq_zero X).2 h)
    exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hid)
  have hfactor : c * (c - 1) = 0 := by
    rw [mul_sub, mul_one, hcid, sub_self]
  rcases mul_eq_zero.mp hfactor with hc0 | hc1
  · left
    rw [IsZero.iff_id_eq_zero]
    have hpzero : p = 0 := by
      rw [← hc, hc0, zero_smul]
    have hfst : biprod.fst (X := Y) (Y := Z) = 0 := by
      calc
        biprod.fst = e.inv ≫ p ≫ e.hom ≫ biprod.fst := by
          dsimp only [p]
          simp only [Category.assoc]
          simp
        _ = 0 := by rw [hpzero]; simp
    rw [← biprod.inl_fst, hfst, comp_zero]
  · right
    have hc_one : c = 1 := sub_eq_zero.mp hc1
    rw [IsZero.iff_id_eq_zero]
    have hpone : p = 𝟙 X := by
      rw [← hc, hc_one, one_smul]
    have hinr : biprod.inr (X := Y) (Y := Z) = 0 := by
      calc
        biprod.inr = biprod.inr ≫ e.inv ≫ p ≫ e.hom := by
          rw [hpone]
          simp
        _ = 0 := by
          dsimp only [p]
          simp only [Category.assoc]
          simp
    rw [← biprod.inr_snd, hinr, zero_comp]

end MagnitudeConjecture.CategoryTheory
