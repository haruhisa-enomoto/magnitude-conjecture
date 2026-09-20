import MagnitudeConjecture.CategoryTheory.IncomingDecompositionIdeal
import MagnitudeConjecture.CategoryTheory.HomIdealComap
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Local comparison of ideal products with a full subcategory -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open scoped BigOperators
namespace MagnitudeConjecture
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasBinaryBiproducts C] [HasFiniteBiproducts C]
variable (P : ObjectProperty C)

/-- Bundle an ambient map between two objects of a full subcategory. -/
def fullSubcategoryHomAddEquiv (X Y : P.FullSubcategory) :
    (X.obj ⟶ Y.obj) ≃+ (X ⟶ Y) where
  toFun f := ⟨f⟩
  invFun f := f.hom
  left_inv _ := rfl
  right_inv f := by cases f; rfl
  map_add' _ _ := rfl

/-- At a target whose nonzero incoming indecomposables lie in the full
subcategory, multiplication of categorical ideals commutes with restriction. -/
theorem homIdealProduct_fullSubcategory_iff
    (hdec : ∀ M : C, Nonempty (CategoryTheory.FiniteIndecomposableDecomposition M))
    (I J : HomIdeal C) (X Y : P.FullSubcategory)
    (hY : ∀ Z : C, Indecomposable Z → ∀ b : Z ⟶ Y.obj, b ≠ 0 → P Z)
    (f : X ⟶ Y) :
    f.hom ∈ (I ⋆ᵢ J).hom X.obj Y.obj ↔
      f ∈ ((I.comap P.ι) ⋆ᵢ (J.comap P.ι)).hom X Y := by
  classical
  let K := ((I.comap P.ι) ⋆ᵢ (J.comap P.ι)).hom X Y
  let E := fullSubcategoryHomAddEquiv P X Y
  constructor
  · intro hf
    have hle : (I ⋆ᵢ J).hom X.obj Y.obj ≤ K.comap E.toAddMonoidHom := by
      apply (AddSubgroup.closure_le _).2
      rintro g ⟨M, a, b, ha, hb, rfl⟩
      obtain ⟨d⟩ := hdec M
      letI : Fintype (d.IncomingIndex b) := Fintype.ofFinite _
      change E (a ≫ b) ∈ K
      rw [d.comp_eq_sum_incoming a b, map_sum]
      apply K.sum_mem
      intro q _
      have hq := d.incoming_summand_property P hY b q
      let Z : P.FullSubcategory := ⟨d.summand q.val, hq⟩
      let a' : X ⟶ Z := ⟨d.outgoingComponent a q.val⟩
      let b' : Z ⟶ Y := ⟨d.incomingComponent b q.val⟩
      change a' ≫ b' ∈ K
      exact HomIdeal.comp_mem_mul
        (d.outgoingComponent_mem I a ha q.val)
        (d.incomingComponent_mem J b hb q.val)
    exact hle hf
  · intro hf
    induction hf using AddSubgroup.closure_induction with
    | mem g hg =>
      obtain ⟨Z, a, b, ha, hb, rfl⟩ := hg
      exact HomIdeal.comp_mem_mul ha hb
    | zero => exact zero_mem _
    | add g h _ _ hg hh => exact add_mem hg hh
    | neg g _ hg => exact neg_mem hg

end MagnitudeConjecture
