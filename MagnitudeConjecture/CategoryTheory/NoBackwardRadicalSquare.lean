import MagnitudeConjecture.CategoryTheory.NoBackwardFactorization
import MagnitudeConjecture.CategoryTheory.CategoricalIrreducibleSpace

/-! # No-reverse-map factorizations lie in the radical square -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution.CategoricalIdeal
open QuotientSubmoduleEquidistribution.CategoricalRadical
namespace MagnitudeConjecture.CategoryTheory
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C] [HasBinaryBiproducts C] [HasFiniteBiproducts C]

/-- Absence of reverse maps forces both factors into the categorical radical. -/
theorem noBackwardFactorizations_le_radicalSquare (X Y : C) :
    noBackwardFactorizations (k := k) X Y ≤ CategoricalIrreducible.radicalSquare k X Y := by
  rintro f ⟨M, a, b, rfl, ha, hb⟩
  apply HomIdeal.comp_mem_mul
  · change IsRadicalMorphism a
    intro r
    rw [ha r, comp_zero, sub_zero]
    infer_instance
  · change IsRadicalMorphism b
    intro r
    rw [hb r, comp_zero, sub_zero]
    infer_instance

end MagnitudeConjecture.CategoryTheory
