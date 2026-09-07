import MagnitudeConjecture.Algebra.StringArrowRightIdeal
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectivePresentation

/-!
# Represented string-arrow maps

This file records the coefficient-field-linear realization of a represented
arrow map and its underlying range.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- The objects of the quotient path category are exactly its displayed
quiver vertices. -/
def quotientObjectEquiv (P : StringPresentation k A Q) :
    Category P.toPresentation.relations ≃ Q where
  toFun X := LinearPathCategory.vertex
    ((CategoryTheory.Quotient.equiv
      (LinearPathCategory.HomogeneousQuotient.relationIdeal
        P.toPresentation.relations).rel) X)
  invFun z := obj P.toPresentation.relations z
  left_inv X := by cases X; rfl
  right_inv z := rfl

@[simp]
theorem quotientObjectEquiv_obj
    (P : StringPresentation k A Q) (z : Q) :
    P.quotientObjectEquiv (obj P.toPresentation.relations z) = z :=
  rfl

@[simp]
theorem quotientObjectEquiv_symm_apply
    (P : StringPresentation k A Q) (z : Q) :
    P.quotientObjectEquiv.symm z = obj P.toPresentation.relations z :=
  rfl

/-- The underlying coefficient-field Hom space of a represented vertex
module. -/
abbrev representedVertexHom
    (P : StringPresentation k A Q) (x : Q) :=
  (CoveringHom.finiteCategoryProjectiveGenerator
      (finiteRepresentablesOfAdmissible P.toPresentation.admissible) ⟶
    P.quotientRepresentable (obj P.toPresentation.relations x))

/-- Postcomposition with the arrow transformation as a coefficient-field
linear map. -/
def representedArrowKLinearMap
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    P.representedVertexHom x →ₗ[k] P.representedVertexHom y where
  toFun f := f ≫ P.arrowRepresentableMap a
  map_add' f g := by simp
  map_smul' r f := by
    simpa only [RingHom.id_apply] using
      (CategoryTheory.Linear.smul_comp _ _ _ r f
        (P.arrowRepresentableMap a))

@[simp]
theorem representedArrowLinearMap_apply
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (f : P.representedVertexModule x) :
    P.representedArrowLinearMap a f = P.representedArrowKLinearMap a f :=
  rfl

instance representedArrowLinearRangeModule
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Module k (LinearMap.range (P.representedArrowLinearMap a)) :=
  Module.restrictScalars k P.quotientCategoryAlgebraᵐᵒᵖ _

instance representedArrowLinearRangeIsScalarTower
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    IsScalarTower k P.quotientCategoryAlgebraᵐᵒᵖ
      (LinearMap.range (P.representedArrowLinearMap a)) :=
  IsScalarTower.restrictScalars k P.quotientCategoryAlgebraᵐᵒᵖ _

end StringPresentation

end MagnitudeConjecture.BoundQuiver
