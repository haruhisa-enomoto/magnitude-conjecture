import MagnitudeConjecture.Algebra.StringOtherIncomingFamily

/-! # The surviving incoming-arrow family of an arrow cokernel -/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- A vector in one incoming-arrow range, inserted in the corresponding
coordinate of the full branch family. -/
def incomingArrowRangeFamilySingle
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y)
    (z : LinearMap.range (P.representedArrowLinearMap a.2)) :
    (∀ b : DisplayedIncomingArrow y,
      LinearMap.range (P.representedArrowLinearMap b.2)) := by
  classical
  exact Pi.single a z

/-- The selected branch inclusion is the corresponding single-coordinate
vector under the radical decomposition. -/
theorem incomingArrowRangeFamilyRadicalLinearEquiv_symm_branchInclusion
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y)
    (z : LinearMap.range (P.representedArrowLinearMap a.2)) :
    (P.incomingArrowRangeFamilyRadicalLinearEquiv y).symm
        (P.arrowBranchRadicalInclusionLinearMap a z) =
      P.incomingArrowRangeFamilySingle a z := by
  apply (P.incomingArrowRangeFamilyRadicalLinearEquiv y).injective
  rw [(P.incomingArrowRangeFamilyRadicalLinearEquiv y).apply_symm_apply]
  rfl

/-- Deleting the selected coordinate and then passing to the arrow cokernel
identifies the remaining branch family with the radical of `V(a)`. -/
def otherIncomingFamilyToCokernelRadical
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    (∀ b : OtherIncomingArrow (Sigma.mk x a),
        LinearMap.range (P.representedArrowLinearMap b.1.2)) →ₗ[
      P.quotientCategoryAlgebraᵐᵒᵖ]
    Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
      (P.arrowCokernelFGObj a) :=
  (P.arrowCokernelRadicalLinearMap a).comp
    ((P.incomingArrowRangeFamilyRadicalLinearEquiv y).toLinearMap.comp
      (P.otherIncomingFamilyInsertion (Sigma.mk x a)))

end MagnitudeConjecture.BoundQuiver.StringPresentation
