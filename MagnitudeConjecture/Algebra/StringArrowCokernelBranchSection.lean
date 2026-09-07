import MagnitudeConjecture.Algebra.StringArrowCokernelBranchSectionApply
import MagnitudeConjecture.Algebra.StringArrowBranchProjectionComplement

/-! # The selected coordinate of the arrow-cokernel radical section -/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

set_option maxHeartbeats 1000000 in
/-- The canonical radical section has zero selected-arrow coordinate. -/
theorem arrowCokernelRadicalSection_selectedCoordinate
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (z : Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
      (P.arrowCokernelFGObj a)) :
    (P.incomingArrowRangeFamilyRadicalLinearEquiv y).symm
        (P.arrowCokernelRadicalSection a z) (Sigma.mk x a) = 0 := by
  obtain ⟨w, rfl⟩ := P.arrowCokernelRadicalMap_surjective a z
  rw [P.arrowCokernelRadicalSection_apply_map a w]
  change P.arrowBranchRadicalProjectionLinearMap (Sigma.mk x a)
      (P.arrowRadicalComplementProjection a w) = 0
  exact P.arrowBranchRadicalProjection_complement a w

end MagnitudeConjecture.BoundQuiver.StringPresentation
