import MagnitudeConjecture.Algebra.StringArrowCokernelBranchBasic

/-! # The canonical arrow-cokernel radical section on images -/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- Applying the canonical radical section to the image of a projective-
radical vector discards exactly its selected-arrow coordinate. -/
theorem arrowCokernelRadicalSection_apply_map
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (z : Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y)) :
    P.arrowCokernelRadicalSection a
        (P.arrowCokernelRadicalLinearMap a z) =
      P.arrowRadicalComplementProjection a z := by
  change
    (LinearMap.ker (P.arrowCokernelRadicalLinearMap a)).liftQ
        (P.arrowRadicalComplementProjection a)
        (P.arrowRadicalComplementProjection_ker a)
        (((P.arrowCokernelRadicalLinearMap a).quotKerEquivOfSurjective
          (P.arrowCokernelRadicalMap_surjective a)).symm
            (P.arrowCokernelRadicalLinearMap a z)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rw [Submodule.liftQ_apply]

end MagnitudeConjecture.BoundQuiver.StringPresentation
