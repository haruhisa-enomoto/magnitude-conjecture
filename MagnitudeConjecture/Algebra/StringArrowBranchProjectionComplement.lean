import MagnitudeConjecture.Algebra.StringArrowCokernelBranchBasic
import MagnitudeConjecture.LinearAlgebra.ComplementProjection

/-! # The selected coordinate of the branch complement -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

set_option maxHeartbeats 1000000 in
/-- Projection away from a branch has zero coordinate on that branch. -/
theorem arrowBranchRadicalProjection_complement
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (z : Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y)) :
    P.arrowBranchRadicalProjectionLinearMap (Sigma.mk x a)
        (P.arrowRadicalComplementProjection a z) = 0 := by
  exact MagnitudeConjecture.linearMap_projection_sub_comp_apply_eq_zero
    (P.arrowBranchRadicalInclusionLinearMap (Sigma.mk x a))
    (P.arrowBranchRadicalProjectionLinearMap (Sigma.mk x a))
    (P.arrowBranchRadicalInclusion_projection (Sigma.mk x a)) z

end MagnitudeConjecture.BoundQuiver.StringPresentation
