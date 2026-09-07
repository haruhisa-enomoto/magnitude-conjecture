import MagnitudeConjecture.Algebra.StringArrowCokernelRadicalMap
import MagnitudeConjecture.LinearAlgebra.ComplementProjection

/-! # The complementary projection for a string-arrow cokernel radical -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- Projection of the projective radical away from the selected arrow
branch. -/
def arrowRadicalComplementProjection
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y) →ₗ[
      P.quotientCategoryAlgebraᵐᵒᵖ]
      Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y) :=
  LinearMap.id -
    (P.arrowBranchRadicalInclusionLinearMap (Sigma.mk x a)).comp
      (P.arrowBranchRadicalProjectionLinearMap (Sigma.mk x a))

theorem arrowRadicalComplementProjection_quotient
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y)
    (z : Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
      (P.representedVertexModule y)) :
    P.arrowCokernelRadicalLinearMap a
        (P.arrowRadicalComplementProjection a z) =
      P.arrowCokernelRadicalLinearMap a z := by
  have hker : LinearMap.ker (P.arrowCokernelRadicalLinearMap a) =
      LinearMap.range
        (P.arrowBranchRadicalInclusionLinearMap (Sigma.mk x a)) :=
    P.arrowCokernelRadicalMap_ker a
  exact MagnitudeConjecture.linearMap_sub_comp_apply_eq
    (P.arrowCokernelRadicalLinearMap a)
    (P.arrowBranchRadicalInclusionLinearMap (Sigma.mk x a))
    (P.arrowBranchRadicalProjectionLinearMap (Sigma.mk x a)) hker z

end MagnitudeConjecture.BoundQuiver.StringPresentation
