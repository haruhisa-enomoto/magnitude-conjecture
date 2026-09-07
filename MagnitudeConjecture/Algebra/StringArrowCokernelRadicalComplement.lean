import MagnitudeConjecture.Algebra.StringArrowCokernelRadicalComplementBasic

/-! # The kernel killed by the arrow-radical complementary projection -/

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

theorem arrowRadicalComplementProjection_ker
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    LinearMap.ker (P.arrowCokernelRadicalLinearMap a) ≤
      LinearMap.ker (P.arrowRadicalComplementProjection a) := by
  exact MagnitudeConjecture.linearMap_ker_le_ker_sub_comp
    (P.arrowCokernelRadicalLinearMap a)
    (P.arrowBranchRadicalInclusionLinearMap (Sigma.mk x a))
    (P.arrowBranchRadicalProjectionLinearMap (Sigma.mk x a))
    (P.arrowCokernelRadicalMap_ker a)
    (P.arrowBranchRadicalInclusion_projection (Sigma.mk x a))

end MagnitudeConjecture.BoundQuiver.StringPresentation
