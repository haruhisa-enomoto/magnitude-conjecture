import MagnitudeConjecture.Algebra.StringArrowCokernelRadicalComplement
import Mathlib.LinearAlgebra.Projection

/-! # Splitting the radical map of a string-arrow cokernel -/

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

/-- A canonical section of the projective-radical quotient obtained by
discarding the selected arrow coordinate. -/
def arrowCokernelRadicalSection
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.arrowCokernelFGObj a) →ₗ[
      P.quotientCategoryAlgebraᵐᵒᵖ]
      Module.jacobson P.quotientCategoryAlgebraᵐᵒᵖ
        (P.representedVertexModule y) :=
  (LinearMap.ker (P.arrowCokernelRadicalLinearMap a)).liftQ
      (P.arrowRadicalComplementProjection a)
      (P.arrowRadicalComplementProjection_ker a) |>.comp
    ((P.arrowCokernelRadicalLinearMap a).quotKerEquivOfSurjective
      (P.arrowCokernelRadicalMap_surjective a)).symm.toLinearMap

set_option maxHeartbeats 800000 in
@[simp]
theorem arrowCokernelRadicalMap_section
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    (P.arrowCokernelRadicalLinearMap a).comp
        (P.arrowCokernelRadicalSection a) =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ :=
    P.arrowCokernelRadicalMap_surjective a z
  change P.arrowCokernelRadicalLinearMap a
      ((LinearMap.ker
        (P.arrowCokernelRadicalLinearMap a)).liftQ
          (P.arrowRadicalComplementProjection a)
          (P.arrowRadicalComplementProjection_ker a)
          (((P.arrowCokernelRadicalLinearMap a).quotKerEquivOfSurjective
            (P.arrowCokernelRadicalMap_surjective a)).symm
              (P.arrowCokernelRadicalLinearMap a w))) =
    P.arrowCokernelRadicalLinearMap a w
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rw [Submodule.liftQ_apply]
  exact P.arrowRadicalComplementProjection_quotient a w

end MagnitudeConjecture.BoundQuiver.StringPresentation
