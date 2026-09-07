import MagnitudeConjecture.Algebra.StringArrowCokernelClassification
import MagnitudeConjecture.LinearAlgebra.SubmodulePiSum

/-! # Evaluating an arrow-branch coordinate in the projective radical -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
  [Fintype Q] [Quiver.{u} Q] [∀ x y : Q, Fintype (x ⟶ y)]

/-- The radical decomposition includes a single arrow coordinate by its
ambient submodule inclusion. -/
theorem incomingArrowRangeFamilyRadicalLinearEquiv_single_coe
    (P : StringPresentation k A Q) {y : Q} [DecidableEq (DisplayedIncomingArrow y)]
    (a : DisplayedIncomingArrow y)
    (z : LinearMap.range (P.representedArrowLinearMap a.2)) :
    ((P.incomingArrowRangeFamilyRadicalLinearEquiv y)
      ((LinearMap.single P.quotientCategoryAlgebraᵐᵒᵖ
        (fun b : DisplayedIncomingArrow y ↦
          LinearMap.range (P.representedArrowLinearMap b.2)) a) z)).1 = z.1 := by
  classical
  change (∑ b : DisplayedIncomingArrow y,
    (((Pi.single a z : ∀ b : DisplayedIncomingArrow y,
      LinearMap.range (P.representedArrowLinearMap b.2)) b).1)) = z.1
  exact Submodule.sum_coe_single
    (fun b : DisplayedIncomingArrow y ↦
      LinearMap.range (P.representedArrowLinearMap b.2)) a z

end MagnitudeConjecture.BoundQuiver.StringPresentation
