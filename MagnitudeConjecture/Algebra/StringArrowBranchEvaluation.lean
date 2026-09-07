import MagnitudeConjecture.Algebra.StringArrowBranchMaps

/-! # Underlying functions of the radical and branch inclusions -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
  [Fintype Q] [Quiver.{u} Q] [∀ x y : Q, Fintype (x ⟶ y)]

theorem representedVertexRadicalInclusion_apply
    (P : StringPresentation k A Q) (y : Q)
    (z : P.representedVertexRadicalFGObj y) :
    (P.representedVertexRadicalInclusion y).hom.hom z = z.1 := rfl

theorem arrowBranchRadicalInclusion_apply_coe
    (P : StringPresentation k A Q) {y : Q} (a : DisplayedIncomingArrow y)
    (z : P.incomingArrowRangeFGObj a) :
    ((P.arrowBranchRadicalInclusion a).hom.hom z).1 = z.1 := by
  classical
  exact P.incomingArrowRangeFamilyRadicalLinearEquiv_single_coe a z

theorem arrowBranchRadicalInclusionLinearMap_apply_coe
    (P : StringPresentation k A Q) {y : Q} (a : DisplayedIncomingArrow y)
    (z : LinearMap.range (P.representedArrowLinearMap a.2)) :
    (P.arrowBranchRadicalInclusionLinearMap a z).1 = z.1 := by
  classical
  exact P.incomingArrowRangeFamilyRadicalLinearEquiv_single_coe a z

end MagnitudeConjecture.BoundQuiver.StringPresentation
