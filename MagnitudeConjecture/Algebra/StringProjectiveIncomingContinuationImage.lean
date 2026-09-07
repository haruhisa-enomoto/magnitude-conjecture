import MagnitudeConjecture.Algebra.StringProjectiveIncomingSumSingle
import MagnitudeConjecture.Algebra.StringProjectiveIncomingPathComposite

/-!
# The image of one incoming-arrow continuation vector
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- The incoming-range sum sends the basis continuation in one arrow
coordinate to the represented path obtained by adjoining that arrow. -/
theorem incomingArrowRangeSumKLinearMap_singleBasis
    (P : StringPresentation k A Q) (y : Q)
    (a : DisplayedIncomingArrow y)
    (p : P.toSpecialBiserialPresentation.LeftContinuationPath a.2) :
    P.incomingArrowRangeSumKLinearMap y
        (P.incomingArrowRangeSingle y a
          (P.incomingArrowModuleBasisFamily y a p)) =
      P.representedPathElement y
        (P.incomingContinuationEquivPositiveVertexPath y ⟨a, p⟩).1 := by
  rw [P.incomingArrowRangeSumKLinearMap_single]
  change (P.representedArrowModuleBasis a.2 p).1 = _
  have hb : (P.representedArrowModuleBasis a.2 p).1 =
      (P.representedContinuationElement a.2 p).1 :=
    congrArg Subtype.val (P.representedArrowModuleBasis_apply a.2 p)
  apply hb.trans
  change
    biproduct.π P.quotientRepresentable
          (obj P.toPresentation.relations p.1.1) ≫
        P.pathRepresentableMap p.1.2 ≫ P.arrowRepresentableMap a.2 =
      biproduct.π P.quotientRepresentable
          (obj P.toPresentation.relations p.1.1) ≫
        P.pathRepresentableMap (p.1.2.cons a.2)
  exact P.biproductProjection_pathRepresentableMap_comp_arrow p.1.2 a.2

end MagnitudeConjecture.BoundQuiver.StringPresentation
