import MagnitudeConjecture.Algebra.StringProjectiveRadicalDecompositionObjects
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition

/-!
# Basic objects for decomposing string projective radicals
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

noncomputable def displayedIncomingArrowEquivFin (y : Q) :
    Fin (Nat.card (DisplayedIncomingArrow y)) ≃ DisplayedIncomingArrow y :=
  (Finite.equivFin (DisplayedIncomingArrow y)).symm

noncomputable def representedVertexRadicalSummand
    (P : StringPresentation k A Q) (y : Q)
    (i : Fin (Nat.card (DisplayedIncomingArrow y))) :
    FGModuleCat P.quotientCategoryAlgebraᵐᵒᵖ :=
  P.incomingArrowRangeFGObj (displayedIncomingArrowEquivFin y i)

end StringPresentation

end MagnitudeConjecture.BoundQuiver
