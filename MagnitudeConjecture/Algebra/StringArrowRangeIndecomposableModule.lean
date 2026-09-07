import MagnitudeConjecture.Algebra.StringProjectiveRadicalDecompositionObjects

/-!
# Module-theoretic indecomposability of represented string-arrow ranges
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.BoundQuiver.StringPresentation

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

/-- A nonzero uniserial represented arrow range is indecomposable as a
module. -/
theorem representedArrowLinearRange_isIndecomposableModule
    (P : StringPresentation k A Q) {x y : Q} (a : x ⟶ y) :
    Foundation.IsIndecomposableModule P.quotientCategoryAlgebraᵐᵒᵖ
      (LinearMap.range (P.representedArrowLinearMap a)) := by
  letI : Nontrivial
      (LinearMap.range (P.representedArrowLinearMap a)) :=
    P.representedArrowLinearRange_nontrivial a
  exact (P.representedArrowLinearRange_isUniserial a)
    |>.isIndecomposableModule

end MagnitudeConjecture.BoundQuiver.StringPresentation
