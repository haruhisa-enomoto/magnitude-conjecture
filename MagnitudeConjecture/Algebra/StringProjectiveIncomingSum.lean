import MagnitudeConjecture.Algebra.StringProjectiveIncomingSumImage

/-!
# Incoming-arrow sums in represented string projectives

The explicit path-basis calculation proves that the sum of the incoming-arrow
ranges is internal.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- The represented incoming-arrow ranges form an internal direct sum. -/
theorem incomingArrowRangeSumLinearMap_injective
    (P : StringPresentation k A Q) (y : Q) :
    Function.Injective (P.incomingArrowRangeSumLinearMap y) := by
  classical
  change Function.Injective (P.incomingArrowRangeSumKLinearMap y)
  let b := P.incomingArrowRangePositiveBasis y
  apply LinearMap.injective_of_linearIndependent
    b.span_eq
  have hli := (P.representedVertexExplicitPathBasis y).linearIndependent.comp
    (fun q : P.PositiveVertexPath y ↦ q.1)
    (by
      intro q r hqr
      exact Subtype.ext hqr)
  change LinearIndependent k (fun q : P.PositiveVertexPath y ↦
    P.representedVertexExplicitPathBasis y q.1) at hli
  change LinearIndependent k (fun q : P.PositiveVertexPath y ↦
    P.incomingArrowRangeSumKLinearMap y
      (b q))
  have hfamily :
      (fun q : P.PositiveVertexPath y ↦
        P.incomingArrowRangeSumKLinearMap y (b q)) =
      (fun q ↦ P.representedVertexExplicitPathBasis y q.1) := by
    funext q
    exact P.incomingArrowRangeSumKLinearMap_positiveBasis y q
  rw [hfamily]
  exact hli

end StringPresentation

end MagnitudeConjecture.BoundQuiver
