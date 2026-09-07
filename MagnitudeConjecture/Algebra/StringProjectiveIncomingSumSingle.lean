import MagnitudeConjecture.Algebra.StringProjectiveIncomingSumBasic

/-!
# Single-coordinate vectors for incoming-arrow sums

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

local instance displayedIncomingArrowDecidableEq (y : Q) :
    DecidableEq (DisplayedIncomingArrow y) := Classical.decEq _

/-- Insert one incoming-arrow range element in its coordinate of the finite
dependent product. -/
def incomingArrowRangeSingle
    (P : StringPresentation k A Q) (y : Q)
    (a : DisplayedIncomingArrow y)
    (g : LinearMap.range (P.representedArrowLinearMap a.2)) :
    ∀ b : DisplayedIncomingArrow y,
      LinearMap.range (P.representedArrowLinearMap b.2) :=
  MagnitudeConjecture.piSingle a g

/-- The incoming-range sum sends a vector supported in one arrow coordinate
to that coordinate's underlying represented morphism. -/
theorem incomingArrowRangeSumKLinearMap_single
    (P : StringPresentation k A Q) (y : Q)
    (a : DisplayedIncomingArrow y)
    (g : LinearMap.range (P.representedArrowLinearMap a.2)) :
    P.incomingArrowRangeSumKLinearMap y
        (P.incomingArrowRangeSingle y a g) = g.1 := by
  classical
  change (∑ b : DisplayedIncomingArrow y,
    ((Pi.single a g : ∀ c : DisplayedIncomingArrow y,
      LinearMap.range (P.representedArrowLinearMap c.2)) b).1) = g.1
  rw [Finset.sum_eq_single a]
  · simp

  · intro b _ hba
    rw [Pi.single_eq_of_ne hba]
    rfl
  · simp

end StringPresentation

end MagnitudeConjecture.BoundQuiver
