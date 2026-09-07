import MagnitudeConjecture.Algebra.StringArrowCokernelIrreducible
import MagnitudeConjecture.Algebra.StringEndpointDeterminism
import MagnitudeConjecture.LinearAlgebra.PiInsertZero

/-! # Families on the complement of an incoming arrow -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.BoundQuiver

universe u

variable {k A Q : Type u} [Field k] [Ring A] [Algebra k A]
variable [Fintype Q] [Quiver.{u} Q]
variable [∀ x y : Q, Fintype (x ⟶ y)]

namespace StringPresentation

/-- Incoming displayed arrows other than a fixed marked arrow. -/
abbrev OtherIncomingArrow {y : Q} (a : DisplayedIncomingArrow y) :=
  {b : DisplayedIncomingArrow y // b ≠ a}

/-- At a special-biserial vertex, deleting one marked incoming arrow leaves
at most one incoming arrow. -/
theorem otherIncomingArrow_subsingleton
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y) :
    Subsingleton (OtherIncomingArrow a) := by
  constructor
  intro b c
  apply Subtype.ext
  exact StringWord.Word.eq_of_ne_of_ne_of_natCard_le_two
    a b.1 c.1 b.2 c.2
    (P.toSpecialBiserialPresentation.arrows_ending_le_two y)

/-- Extend the incoming-arrow family by zero on the marked branch. -/
def otherIncomingFamilyInsertion
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y) :
    (∀ b : OtherIncomingArrow a, P.incomingArrowRangeFGObj b.1) →ₗ[
      P.quotientCategoryAlgebraᵐᵒᵖ]
    (∀ b : DisplayedIncomingArrow y, P.incomingArrowRangeFGObj b) :=
  LinearMap.insertZeroCoordinate P.quotientCategoryAlgebraᵐᵒᵖ
    (fun b ↦ P.incomingArrowRangeFGObj b) a

@[simp]
theorem otherIncomingFamilyInsertion_apply_self
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y)
    (g : ∀ b : OtherIncomingArrow a, P.incomingArrowRangeFGObj b.1) :
    P.otherIncomingFamilyInsertion a g a = 0 :=
  LinearMap.insertZeroCoordinate_self P.quotientCategoryAlgebraᵐᵒᵖ
    (fun b ↦ P.incomingArrowRangeFGObj b) a g

@[simp]
theorem otherIncomingFamilyInsertion_apply_other
    (P : StringPresentation k A Q) {y : Q}
    (a : DisplayedIncomingArrow y)
    (g : ∀ b : OtherIncomingArrow a, P.incomingArrowRangeFGObj b.1)
    (b : OtherIncomingArrow a) :
    P.otherIncomingFamilyInsertion a g b.1 = g b :=
  LinearMap.insertZeroCoordinate_other P.quotientCategoryAlgebraᵐᵒᵖ
    (fun b ↦ P.incomingArrowRangeFGObj b) a g b


end StringPresentation
end MagnitudeConjecture.BoundQuiver
