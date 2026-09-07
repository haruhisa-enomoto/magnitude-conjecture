import MagnitudeConjecture.Algebra.RightModulePrimitiveArrowIdeal
import MagnitudeConjecture.Algebra.RightModulePrimitiveBasicAlgebra

/-!
# Special-biserial presentations of ambient algebras

The category algebra of covariant representables on selected right
projectives is the opposite ambient algebra.  Combining that calculation
with the ordinary-arrow presentation first gives a special-biserial
presentation of the opposite algebra.  Applying the same construction to
the opposite primitive-projective presentation removes this variance and
gives a presentation of the original ambient algebra.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing A]
variable [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- A biserial primitive-projective presentation gives a literal special-
biserial bound-quiver presentation of the opposite ambient algebra.  This is
the variance-correct form of the category-algebra calculation. -/
theorem ambientOpposite_admitsSpecialBiserialPresentation_of_isBiserial
    (hP : P.IsBiserial) :
    BoundQuiver.AdmitsSpecialBiserialPresentation k Aᵐᵒᵖ := by
  exact
    (BoundQuiver.admitsSpecialBiserialPresentation_iff_of_algEquiv
      P.basicAlgebraAlgEquiv).2
        (P.admitsSpecialBiserialPresentation_of_isBiserial hP)

/-- A complete biserial primitive-projective presentation gives a literal
special-biserial bound-quiver presentation of its ambient algebra.  Apply the
variance-correct category-algebra calculation to the opposite presentation
and then remove the double opposite. -/
theorem ambient_admitsSpecialBiserialPresentation_of_isBiserial
    (hP : P.IsBiserial) :
    BoundQuiver.AdmitsSpecialBiserialPresentation k A := by
  letI : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ := IsNoetherianRing.of_finite k _
  have hop :
      BoundQuiver.AdmitsSpecialBiserialPresentation k (Aᵐᵒᵖ)ᵐᵒᵖ :=
    P.oppositePresentation
      |>.ambientOpposite_admitsSpecialBiserialPresentation_of_isBiserial
        (P.oppositePresentation_isBiserial hP)
  exact
    (BoundQuiver.admitsSpecialBiserialPresentation_iff_of_algEquiv
      (AlgEquiv.opOp k A)).2 hop

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
