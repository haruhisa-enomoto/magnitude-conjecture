import MagnitudeConjecture.Algebra.RightModuleSupportQuotient
import MagnitudeConjecture.Algebra.BiserialRadicalTop
import MagnitudeConjecture.CategoryTheory.BiserialObject

/-!
# Biserial primitive-projective presentations

A finite-dimensional algebra is biserial when the principal right and left
ideals belonging to a complete family of primitive orthogonal idempotents are
biserial modules.  This file records that condition on the literal
primitive-projective presentations used by the support-quotient construction.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

namespace PrimitiveProjectivePresentation

/-- A complete primitive-projective presentation is biserial when every
associated principal right ideal `eA` and principal left ideal `Ae` is a
biserial object. -/
def IsBiserial (P : S.PrimitiveProjectivePresentation) : Prop :=
  (∀ p, IsBiserialObject (RightModule.rightIdealFGObj (P.idempotent p))) ∧
    (∀ p, IsBiserialObject
      (RightModule.leftIdealFGObj (k := k) (P.idempotent p)))

/-- Biseriality of a primitive-projective presentation bounds the first
radical layer of every associated principal right ideal by two. -/
theorem IsBiserial.rightIdeal_top_jacobson_length_le_two
    {P : S.PrimitiveProjectivePresentation} (hP : P.IsBiserial)
    (p : S.ProjectiveLabel) :
    Module.length Aᵐᵒᵖ
      (Module.jacobson Aᵐᵒᵖ (RightModule.rightIdealFGObj (P.idempotent p)) ⧸
        Module.jacobson Aᵐᵒᵖ
          (Module.jacobson Aᵐᵒᵖ
            (RightModule.rightIdealFGObj (P.idempotent p)))) ≤ 2 := by
  letI : IsArtinianRing Aᵐᵒᵖ := IsArtinianRing.of_finite k Aᵐᵒᵖ
  apply top_jacobson_length_le_two_of_biserial
  exact IsBiserialObject.toIsBiserialModule_of_fg _ (hP.1 p)

/-- Biseriality of a primitive-projective presentation bounds the first
radical layer of every associated principal left ideal by two. -/
theorem IsBiserial.leftIdeal_top_jacobson_length_le_two
    {P : S.PrimitiveProjectivePresentation} (hP : P.IsBiserial)
    (p : S.ProjectiveLabel) :
    Module.length A
      (Module.jacobson A (RightModule.leftIdealFGObj (k := k) (P.idempotent p)) ⧸
        Module.jacobson A
          (Module.jacobson A
            (RightModule.leftIdealFGObj (k := k) (P.idempotent p)))) ≤ 2 := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite k A
  apply top_jacobson_length_le_two_of_biserial
  exact IsBiserialObject.toIsBiserialModule_of_fg _ (hP.2 p)

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
