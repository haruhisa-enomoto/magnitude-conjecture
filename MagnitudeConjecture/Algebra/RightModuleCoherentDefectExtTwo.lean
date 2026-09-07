import MagnitudeConjecture.Algebra.RightModuleCoherentDefectDimensionShift

/-!
# The degree-two Ext calculation for a coherent defect

The two short exact halves of the representable resolution identify the
intrinsic degree-two Ext group with the quotient computed from the left
representable presentation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable [HasExt.{u} (FG (A := A))]
variable [HasExt.{u} (S.FiniteContravariantFunctor)]

/-- The two short exact halves compute the intrinsic degree-two Ext group as
the quotient attached to the left representable presentation. -/
def finiteContravariantDefectPresentationLinearEquiv
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) :
    (((S.finiteContravariantDefectLeftShortComplex K).X₁ ⟶
          S.finiteContravariantRepresentableOnSkeleton.obj X) ⧸
        ProjectivePresentationExt.presentationRange (k := k)
          (S.finiteContravariantDefectLeftShortComplex K)
          (S.finiteContravariantRepresentableOnSkeleton.obj X)) ≃ₗ[k]
      Ext.{u} (S.finiteContravariantDefect K)
        (S.finiteContravariantRepresentableOnSkeleton.obj X) 2 := by
  letI : Projective
      (S.finiteRestrictedContravariantRepresentable K.X₂) :=
    S.finiteRestrictedContravariantRepresentable_projective K.X₂
  letI : Projective
      (S.finiteContravariantDefectLeftShortComplex K).X₂ := by
    change Projective
      (S.finiteRestrictedContravariantRepresentable K.X₂)
    infer_instance
  exact
    (ProjectivePresentationExt.quotientLinearEquivExtOne
      (k := k) (S.finiteContravariantDefectLeftShortComplex_shortExact hK)
      (S.finiteContravariantRepresentableOnSkeleton.obj X)).trans
        (S.finiteContravariantDefectDimensionShiftLinearEquiv hK X)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
