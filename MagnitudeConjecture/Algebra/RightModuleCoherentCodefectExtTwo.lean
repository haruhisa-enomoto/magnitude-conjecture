import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectDimensionShift

/-! # The degree-two Ext calculation for a covariant coherent defect -/

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
variable [HasExt.{u} (S.FiniteCovariantFunctor)]

/-- The two short exact halves compute reverse coherent duality as the
quotient attached to the left covariant-representable presentation. -/
def finiteCovariantDefectPresentationLinearEquiv
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategoryᵒᵖ) :
    (((S.finiteCovariantDefectLeftShortComplex K).X₁ ⟶
          S.finiteCovariantRepresentableOnSkeleton.obj X) ⧸
        ProjectivePresentationExt.presentationRange (k := k)
          (S.finiteCovariantDefectLeftShortComplex K)
          (S.finiteCovariantRepresentableOnSkeleton.obj X)) ≃ₗ[k]
      Ext.{u} (S.finiteCovariantDefect K)
        (S.finiteCovariantRepresentableOnSkeleton.obj X) 2 := by
  letI : Projective
      (S.finiteRestrictedCovariantRepresentable K.X₂) :=
    S.finiteRestrictedCovariantRepresentable_projective K.X₂
  letI : Projective
      (S.finiteCovariantDefectLeftShortComplex K).X₂ := by
    change Projective
      (S.finiteRestrictedCovariantRepresentable K.X₂)
    infer_instance
  exact
    (ProjectivePresentationExt.quotientLinearEquivExtOne
      (k := k) (S.finiteCovariantDefectLeftShortComplex_shortExact hK)
      (S.finiteCovariantRepresentableOnSkeleton.obj X)).trans
        (S.finiteCovariantDefectDimensionShiftLinearEquiv hK X)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
