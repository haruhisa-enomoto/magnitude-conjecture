import MagnitudeConjecture.Algebra.RightModuleCoherentCodefect
import MagnitudeConjecture.CategoryTheory.ProjectiveMiddleDimensionShift

/-! # Dimension shifting for a covariant coherent defect -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable [HasExt.{u} (S.FiniteCovariantFunctor)]

/-- Dimension shifting across the right half of the covariant representable
resolution. -/
def finiteCovariantDefectDimensionShiftLinearEquiv
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategoryᵒᵖ) :
    Ext.{u} (S.finiteCovariantDefectSyzygy K)
        (S.finiteCovariantRepresentableOnSkeleton.obj X) 1 ≃ₗ[k]
      Ext.{u} (S.finiteCovariantDefect K)
        (S.finiteCovariantRepresentableOnSkeleton.obj X) 2 := by
  letI : Projective
      (S.finiteRestrictedCovariantRepresentable K.X₁) :=
    S.finiteRestrictedCovariantRepresentable_projective K.X₁
  letI : Projective
      (S.finiteCovariantDefectRightShortComplex K).X₂ := by
    change Projective
      (S.finiteRestrictedCovariantRepresentable K.X₁)
    infer_instance
  exact MagnitudeConjecture.ProjectiveMiddleDimensionShift.linearEquiv
    (k := k) (S.finiteCovariantDefectRightShortComplex_shortExact hK)
    (S.finiteCovariantRepresentableOnSkeleton.obj X) 0

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
