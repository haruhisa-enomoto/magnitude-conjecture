import MagnitudeConjecture.Algebra.RightModuleCoherentDuality
import MagnitudeConjecture.CategoryTheory.ProjectiveMiddleDimensionShift

/-!
# Dimension shifting for a coherent defect

This leaf specializes the generic projective-middle dimension shift to the
right half of the four-term representable resolution of a coherent defect.
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

/-- Dimension shifting across the right half of the four-term
representable resolution. -/
def finiteContravariantDefectDimensionShiftLinearEquiv
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) :
    Ext.{u} (S.finiteContravariantDefectSyzygy K)
        (S.finiteContravariantRepresentableOnSkeleton.obj X) 1 ≃ₗ[k]
      Ext.{u} (S.finiteContravariantDefect K)
        (S.finiteContravariantRepresentableOnSkeleton.obj X) 2 := by
  letI : Projective
      (S.finiteRestrictedContravariantRepresentable K.X₃) :=
    S.finiteRestrictedContravariantRepresentable_projective K.X₃
  letI : Projective
      (S.finiteContravariantDefectRightShortComplex K).X₂ := by
    change Projective
      (S.finiteRestrictedContravariantRepresentable K.X₃)
    infer_instance
  exact MagnitudeConjecture.ProjectiveMiddleDimensionShift.linearEquiv
    (k := k) (S.finiteContravariantDefectRightShortComplex_shortExact hK)
    (S.finiteContravariantRepresentableOnSkeleton.obj X) 0

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
