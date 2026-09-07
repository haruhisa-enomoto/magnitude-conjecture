import MagnitudeConjecture.Algebra.RightModuleCoherentDefectExtTwo
import MagnitudeConjecture.Algebra.RightModuleCoherentDefectDimensionShiftNaturality

/-!
# Naturality of the coherent-defect Ext² calculation

The presentation-quotient calculation of `Ext²` commutes with
postcomposition in the restricted representable target.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Abelian
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

/-- Naturality of the quotient model for `Ext²` along a skeleton
morphism. -/
theorem finiteContravariantDefectPresentationLinearEquiv_postcomp
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    {X Y : S.IndecCategory} (a : X ⟶ Y)
    (q :
      ((S.finiteContravariantDefectLeftShortComplex K).X₁ ⟶
          S.finiteContravariantRepresentableOnSkeleton.obj X) ⧸
        ProjectivePresentationExt.presentationRange (k := k)
          (S.finiteContravariantDefectLeftShortComplex K)
          (S.finiteContravariantRepresentableOnSkeleton.obj X)) :
    S.finiteContravariantDefectPresentationLinearEquiv hK Y
        (ProjectivePresentationExt.postcompQuotient (k := k)
          (S.finiteContravariantDefectLeftShortComplex K)
          (S.finiteContravariantRepresentableOnSkeleton.map a) q) =
      Ext.postcompOfLinear
        (Ext.mk₀ (S.finiteContravariantRepresentableOnSkeleton.map a)) k
        (S.finiteContravariantDefect K) (add_zero 2)
        (S.finiteContravariantDefectPresentationLinearEquiv hK X q) := by
  letI : Projective
      (S.finiteRestrictedContravariantRepresentable K.X₂) :=
    S.finiteRestrictedContravariantRepresentable_projective K.X₂
  letI : Projective
      (S.finiteContravariantDefectLeftShortComplex K).X₂ := by
    change Projective
      (S.finiteRestrictedContravariantRepresentable K.X₂)
    infer_instance
  let eX := ProjectivePresentationExt.quotientLinearEquivExtOne
    (k := k) (S.finiteContravariantDefectLeftShortComplex_shortExact hK)
    (S.finiteContravariantRepresentableOnSkeleton.obj X)
  let eY := ProjectivePresentationExt.quotientLinearEquivExtOne
    (k := k) (S.finiteContravariantDefectLeftShortComplex_shortExact hK)
    (S.finiteContravariantRepresentableOnSkeleton.obj Y)
  have h₁ := ProjectivePresentationExt.quotientLinearEquivExtOne_postcompQuotient
    (k := k) (S.finiteContravariantDefectLeftShortComplex_shortExact hK)
    (S.finiteContravariantRepresentableOnSkeleton.map a) q
  have h₂ := S.finiteContravariantDefectDimensionShiftLinearEquiv_postcomp
    hK a (eX q)
  change
    S.finiteContravariantDefectDimensionShiftLinearEquiv hK Y
        (eY (ProjectivePresentationExt.postcompQuotient (k := k)
          (S.finiteContravariantDefectLeftShortComplex K)
          (S.finiteContravariantRepresentableOnSkeleton.map a) q)) = _
  rw [h₁]
  exact h₂

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
