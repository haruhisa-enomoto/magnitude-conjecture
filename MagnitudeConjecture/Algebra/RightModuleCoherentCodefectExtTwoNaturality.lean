import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectExtTwo
import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectDimensionShiftNaturality

/-! # Naturality of the reverse coherent-defect Ext² calculation -/

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
variable [HasExt.{u} (S.FiniteCovariantFunctor)]

/-- Naturality of the reverse quotient model for `Ext²`. -/
theorem finiteCovariantDefectPresentationLinearEquiv_postcomp
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    {X Y : S.IndecCategoryᵒᵖ} (a : X ⟶ Y)
    (q :
      ((S.finiteCovariantDefectLeftShortComplex K).X₁ ⟶
          S.finiteCovariantRepresentableOnSkeleton.obj X) ⧸
        ProjectivePresentationExt.presentationRange (k := k)
          (S.finiteCovariantDefectLeftShortComplex K)
          (S.finiteCovariantRepresentableOnSkeleton.obj X)) :
    S.finiteCovariantDefectPresentationLinearEquiv hK Y
        (ProjectivePresentationExt.postcompQuotient (k := k)
          (S.finiteCovariantDefectLeftShortComplex K)
          (S.finiteCovariantRepresentableOnSkeleton.map a) q) =
      Ext.postcompOfLinear
        (Ext.mk₀ (S.finiteCovariantRepresentableOnSkeleton.map a)) k
        (S.finiteCovariantDefect K) (add_zero 2)
        (S.finiteCovariantDefectPresentationLinearEquiv hK X q) := by
  letI : Projective
      (S.finiteRestrictedCovariantRepresentable K.X₂) :=
    S.finiteRestrictedCovariantRepresentable_projective K.X₂
  letI : Projective
      (S.finiteCovariantDefectLeftShortComplex K).X₂ := by
    change Projective
      (S.finiteRestrictedCovariantRepresentable K.X₂)
    infer_instance
  let eX := ProjectivePresentationExt.quotientLinearEquivExtOne
    (k := k) (S.finiteCovariantDefectLeftShortComplex_shortExact hK)
    (S.finiteCovariantRepresentableOnSkeleton.obj X)
  let eY := ProjectivePresentationExt.quotientLinearEquivExtOne
    (k := k) (S.finiteCovariantDefectLeftShortComplex_shortExact hK)
    (S.finiteCovariantRepresentableOnSkeleton.obj Y)
  have h₁ := ProjectivePresentationExt.quotientLinearEquivExtOne_postcompQuotient
    (k := k) (S.finiteCovariantDefectLeftShortComplex_shortExact hK)
    (S.finiteCovariantRepresentableOnSkeleton.map a) q
  have h₂ := S.finiteCovariantDefectDimensionShiftLinearEquiv_postcomp
    hK a (eX q)
  change
    S.finiteCovariantDefectDimensionShiftLinearEquiv hK Y
        (eY (ProjectivePresentationExt.postcompQuotient (k := k)
          (S.finiteCovariantDefectLeftShortComplex K)
          (S.finiteCovariantRepresentableOnSkeleton.map a) q)) = _
  rw [h₁]
  exact h₂

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
