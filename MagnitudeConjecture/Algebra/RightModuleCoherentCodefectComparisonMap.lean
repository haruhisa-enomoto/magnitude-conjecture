import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectExtTwoNaturality
import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectCoyonedaQuotient

/-! # The comparison from a contravariant defect to the coherent codual -/

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

/-- The reverse comparison before quotienting the contravariant representable. -/
def finiteContravariantRepresentableToCoherentCodualLinear
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) :
    ((S.fgObj X).obj ⟶ K.X₃.obj) →ₗ[k]
      Ext.{u} (S.finiteCovariantDefect K)
        (S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X)) 2 :=
  (S.finiteCovariantDefectPresentationLinearEquiv hK
      (Opposite.op X)).toLinearMap.comp
    ((ProjectivePresentationExt.presentationRange (k := k)
      (S.finiteCovariantDefectLeftShortComplex K)
      (S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X))).mkQ.comp
        (S.ambientFiniteRestrictedCovariantRepresentableHomLinearEquiv
          K.X₃ X).toLinearMap)

@[simp]
theorem finiteContravariantRepresentableToCoherentCodualLinear_apply
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) (f : (S.fgObj X).obj ⟶ K.X₃.obj) :
    S.finiteContravariantRepresentableToCoherentCodualLinear hK X f =
      S.finiteCovariantDefectPresentationLinearEquiv hK (Opposite.op X)
        (Submodule.Quotient.mk
          (S.finiteRestrictedCovariantRepresentableMap
            (ObjectProperty.homMk f))) :=
  rfl

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
