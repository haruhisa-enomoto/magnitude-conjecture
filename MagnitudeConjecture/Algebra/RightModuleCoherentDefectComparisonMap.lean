import MagnitudeConjecture.Algebra.RightModuleCoherentDefectExtTwoNaturality
import MagnitudeConjecture.Algebra.RightModuleCoherentDefectYonedaQuotient

/-!
# The comparison from a covariant defect to the coherent dual

For a short exact presentation `K`, a map `K.X₁ → X` determines a map
from the first representable in the four-term resolution to `Hom(-, X)`.
Its presentation class and the degree-two Ext calculation define the
canonical natural map from the covariant defect to Auslander's coherent
dual.
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

/-- The comparison before quotienting the covariant representable. -/
def finiteCovariantRepresentableToCoherentDualLinear
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) :
    (K.X₁.obj ⟶ (S.fgObj X).obj) →ₗ[k]
      Ext.{u} (S.finiteContravariantDefect K)
        (S.finiteContravariantRepresentableOnSkeleton.obj X) 2 :=
  (S.finiteContravariantDefectPresentationLinearEquiv hK X).toLinearMap.comp
    ((ProjectivePresentationExt.presentationRange (k := k)
      (S.finiteContravariantDefectLeftShortComplex K)
      (S.finiteContravariantRepresentableOnSkeleton.obj X)).mkQ.comp
        (S.ambientFiniteRestrictedContravariantRepresentableHomLinearEquiv
          K.X₁ X).toLinearMap)

@[simp]
theorem finiteCovariantRepresentableToCoherentDualLinear_apply
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) (f : K.X₁.obj ⟶ (S.fgObj X).obj) :
    S.finiteCovariantRepresentableToCoherentDualLinear hK X f =
      S.finiteContravariantDefectPresentationLinearEquiv hK X
        (Submodule.Quotient.mk
          (S.finiteRestrictedContravariantRepresentableMap
            (ObjectProperty.homMk f))) :=
  rfl

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
