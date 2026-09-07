import MagnitudeConjecture.Algebra.RightModuleCoherentDefectComparisonDescent

/-!
# The quotient equivalence underlying the coherent-defect comparison
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

/-- The ambient module-presentation quotient is canonically the degree-two
Ext group defining the coherent dual. -/
def finiteCovariantPresentationToCoherentDualLinearEquiv
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) :
    ((K.X₁.obj ⟶ (S.fgObj X).obj) ⧸
        S.finiteCovariantPresentationRange K X) ≃ₗ[k]
      Ext.{u} (S.finiteContravariantDefect K)
        (S.finiteContravariantRepresentableOnSkeleton.obj X) 2 :=
  (S.finiteContravariantDefectPresentationYonedaLinearEquiv K X).trans
    (S.finiteContravariantDefectPresentationLinearEquiv hK X)

@[simp]
theorem finiteCovariantPresentationToCoherentDualLinearEquiv_mk
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) (f : K.X₁.obj ⟶ (S.fgObj X).obj) :
    S.finiteCovariantPresentationToCoherentDualLinearEquiv hK X
        (Submodule.Quotient.mk f) =
      S.finiteCovariantRepresentableToCoherentDualLinear hK X f := by
  rfl

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
