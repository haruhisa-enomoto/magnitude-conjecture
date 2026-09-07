import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectComparisonDescent

/-! # The quotient equivalence underlying the reverse comparison -/

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

/-- The contravariant module-presentation quotient is canonically the
degree-two Ext group defining the reverse coherent dual. -/
def finiteContravariantPresentationToCoherentCodualLinearEquiv
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) :
    (((S.fgObj X).obj ⟶ K.X₃.obj) ⧸
        S.finiteContravariantPresentationRange K X) ≃ₗ[k]
      Ext.{u} (S.finiteCovariantDefect K)
        (S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X)) 2 :=
  (S.finiteCovariantDefectPresentationCoyonedaLinearEquiv K X).trans
    (S.finiteCovariantDefectPresentationLinearEquiv hK (Opposite.op X))

@[simp]
theorem finiteContravariantPresentationToCoherentCodualLinearEquiv_mk
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) (f : (S.fgObj X).obj ⟶ K.X₃.obj) :
    S.finiteContravariantPresentationToCoherentCodualLinearEquiv hK X
        (Submodule.Quotient.mk f) =
      S.finiteContravariantRepresentableToCoherentCodualLinear hK X f := by
  rfl

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
