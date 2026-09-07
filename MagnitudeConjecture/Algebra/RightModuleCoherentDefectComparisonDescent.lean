import MagnitudeConjecture.Algebra.RightModuleCoherentDefectComparisonNaturality

/-! # Descent of the coherent-defect comparison -/

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

/-- Maps extending across `K.X₂` have zero coherent-dual class. -/
theorem finiteCovariantRepresentableToCoherentDualLinear_comp_f_zero
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) (b : K.X₂.obj ⟶ (S.fgObj X).obj) :
    S.finiteCovariantRepresentableToCoherentDualLinear hK X
        (K.f.hom ≫ b) = 0 := by
  let v : (S.finiteContravariantDefectLeftShortComplex K).X₁ ⟶
      S.finiteContravariantRepresentableOnSkeleton.obj X :=
    S.finiteRestrictedContravariantRepresentableMap
      (ObjectProperty.homMk (K.f.hom ≫ b))
  have hv : v ∈ ProjectivePresentationExt.presentationRange (k := k)
      (S.finiteContravariantDefectLeftShortComplex K)
      (S.finiteContravariantRepresentableOnSkeleton.obj X) := by
    refine ⟨S.finiteRestrictedContravariantRepresentableMap
      (ObjectProperty.homMk b), ?_⟩
    dsimp only [v]
    change
      S.finiteRestrictedContravariantRepresentableMap K.f ≫
          S.finiteRestrictedContravariantRepresentableMap
            (ObjectProperty.homMk b) =
        S.finiteRestrictedContravariantRepresentableMap
          (ObjectProperty.homMk (K.f.hom ≫ b))
    exact (S.finiteRestrictedContravariantRepresentableMap_comp
      K.f (ObjectProperty.homMk b)).symm
  have hz : Submodule.Quotient.mk
      (p := ProjectivePresentationExt.presentationRange (k := k)
        (S.finiteContravariantDefectLeftShortComplex K)
        (S.finiteContravariantRepresentableOnSkeleton.obj X)) v = 0 := by
    rw [Submodule.Quotient.mk_eq_zero]
    exact hv
  rw [S.finiteCovariantRepresentableToCoherentDualLinear_apply]
  change S.finiteContravariantDefectPresentationLinearEquiv hK X
    (Submodule.Quotient.mk v) = 0
  calc
    _ = S.finiteContravariantDefectPresentationLinearEquiv hK X 0 :=
      congrArg (S.finiteContravariantDefectPresentationLinearEquiv hK X) hz
    _ = 0 := (S.finiteContravariantDefectPresentationLinearEquiv hK X).map_zero

/-- The comparison annihilates the image of the second covariant
representable. -/
theorem finiteCovariantRepresentableToCoherentDual_comp_eq_zero
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    S.finiteCovariantFunctorInclusion.map
        (S.finiteRestrictedCovariantRepresentableMap K.f) ≫
      S.finiteCovariantRepresentableToCoherentDual hK = 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact S.finiteCovariantRepresentableToCoherentDualLinear_comp_f_zero hK X b

/-- The canonical comparison descended to the ambient cokernel. -/
def finiteCovariantCokernelToCoherentDual
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    cokernel (S.finiteCovariantFunctorInclusion.map
      (S.finiteRestrictedCovariantRepresentableMap K.f)) ⟶
        S.coherentDualObj (S.finiteContravariantDefect K) :=
  cokernel.desc _ (S.finiteCovariantRepresentableToCoherentDual hK)
    (S.finiteCovariantRepresentableToCoherentDual_comp_eq_zero hK)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
