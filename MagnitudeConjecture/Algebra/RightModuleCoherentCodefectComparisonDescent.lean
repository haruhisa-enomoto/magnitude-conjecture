import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectComparisonNaturality

/-! # Descent of the reverse coherent-defect comparison -/

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

/-- Maps factoring through `K.X₂` have zero reverse coherent-dual class. -/
theorem finiteContravariantRepresentableToCoherentCodualLinear_comp_g_zero
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) (b : (S.fgObj X).obj ⟶ K.X₂.obj) :
    S.finiteContravariantRepresentableToCoherentCodualLinear hK X
        (b ≫ K.g.hom) = 0 := by
  let v : (S.finiteCovariantDefectLeftShortComplex K).X₁ ⟶
      S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X) :=
    S.finiteRestrictedCovariantRepresentableMap
      (ObjectProperty.homMk (b ≫ K.g.hom))
  have hv : v ∈ ProjectivePresentationExt.presentationRange (k := k)
      (S.finiteCovariantDefectLeftShortComplex K)
      (S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X)) := by
    refine ⟨S.finiteRestrictedCovariantRepresentableMap
      (ObjectProperty.homMk b), ?_⟩
    dsimp only [v]
    change
      S.finiteRestrictedCovariantRepresentableMap K.g ≫
          S.finiteRestrictedCovariantRepresentableMap
            (ObjectProperty.homMk b) =
        S.finiteRestrictedCovariantRepresentableMap
          (ObjectProperty.homMk (b ≫ K.g.hom))
    exact S.finiteRestrictedCovariantRepresentableMap_comp
      (ObjectProperty.homMk b) K.g
  have hz : Submodule.Quotient.mk
      (p := ProjectivePresentationExt.presentationRange (k := k)
        (S.finiteCovariantDefectLeftShortComplex K)
        (S.finiteCovariantRepresentableOnSkeleton.obj (Opposite.op X))) v = 0 := by
    rw [Submodule.Quotient.mk_eq_zero]
    exact hv
  rw [S.finiteContravariantRepresentableToCoherentCodualLinear_apply]
  change S.finiteCovariantDefectPresentationLinearEquiv hK (Opposite.op X)
    (Submodule.Quotient.mk v) = 0
  calc
    _ = S.finiteCovariantDefectPresentationLinearEquiv hK (Opposite.op X) 0 :=
      congrArg
        (S.finiteCovariantDefectPresentationLinearEquiv hK (Opposite.op X)) hz
    _ = 0 :=
      (S.finiteCovariantDefectPresentationLinearEquiv
        hK (Opposite.op X)).map_zero

/-- The reverse comparison annihilates the image of the first
contravariant representable. -/
theorem finiteContravariantRepresentableToCoherentCodual_comp_eq_zero
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    S.finiteContravariantFunctorInclusion.map
        (S.finiteRestrictedContravariantRepresentableMap K.g) ≫
      S.finiteContravariantRepresentableToCoherentCodual hK = 0 := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact
    S.finiteContravariantRepresentableToCoherentCodualLinear_comp_g_zero
      hK X.unop b

/-- The reverse comparison descended to the ambient cokernel. -/
def finiteContravariantCokernelToCoherentCodual
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    cokernel (S.finiteContravariantFunctorInclusion.map
      (S.finiteRestrictedContravariantRepresentableMap K.g)) ⟶
        S.coherentCodualObj (S.finiteCovariantDefect K) :=
  cokernel.desc _ (S.finiteContravariantRepresentableToCoherentCodual hK)
    (S.finiteContravariantRepresentableToCoherentCodual_comp_eq_zero hK)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
