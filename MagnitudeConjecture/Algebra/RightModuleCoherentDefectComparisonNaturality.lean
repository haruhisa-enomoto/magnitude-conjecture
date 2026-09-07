import MagnitudeConjecture.Algebra.RightModuleCoherentDefectComparisonMap

/-! # Naturality of the coherent-defect comparison -/

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

/-- Naturality of the unquotiented comparison. -/
theorem finiteCovariantRepresentableToCoherentDualLinear_postcomp
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    {X Y : S.IndecCategory} (a : X ⟶ Y)
    (f : K.X₁.obj ⟶ (S.fgObj X).obj) :
    S.finiteCovariantRepresentableToCoherentDualLinear hK Y
        (f ≫ (S.fgMap a).hom) =
      Ext.postcompOfLinear
        (Ext.mk₀ (S.finiteContravariantRepresentableOnSkeleton.map a)) k
        (S.finiteContravariantDefect K) (add_zero 2)
        (S.finiteCovariantRepresentableToCoherentDualLinear hK X f) := by
  let q := Submodule.Quotient.mk
    (p := ProjectivePresentationExt.presentationRange (k := k)
      (S.finiteContravariantDefectLeftShortComplex K)
      (S.finiteContravariantRepresentableOnSkeleton.obj X))
    (S.finiteRestrictedContravariantRepresentableMap
      (ObjectProperty.homMk f))
  have hnat := S.finiteContravariantDefectPresentationLinearEquiv_postcomp
    hK a q
  rw [S.finiteCovariantRepresentableToCoherentDualLinear_apply,
    S.finiteCovariantRepresentableToCoherentDualLinear_apply, ← hnat]
  congr 1

/-- The unquotiented comparison is a natural transformation. -/
def finiteCovariantRepresentableToCoherentDual
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    S.finiteCovariantFunctorInclusion.obj
        (S.finiteRestrictedCovariantRepresentable K.X₁) ⟶
      S.coherentDualObj (S.finiteContravariantDefect K) where
  app X := ModuleCat.ofHom
    (S.finiteCovariantRepresentableToCoherentDualLinear hK X)
  naturality := by
    intro X Y a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact S.finiteCovariantRepresentableToCoherentDualLinear_postcomp hK a f

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
