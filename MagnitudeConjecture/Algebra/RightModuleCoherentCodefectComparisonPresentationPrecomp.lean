import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectComparisonMapPrecomp

/-! # Presentation-level reverse comparison naturality -/

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

/-- Naturality of the reverse Ext² comparison on quotient representatives
coming from restricted covariant Yoneda. -/
theorem finiteCovariantDefectPresentationLinearEquiv_representable_precomp
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    {X Y : S.IndecCategoryᵒᵖ} (a : X ⟶ Y)
    (f : (S.fgObj X.unop).obj ⟶ K.X₃.obj) :
    S.finiteCovariantDefectPresentationLinearEquiv hK Y
        (Submodule.Quotient.mk
          (S.finiteRestrictedCovariantRepresentableMap
            (ObjectProperty.homMk ((S.fgMap a.unop).hom ≫ f)))) =
      Ext.postcompOfLinear
        (Ext.mk₀ (S.finiteCovariantRepresentableOnSkeleton.map a)) k
        (S.finiteCovariantDefect K) (add_zero 2)
        (S.finiteCovariantDefectPresentationLinearEquiv hK X
          (Submodule.Quotient.mk
            (S.finiteRestrictedCovariantRepresentableMap
              (ObjectProperty.homMk f)))) := by
  let q := Submodule.Quotient.mk
    (p := ProjectivePresentationExt.presentationRange (k := k)
      (S.finiteCovariantDefectLeftShortComplex K)
      (S.finiteCovariantRepresentableOnSkeleton.obj X))
    (S.finiteRestrictedCovariantRepresentableMap
      (ObjectProperty.homMk f))
  have hnat := S.finiteCovariantDefectPresentationLinearEquiv_postcomp
    hK a q
  rw [S.finiteRestrictedCovariantRepresentableMap_precomp]
  change
    S.finiteCovariantDefectPresentationLinearEquiv hK Y
        (ProjectivePresentationExt.postcompQuotient (k := k)
          (S.finiteCovariantDefectLeftShortComplex K)
          (S.finiteCovariantRepresentableOnSkeleton.map a) q) = _
  exact hnat

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
