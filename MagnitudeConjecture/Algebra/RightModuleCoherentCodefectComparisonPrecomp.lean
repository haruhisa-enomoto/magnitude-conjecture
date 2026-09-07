import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectComparisonPresentationPrecomp

/-! # Precomposition for the reverse coherent-defect comparison -/

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

/-- Naturality of the unquotiented reverse comparison. -/
theorem finiteContravariantRepresentableToCoherentCodualLinear_precomp
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    {X Y : S.IndecCategoryᵒᵖ} (a : X ⟶ Y)
    (f : (S.fgObj X.unop).obj ⟶ K.X₃.obj) :
    S.finiteContravariantRepresentableToCoherentCodualLinear hK Y.unop
        ((S.fgMap a.unop).hom ≫ f) =
      Ext.postcompOfLinear
        (Ext.mk₀ (S.finiteCovariantRepresentableOnSkeleton.map a)) k
        (S.finiteCovariantDefect K) (add_zero 2)
        (S.finiteContravariantRepresentableToCoherentCodualLinear
          hK X.unop f) := by
  exact S.finiteCovariantDefectPresentationLinearEquiv_representable_precomp
    hK a f

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
