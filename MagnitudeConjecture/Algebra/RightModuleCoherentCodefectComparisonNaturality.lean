import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectComparisonPrecomp

/-! # Naturality of the reverse coherent-defect comparison -/

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

/-- The unquotiented reverse comparison is a natural transformation. -/
def finiteContravariantRepresentableToCoherentCodual
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    S.finiteContravariantFunctorInclusion.obj
        (S.finiteRestrictedContravariantRepresentable K.X₃) ⟶
      S.coherentCodualObj (S.finiteCovariantDefect K) where
  app X := ModuleCat.ofHom
    (S.finiteContravariantRepresentableToCoherentCodualLinear hK X.unop)
  naturality := by
    intro X Y a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact S.finiteContravariantRepresentableToCoherentCodualLinear_precomp
      hK a f

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
