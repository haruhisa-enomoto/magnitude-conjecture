import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectComparisonMap

/-! # Restricted-covariant-representable precomposition -/

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

/-- Restricted covariant Yoneda converts precomposition of module maps into
postcomposition of natural transformations. -/
theorem finiteRestrictedCovariantRepresentableMap_precomp
    {K : ShortComplex (FG (A := A))}
    {X Y : S.IndecCategoryᵒᵖ} (a : X ⟶ Y)
    (f : (S.fgObj X.unop).obj ⟶ K.X₃.obj) :
    S.finiteRestrictedCovariantRepresentableMap
        (ObjectProperty.homMk ((S.fgMap a.unop).hom ≫ f)) =
      S.finiteRestrictedCovariantRepresentableMap
          (ObjectProperty.homMk f) ≫
        S.finiteCovariantRepresentableOnSkeleton.map a := by
  rw [show ObjectProperty.homMk ((S.fgMap a.unop).hom ≫ f) =
      S.fgMap a.unop ≫ ObjectProperty.homMk f from rfl,
    S.finiteRestrictedCovariantRepresentableMap_comp]
  rfl

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
