import MagnitudeConjecture.Algebra.RightModuleCoherentDefectEvaluation
import MagnitudeConjecture.CategoryTheory.LinearExtAlongFunctor

/-!
# The reverse coherent dual on the finite right-module skeleton

For a finite covariant functor `G`, the reverse coherent dual is

`X ↦ Ext²(G, Hom(X, -))`.

Its exact-presentation calculation will recover the corresponding
contravariant defect and provide the inverse half of Auslander's duality.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable [HasExt.{u} (S.FiniteCovariantFunctor)]

/-- Restricted covariant representables, contravariantly functorial in the
chosen representing indecomposable. -/
def finiteCovariantRepresentableOnSkeleton :
    S.IndecCategoryᵒᵖ ⥤ S.FiniteCovariantFunctor where
  obj X := S.finiteRestrictedCovariantRepresentable (S.fgObj X.unop)
  map a := S.finiteRestrictedCovariantRepresentableMap (S.fgMap a.unop)
  map_id X := by
    rw [show S.fgMap (𝟙 X).unop = 𝟙 (S.fgObj X.unop) by
      apply ObjectProperty.hom_ext
      exact S.inclusion.map_id X.unop]
    exact S.finiteRestrictedCovariantRepresentableMap_id (S.fgObj X.unop)
  map_comp a b := by
    rw [show S.fgMap (a ≫ b).unop = S.fgMap b.unop ≫ S.fgMap a.unop by
      apply ObjectProperty.hom_ext
      exact S.inclusion.map_comp b.unop a.unop]
    exact S.finiteRestrictedCovariantRepresentableMap_comp _ _

/-- The reverse coherent-dual expression on one finite covariant functor. -/
def coherentCodualObj (G : S.FiniteCovariantFunctor) :
    S.IndecCategoryᵒᵖ ⥤ ModuleCat.{u} k :=
  MagnitudeConjecture.CategoryTheory.linearExtObjAlong
    (R := k) S.finiteCovariantRepresentableOnSkeleton G 2

/-- The reverse coherent dual is contravariantly functorial in the finite
covariant functor. -/
def coherentCodualRaw :
    S.FiniteCovariantFunctorᵒᵖ ⥤
      (S.IndecCategoryᵒᵖ ⥤ ModuleCat.{u} k) :=
  MagnitudeConjecture.CategoryTheory.linearExtAlong
    (R := k) S.finiteCovariantRepresentableOnSkeleton 2

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
