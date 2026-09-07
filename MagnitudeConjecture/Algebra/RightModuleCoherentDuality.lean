import MagnitudeConjecture.Algebra.RightModuleCoherentDefect
import MagnitudeConjecture.CategoryTheory.LinearExtAlongFunctor

/-!
# Auslander's coherent dual on the finite right-module skeleton

For a finite contravariant functor `F`, Auslander's coherent dual is the
covariant functor

`X ↦ Ext²(F, Hom(-, X))`.

This file first constructs that expression functorially, including its
contravariance in `F`.  The subsequent exact-presentation comparison will
identify its value on `finiteContravariantDefect K` with
`finiteCovariantDefect K` when `K` is short exact.
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

abbrev FiniteContravariantFunctor :=
  CoveringHom.FiniteDimensionalModuleCategory
    (C := S.IndecCategoryᵒᵖ) k

variable [HasExt.{u} (FG (A := A))]
variable [HasExt.{u} (S.FiniteContravariantFunctor)]

/-- Restricted contravariant representables, with the represented object
confined to the chosen indecomposable skeleton.  Naming this functor keeps
the substantially larger `Ext²` expressions below from repeatedly unfolding
the full-subcategory maps. -/
def finiteContravariantRepresentableOnSkeleton :
    S.IndecCategory ⥤ S.FiniteContravariantFunctor where
  obj X := S.finiteRestrictedContravariantRepresentable (S.fgObj X)
  map f := S.finiteRestrictedContravariantRepresentableMap (S.fgMap f)
  map_id X := by
    rw [show S.fgMap (𝟙 X) = 𝟙 (S.fgObj X) by
      apply ObjectProperty.hom_ext
      exact S.inclusion.map_id X]
    exact S.finiteRestrictedContravariantRepresentableMap_id (S.fgObj X)
  map_comp f g := by
    rw [show S.fgMap (f ≫ g) = S.fgMap f ≫ S.fgMap g by
      apply ObjectProperty.hom_ext
      exact S.inclusion.map_comp f g]
    exact S.finiteRestrictedContravariantRepresentableMap_comp _ _

/-- The `Ext²` expression defining Auslander's coherent dual of one finite
contravariant functor.  At this stage the codomain is the ambient functor
category; finiteness will follow from an exact presentation. -/
def coherentDualObj (F : S.FiniteContravariantFunctor) :
    S.IndecCategory ⥤ ModuleCat.{u} k :=
  MagnitudeConjecture.CategoryTheory.linearExtObjAlong
    (R := k) S.finiteContravariantRepresentableOnSkeleton F 2

/-- Auslander's coherent-dual construction is contravariantly functorial in
the finite contravariant functor. -/
def coherentDualRaw :
    S.FiniteContravariantFunctorᵒᵖ ⥤
      (S.IndecCategory ⥤ ModuleCat.{u} k) :=
  MagnitudeConjecture.CategoryTheory.linearExtAlong
    (R := k) S.finiteContravariantRepresentableOnSkeleton 2

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
