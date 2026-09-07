import MagnitudeConjecture.Algebra.RightModuleCoherentCoduality
import MagnitudeConjecture.Algebra.RightModuleCoherentDuality
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Evaluating the contravariant defect

Evaluation is exact on the finite linear functor category.  Consequently the
value of the contravariant defect at `Xᵒᵖ` is the ordinary quotient

`Hom(X, C) / im(Hom(X, B) → Hom(X, C))`

attached to the second map `B → C` of the module complex.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

private abbrev finiteContravariantModuleInclusion :=
  (CoveringHom.IsFiniteDimensionalModule.{0, u, u, u}
    (C := S.IndecCategoryᵒᵖ) k).ι

private abbrev contravariantLinearModuleInclusion :=
  (CoveringHom.IsLinearModule.{0, u, u, u}
    (C := S.IndecCategoryᵒᵖ) k).ι

/-- Forget the finite-dimensional and linear-property wrappers. -/
def finiteContravariantFunctorInclusion :
    S.FiniteContravariantFunctor ⥤
      (S.IndecCategoryᵒᵖ ⥤ ModuleCat.{u} k) :=
  finiteContravariantModuleInclusion S ⋙
    contravariantLinearModuleInclusion S

/-- Evaluation of a finite contravariant functor at a chosen indecomposable. -/
def finiteContravariantFunctorEvaluation (X : S.IndecCategoryᵒᵖ) :
    S.FiniteContravariantFunctor ⥤ ModuleCat.{u} k :=
  S.finiteContravariantFunctorInclusion ⋙
    (evaluation S.IndecCategoryᵒᵖ (ModuleCat.{u} k)).obj X

local instance {M N : S.FiniteContravariantFunctor} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0)
      (finiteContravariantModuleInclusion S) :=
  (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategoryᵒᵖ) k).preservesCokernels_ι f

local instance {M N : S.FiniteContravariantFunctor} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0)
      (finiteContravariantModuleInclusion S) :=
  (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategoryᵒᵖ) k).preservesKernels_ι f

local instance {M N : CoveringHom.LinearModuleCategory
    (C := S.IndecCategoryᵒᵖ) k} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0)
      (contravariantLinearModuleInclusion S) :=
  (CoveringHom.IsLinearModule
    (C := S.IndecCategoryᵒᵖ) k).preservesCokernels_ι f

local instance {M N : CoveringHom.LinearModuleCategory
    (C := S.IndecCategoryᵒᵖ) k} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0)
      (contravariantLinearModuleInclusion S) :=
  (CoveringHom.IsLinearModule
    (C := S.IndecCategoryᵒᵖ) k).preservesKernels_ι f

local instance : PreservesFiniteLimits
    (finiteContravariantModuleInclusion S) :=
  (finiteContravariantModuleInclusion S).preservesFiniteLimits_of_preservesKernels

local instance : PreservesFiniteLimits
    (contravariantLinearModuleInclusion S) :=
  (contravariantLinearModuleInclusion S).preservesFiniteLimits_of_preservesKernels

local instance : PreservesFiniteLimits
    (finiteContravariantModuleInclusion S ⋙
      contravariantLinearModuleInclusion S) :=
  comp_preservesFiniteLimits (finiteContravariantModuleInclusion S)
    (contravariantLinearModuleInclusion S)

local instance : PreservesFiniteColimits
    (finiteContravariantModuleInclusion S) :=
  (finiteContravariantModuleInclusion S).preservesFiniteColimits_of_preservesCokernels

local instance : PreservesFiniteColimits
    (contravariantLinearModuleInclusion S) :=
  (contravariantLinearModuleInclusion S).preservesFiniteColimits_of_preservesCokernels

local instance : PreservesFiniteColimits
    (finiteContravariantModuleInclusion S ⋙
      contravariantLinearModuleInclusion S) :=
  comp_preservesFiniteColimits (finiteContravariantModuleInclusion S)
    (contravariantLinearModuleInclusion S)

noncomputable instance finiteContravariantFunctorInclusion_preservesFiniteColimits :
    PreservesFiniteColimits S.finiteContravariantFunctorInclusion := by
  change PreservesFiniteColimits
    (finiteContravariantModuleInclusion S ⋙
      contravariantLinearModuleInclusion S)
  infer_instance

noncomputable instance finiteContravariantFunctorInclusion_preservesFiniteLimits :
    PreservesFiniteLimits S.finiteContravariantFunctorInclusion := by
  change PreservesFiniteLimits
    (finiteContravariantModuleInclusion S ⋙
      contravariantLinearModuleInclusion S)
  infer_instance

noncomputable instance finiteContravariantFunctorEvaluation_preservesFiniteLimits
    (X : S.IndecCategoryᵒᵖ) : PreservesFiniteLimits
      (S.finiteContravariantFunctorEvaluation X) := by
  change PreservesFiniteLimits
    (S.finiteContravariantFunctorInclusion ⋙
      (evaluation S.IndecCategoryᵒᵖ (ModuleCat.{u} k)).obj X)
  exact comp_preservesFiniteLimits
    S.finiteContravariantFunctorInclusion
    ((evaluation S.IndecCategoryᵒᵖ (ModuleCat.{u} k)).obj X)

noncomputable instance finiteContravariantFunctorEvaluation_preservesFiniteColimits
    (X : S.IndecCategoryᵒᵖ) : PreservesFiniteColimits
      (S.finiteContravariantFunctorEvaluation X) := by
  change PreservesFiniteColimits
    (S.finiteContravariantFunctorInclusion ⋙
      (evaluation S.IndecCategoryᵒᵖ (ModuleCat.{u} k)).obj X)
  exact comp_preservesFiniteColimits
    S.finiteContravariantFunctorInclusion
    ((evaluation S.IndecCategoryᵒᵖ (ModuleCat.{u} k)).obj X)

local instance (X : S.IndecCategoryᵒᵖ) : PreservesFiniteColimits
    (S.finiteContravariantFunctorEvaluation X) := by
  change PreservesFiniteColimits
    (S.finiteContravariantFunctorInclusion ⋙
      (evaluation S.IndecCategoryᵒᵖ (ModuleCat.{u} k)).obj X)
  exact comp_preservesFiniteColimits
    S.finiteContravariantFunctorInclusion
    ((evaluation S.IndecCategoryᵒᵖ (ModuleCat.{u} k)).obj X)

/-- The ambient module-theoretic presentation coboundaries obtained by
postcomposing with the second map of `K`. -/
abbrev finiteContravariantPresentationRange
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    Submodule k ((S.fgObj X).obj ⟶ K.X₃.obj) :=
  (CategoryTheory.Linear.rightComp k (S.inclusion.obj X) K.g.hom).range

/-- Evaluating the contravariant representable map gives the ordinary
postcomposition map in the module category. -/
theorem finiteContravariantFunctorEvaluation_map_range
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    ((S.finiteContravariantFunctorEvaluation (Opposite.op X)).map
      (S.finiteRestrictedContravariantRepresentableMap K.g)).hom.range =
        S.finiteContravariantPresentationRange K X := by
  rfl

/-- The value of the contravariant defect is the module-presentation quotient. -/
def finiteContravariantDefectEvaluationIsoPresentationQuotient
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    (S.finiteContravariantDefect K).obj.obj.obj (Opposite.op X) ≅
      ModuleCat.of k
        (((S.fgObj X).obj ⟶ K.X₃.obj) ⧸
          S.finiteContravariantPresentationRange K X) := by
  let E := S.finiteContravariantFunctorEvaluation (Opposite.op X)
  let f := S.finiteRestrictedContravariantRepresentableMap K.g
  let eCokernel : E.obj (cokernel f) ≅ cokernel (E.map f) :=
    PreservesCokernel.iso E f
  let eQuotient :
      cokernel (E.map f) ≅
        ModuleCat.of k
          (((S.fgObj X).obj ⟶ K.X₃.obj) ⧸
            S.finiteContravariantPresentationRange K X) :=
    (ModuleCat.cokernelIsoRangeQuotient (E.map f)).trans
      ((Submodule.quotEquivOfEq _ _
        (S.finiteContravariantFunctorEvaluation_map_range K X)).toModuleIso)
  exact eCokernel.trans eQuotient

/-- Linear-equivalence form of the evaluated contravariant-defect calculation. -/
def finiteContravariantDefectEvaluationLinearEquivPresentationQuotient
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    (S.finiteContravariantDefect K).obj.obj.obj (Opposite.op X) ≃ₗ[k]
      (((S.fgObj X).obj ⟶ K.X₃.obj) ⧸
        S.finiteContravariantPresentationRange K X) :=
  (S.finiteContravariantDefectEvaluationIsoPresentationQuotient K X).toLinearEquiv

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
