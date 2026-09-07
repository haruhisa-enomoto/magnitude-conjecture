import MagnitudeConjecture.Algebra.RightModuleCoherentDefect
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Evaluating the covariant defect

Evaluation is exact on the finite linear functor category.  Consequently the
value of the covariant defect at `X` is the ordinary quotient

`Hom(A, X) / im(Hom(B, X) → Hom(A, X))`

attached to the first map `A → B` of the module complex.
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

abbrev FiniteCovariantFunctor :=
  CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
    (C := S.IndecCategory) k

private abbrev finiteModuleInclusion :=
  (CoveringHom.IsFiniteDimensionalModule.{0, u, u, u}
    (C := S.IndecCategory) k).ι

private abbrev linearModuleInclusion :=
  (CoveringHom.IsLinearModule.{0, u, u, u}
    (C := S.IndecCategory) k).ι

/-- Forget the finite-dimensional and linear-property wrappers. -/
def finiteCovariantFunctorInclusion :
    FiniteCovariantFunctor S ⥤
      (S.IndecCategory ⥤ ModuleCat.{u} k) :=
  finiteModuleInclusion S ⋙ linearModuleInclusion S

/-- Evaluation of a finite covariant functor at a chosen indecomposable. -/
def finiteCovariantFunctorEvaluation (X : S.IndecCategory) :
    FiniteCovariantFunctor S ⥤ ModuleCat.{u} k :=
  S.finiteCovariantFunctorInclusion ⋙
    (evaluation S.IndecCategory (ModuleCat.{u} k)).obj X

local instance {M N : FiniteCovariantFunctor S} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (finiteModuleInclusion S) :=
  (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).preservesCokernels_ι f

local instance {M N : FiniteCovariantFunctor S} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (finiteModuleInclusion S) :=
  (CoveringHom.IsFiniteDimensionalModule
    (C := S.IndecCategory) k).preservesKernels_ι f

local instance {M N : CoveringHom.LinearModuleCategory
    (C := S.IndecCategory) k} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (linearModuleInclusion S) :=
  (CoveringHom.IsLinearModule
    (C := S.IndecCategory) k).preservesCokernels_ι f

local instance {M N : CoveringHom.LinearModuleCategory
    (C := S.IndecCategory) k} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (linearModuleInclusion S) :=
  (CoveringHom.IsLinearModule
    (C := S.IndecCategory) k).preservesKernels_ι f

local instance : PreservesFiniteLimits (finiteModuleInclusion S) :=
  (finiteModuleInclusion S).preservesFiniteLimits_of_preservesKernels

local instance : PreservesFiniteLimits (linearModuleInclusion S) :=
  (linearModuleInclusion S).preservesFiniteLimits_of_preservesKernels

local instance : PreservesFiniteLimits
    (finiteModuleInclusion S ⋙ linearModuleInclusion S) :=
  comp_preservesFiniteLimits (finiteModuleInclusion S)
    (linearModuleInclusion S)

local instance : PreservesFiniteColimits (finiteModuleInclusion S) :=
  (finiteModuleInclusion S).preservesFiniteColimits_of_preservesCokernels

local instance : PreservesFiniteColimits (linearModuleInclusion S) :=
  (linearModuleInclusion S).preservesFiniteColimits_of_preservesCokernels

local instance : PreservesFiniteColimits
    (finiteModuleInclusion S ⋙ linearModuleInclusion S) :=
  comp_preservesFiniteColimits (finiteModuleInclusion S)
    (linearModuleInclusion S)

noncomputable instance finiteCovariantFunctorInclusion_preservesFiniteColimits :
    PreservesFiniteColimits S.finiteCovariantFunctorInclusion := by
  change PreservesFiniteColimits
    (finiteModuleInclusion S ⋙ linearModuleInclusion S)
  infer_instance

noncomputable instance finiteCovariantFunctorInclusion_preservesFiniteLimits :
    PreservesFiniteLimits S.finiteCovariantFunctorInclusion := by
  change PreservesFiniteLimits
    (finiteModuleInclusion S ⋙ linearModuleInclusion S)
  infer_instance

noncomputable instance finiteCovariantFunctorEvaluation_preservesFiniteLimits
    (X : S.IndecCategory) : PreservesFiniteLimits
      (S.finiteCovariantFunctorEvaluation X) := by
  change PreservesFiniteLimits
    (S.finiteCovariantFunctorInclusion ⋙
      (evaluation S.IndecCategory (ModuleCat.{u} k)).obj X)
  exact comp_preservesFiniteLimits
    S.finiteCovariantFunctorInclusion
    ((evaluation S.IndecCategory (ModuleCat.{u} k)).obj X)

noncomputable instance finiteCovariantFunctorEvaluation_preservesFiniteColimits
    (X : S.IndecCategory) : PreservesFiniteColimits
      (S.finiteCovariantFunctorEvaluation X) := by
  change PreservesFiniteColimits
    (S.finiteCovariantFunctorInclusion ⋙
      (evaluation S.IndecCategory (ModuleCat.{u} k)).obj X)
  exact comp_preservesFiniteColimits
    S.finiteCovariantFunctorInclusion
    ((evaluation S.IndecCategory (ModuleCat.{u} k)).obj X)

local instance (X : S.IndecCategory) : PreservesFiniteColimits
    (S.finiteCovariantFunctorEvaluation X) := by
  change PreservesFiniteColimits
    (S.finiteCovariantFunctorInclusion ⋙
      (evaluation S.IndecCategory (ModuleCat.{u} k)).obj X)
  exact comp_preservesFiniteColimits
    S.finiteCovariantFunctorInclusion
    ((evaluation S.IndecCategory (ModuleCat.{u} k)).obj X)

/-- The ambient module-theoretic presentation coboundaries obtained by
precomposing with the first map of `K`. -/
abbrev finiteCovariantPresentationRange
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    Submodule k (K.X₁.obj ⟶ (S.fgObj X).obj) :=
  (CategoryTheory.Linear.leftComp k (S.inclusion.obj X) K.f.hom).range

/-- Evaluating the covariant representable map gives the ordinary
precomposition map in the module category. -/
theorem finiteCovariantFunctorEvaluation_map_range
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    ((S.finiteCovariantFunctorEvaluation X).map
      (S.finiteRestrictedCovariantRepresentableMap K.f)).hom.range =
        S.finiteCovariantPresentationRange K X := by
  rfl

/-- The value of the covariant defect is the module-presentation quotient. -/
def finiteCovariantDefectEvaluationIsoPresentationQuotient
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    (S.finiteCovariantDefect K).obj.obj.obj X ≅
      ModuleCat.of k
        ((K.X₁.obj ⟶ (S.fgObj X).obj) ⧸
          S.finiteCovariantPresentationRange K X) := by
  let E := S.finiteCovariantFunctorEvaluation X
  let f := S.finiteRestrictedCovariantRepresentableMap K.f
  let eCokernel : E.obj (cokernel f) ≅ cokernel (E.map f) :=
    PreservesCokernel.iso E f
  let eQuotient :
      cokernel (E.map f) ≅
        ModuleCat.of k
          ((K.X₁.obj ⟶ (S.fgObj X).obj) ⧸
            S.finiteCovariantPresentationRange K X) :=
    (ModuleCat.cokernelIsoRangeQuotient (E.map f)).trans
      ((Submodule.quotEquivOfEq _ _
        (S.finiteCovariantFunctorEvaluation_map_range K X)).toModuleIso)
  exact eCokernel.trans eQuotient

/-- Linear-equivalence form of the evaluated covariant-defect calculation. -/
def finiteCovariantDefectEvaluationLinearEquivPresentationQuotient
    (K : ShortComplex (FG (A := A))) (X : S.IndecCategory) :
    (S.finiteCovariantDefect K).obj.obj.obj X ≃ₗ[k]
      ((K.X₁.obj ⟶ (S.fgObj X).obj) ⧸
        S.finiteCovariantPresentationRange K X) :=
  (S.finiteCovariantDefectEvaluationIsoPresentationQuotient K X).toLinearEquiv

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
