import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAbelian
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleHomFinite
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Restriction of finite-dimensional linear modules

Precomposition along a linear functor whose source has finitely many objects
restricts finite-dimensional modules to finite-dimensional modules.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe uC uD v

variable {k : Type v} [Field k]
variable {C : Type uC} {D : Type uD}
variable [Category.{v} C] [Category.{v} D]
variable [Preadditive C] [Preadditive D] [Linear k C] [Linear k D]
variable [Fintype C]

/-- Restriction of finite-dimensional linear modules along a linear functor
with finite source. -/
def finiteLinearModuleRestrictionFunctor
    (F : C ⥤ D) [F.Additive] [F.Linear k] :
    FiniteDimensionalModuleCategory.{uD, v, v, v} (C := D) k ⥤
      FiniteDimensionalModuleCategory.{uC, v, v, v} (C := C) k where
  obj M :=
    { obj := ⟨F ⋙ M.obj.obj, inferInstance, inferInstance⟩
      property := by
        constructor
        · intro X
          exact M.property.1 (F.obj X)
        · exact Set.toFinite _ }
  map f := ObjectProperty.homMk <| ObjectProperty.homMk <|
    Functor.whiskerLeft F f.hom.hom
  map_id M := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact Functor.whiskerLeft_id F
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact Functor.whiskerLeft_comp F f.hom.hom g.hom.hom

instance finiteLinearModuleRestrictionFunctor_additive
    (F : C ⥤ D) [F.Additive] [F.Linear k] :
    (finiteLinearModuleRestrictionFunctor (k := k) F).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    rfl

instance finiteLinearModuleRestrictionFunctor_linear
    (F : C ⥤ D) [F.Additive] [F.Linear k] :
    (finiteLinearModuleRestrictionFunctor (k := k) F).Linear k where
  map_smul := by
    intro M N f r
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    rfl

/-- Restriction of finite linear modules preserves kernels.  After forgetting
the two full-subcategory layers, this is the pointwise fact that
precomposition preserves limits. -/
instance finiteLinearModuleRestrictionFunctor_preservesKernel
    (F : Functor C D) [F.Additive] [F.Linear k]
    {X Y : FiniteDimensionalModuleCategory.{uD, v, v, v} (C := D) k}
    (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0)
      (finiteLinearModuleRestrictionFunctor (k := k) F) := by
  let K := finiteLinearModuleRestrictionFunctor (k := k) F
  let sourceFiniteInclusion :=
    (IsFiniteDimensionalModule (C := D) k).ι
  let sourceLinearInclusion := (IsLinearModule (C := D) k).ι
  let sourceUnderlying := sourceFiniteInclusion ⋙ sourceLinearInclusion
  let targetFiniteInclusion :=
    (IsFiniteDimensionalModule (C := C) k).ι
  let targetLinearInclusion := (IsLinearModule (C := C) k).ι
  let targetUnderlying := targetFiniteInclusion ⋙ targetLinearInclusion
  letI : PreservesLimit (parallelPair f 0) sourceFiniteInclusion :=
    (IsFiniteDimensionalModule (C := D) k).preservesKernels_ι f
  letI : PreservesLimit
      (parallelPair (sourceFiniteInclusion.map f) 0)
      sourceLinearInclusion :=
    (IsLinearModule (C := D) k).preservesKernels_ι
      (sourceFiniteInclusion.map f)
  letI : PreservesLimit
      (parallelPair f 0 ⋙ sourceFiniteInclusion)
      sourceLinearInclusion := by
    letI : PreservesLimit
        (parallelPair
          ((parallelPair f 0 ⋙ sourceFiniteInclusion).map
            WalkingParallelPairHom.left)
          ((parallelPair f 0 ⋙ sourceFiniteInclusion).map
            WalkingParallelPairHom.right))
        sourceLinearInclusion := by
      rw [show
        (parallelPair f 0 ⋙ sourceFiniteInclusion).map
            WalkingParallelPairHom.right = 0 by rfl]
      exact (IsLinearModule (C := D) k).preservesKernels_ι
        ((parallelPair f 0 ⋙ sourceFiniteInclusion).map
          WalkingParallelPairHom.left)
    apply preservesLimit_of_iso_diagram sourceLinearInclusion
      (diagramIsoParallelPair _).symm
  letI : PreservesLimit (parallelPair f 0) sourceUnderlying :=
    comp_preservesLimit sourceFiniteInclusion sourceLinearInclusion
  letI : targetUnderlying.Faithful := by
    dsimp only [targetUnderlying]
    infer_instance
  letI : targetUnderlying.Full := by
    dsimp only [targetUnderlying]
    infer_instance
  constructor
  intro c hc
  constructor
  apply isLimitOfReflects targetUnderlying
  apply evaluationJointlyReflectsLimits
  intro p
  let E := sourceUnderlying ⋙
    (evaluation D (ModuleCat.{v} k)).obj (F.obj p)
  letI : PreservesLimit (parallelPair f 0) E := by
    dsimp only [E]
    infer_instance
  exact isLimitOfPreserves E hc

end MagnitudeConjecture.CoveringHom
