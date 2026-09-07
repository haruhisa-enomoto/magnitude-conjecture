import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownControlWindow

/-!
# Indecomposable density for finite Gabriel push-down

Gabriel's density theorem is stated for indecomposable modules.  This file
uses finite indecomposable decompositions and additivity of push-down to turn
that statement into the global essential-surjectivity interface consumed by
the finite control-window transport.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Density on indecomposable downstairs modules implies the global
essential-surjectivity form used by the finite control-window theorems. -/
theorem finiteOrbitPushdownDensity_of_indec_dense
    (dense :
      letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := isLinearModule_stableUnderShift (k := k) D.core
      letI := linearModuleCategoryHasShift (k := k) D.core
      letI := linearModuleCategoryAdditiveShift (R := k) D.core
      letI := linearModuleCategoryLinearShift (R := k) D.core
      letI := trivialHasShift
        (LinearModuleCategory.{u, max v w, uK, max w uM}
          (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
      let P := finiteDimensionalModuleOrbitSkeletonPushdown.{u, v, w, uK, uM}
        D (k := k)
      ∀ Y : FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
          (C := DeckOrbitSkeleton C G) k,
        Indecomposable Y → ∃ X, Nonempty (P.obj X ≅ Y)) :
    FiniteOrbitPushdownDensity.{u, v, w, uK, uM} (k := k) D := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let P := finiteDimensionalModuleOrbitSkeletonPushdown.{u, v, w, uK, uM}
    D (k := k)
  letI : P.Additive := inferInstance
  refine ⟨MagnitudeConjecture.CategoryTheory.functor_essSurj_of_indec_dense
    P ?_ dense⟩
  intro Y
  exact finiteDimensionalModule_finiteIndecomposableDecomposition Y

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
