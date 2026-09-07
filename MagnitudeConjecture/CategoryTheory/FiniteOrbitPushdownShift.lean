import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleOrbit
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdown
import MagnitudeConjecture.CategoryTheory.OrbitPushdownShift

/-!
# Translation invariance of finite-dimensional skeletal push-down

The generic translation-invariance isomorphism for Gabriel push-down is
restricted first to the chosen orbit skeleton and then to the literal
finite-dimensional module categories used by the covering argument.
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

/-- Skeletal push-down is invariant under translation of a linear module. -/
noncomputable def linearModuleOrbitSkeletonPushdownShiftIso
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    (linearModuleOrbitSkeletonPushdown
      (k := k) (C := C) (G := G)).obj (M⟦a⟧) ≅
      (linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := G)).obj M := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  apply ObjectProperty.isoMk
  exact Functor.isoWhiskerLeft
    (deckOrbitRepresentativeFunctor (C := C) (G := G))
    (shiftedOrbitPushdownIso D.core M a)

/-- Finite-dimensional skeletal push-down is invariant under translation. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownShiftIso
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown
      (k := k)).obj (M⟦a⟧) ≅
      (D.finiteDimensionalModuleOrbitSkeletonPushdown
        (k := k)).obj M := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  apply ObjectProperty.isoMk
  let e₁ :=
    (linearModuleOrbitSkeletonPushdown
      (k := k) (C := C) (G := G)).mapIso
        (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) M a)
  let e₂ := D.linearModuleOrbitSkeletonPushdownShiftIso M.obj a
  exact e₁ ≪≫ e₂

/-- Translation invariance of finite push-down transported across an explicit
equality of shift instances. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq_shiftIso
    (H : HasShift C (Additive G))
    (hadd : letI := H
      ∀ b : Additive G, (shiftFunctor C b).Additive)
    (hlinear : letI := H
      ∀ b : Additive G, (shiftFunctor C b).Linear k)
    (hH : H = D.hasShift)
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := H
    letI := hadd
    letI := hlinear
    (D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
      (k := k) H hadd hlinear hH).obj (M⟦a⟧) ≅
      (D.finiteDimensionalModuleOrbitSkeletonPushdown_of_hasShift_eq
        (k := k) H hadd hlinear hH).obj M := by
  cases hH
  letI := D.hasShift
  letI := hadd
  letI := hlinear
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  change
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj (M⟦a⟧) ≅
      (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M
  exact D.finiteDimensionalModuleOrbitSkeletonPushdownShiftIso (k := k) M a

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
