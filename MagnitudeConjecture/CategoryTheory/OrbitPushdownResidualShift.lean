import MagnitudeConjecture.CategoryTheory.OrbitPushdownNormalTranslate
import MagnitudeConjecture.CategoryTheory.DeckOrbitResidualLinear
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdown

/-!
# Residual shift and subgroup push-down

For a normal subgroup `N ≤ G`, this file identifies residual translation of
an `N`-pushed-down module with subgroup push-down of the corresponding ambient
translate.  The final comparison restricts the construction to
finite-dimensional modules.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Pushing down translation by `g⁻¹` along a normal subgroup is strict
normal precomposition by `g` on the chosen orbit skeleton. -/
noncomputable def linearModuleOrbitSkeletonPushdownNormalTranslateIso
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    (linearModuleOrbitSkeletonPushdown
      (k := k) (C := C) (G := N)).obj
        (M⟦-Additive.ofMul g⟧) ≅
      ⟨D.deckOrbitNormalTranslateFunctor N g ⋙
          ((linearModuleOrbitSkeletonPushdown
            (k := k) (C := C) (G := N)).obj M).obj,
        inferInstance, inferInstance⟩ := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  apply ObjectProperty.isoMk
  let iN := deckOrbitRepresentativeFunctor (C := C) (G := N)
  let e₁ := Functor.isoWhiskerLeft iN
    (D.orbitPushdownNormalTranslateIso M N (-Additive.ofMul g))
  let e₂ := Functor.isoWhiskerRight
    (D.deckOrbitNormalTranslateRepresentativeNatIso N g)
    (orbitPushdown (A := Additive N) M.obj)
  refine e₁ ≪≫ ?_
  rw [show - -Additive.ofMul g = Additive.ofMul g by simp]
  change iN ⋙ D.shiftOrbitNormalTranslateFunctor N g ⋙
      orbitPushdown (A := Additive N) M.obj ≅
    D.deckOrbitNormalTranslateFunctor N g ⋙
      ((linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := N)).obj M).obj
  exact
    (Functor.associator iN
        (D.shiftOrbitNormalTranslateFunctor N g)
        (orbitPushdown (A := Additive N) M.obj)).symm ≪≫
      e₂.symm ≪≫
      Functor.associator
        (D.deckOrbitNormalTranslateFunctor N g) iN
        (orbitPushdown (A := Additive N) M.obj)

/-- Residual translation of an `N`-push-down is the push-down of the ambient
translate by the inverse chosen representative. -/
noncomputable def linearModuleOrbitSkeletonPushdownResidualShiftIso
    (M : LinearModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (q : Additive (G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI : HasShift
        (LinearModuleCategory.{u, max v w, uK, max w uM}
          (C := DeckOrbitSkeleton C N) k)
        (Additive (G ⧸ N)) :=
      D.deckOrbitResidualLinearModuleHasShift N
    (linearModuleOrbitSkeletonPushdown
      (k := k) (C := C) (G := N)).obj
        (M⟦-Additive.ofMul
          (normalQuotientRepresentative N (-q).toMul)⟧) ≅
      ((linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := N)).obj M)⟦q⟧ := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI : HasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C N) k)
      (Additive (G ⧸ N)) :=
    D.deckOrbitResidualLinearModuleHasShift N
  let g := normalQuotientRepresentative N (-q).toMul
  let P := linearModuleOrbitSkeletonPushdown
    (k := k) (C := C) (G := N)
  let e₁ := D.linearModuleOrbitSkeletonPushdownNormalTranslateIso M N g
  let e₂ : (P.obj M)⟦q⟧ ≅
      ⟨D.deckOrbitNormalTranslateFunctor N g ⋙ (P.obj M).obj,
        inferInstance, inferInstance⟩ :=
    by
      apply ObjectProperty.isoMk
      exact D.deckOrbitResidualLinearModuleShiftUnderlyingIso N (P.obj M) q
  exact e₁ ≪≫ e₂.symm

end MagnitudeConjecture.CoveringHom.CoherentDeckShift

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The residual-shift comparison restricted to finite-dimensional modules. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownResidualShiftIso
    (M : FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)
    (N : Subgroup G) [N.Normal] (q : Additive (G ⧸ N)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    letI : HasShift
        (LinearModuleCategory.{u, max v w, uK, max w uM}
          (C := DeckOrbitSkeleton C N) k)
        (Additive (G ⧸ N)) :=
      D.deckOrbitResidualLinearModuleHasShift N
    letI := (D.deckOrbitResidualCoherentDeckShift N
      ).isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := (D.deckOrbitResidualCoherentDeckShift N
      ).finiteDimensionalModuleCategoryHasShift (k := k)
    ((D.restrict N).finiteDimensionalModuleOrbitSkeletonPushdown
      (k := k)).obj
        (M⟦-Additive.ofMul
          (normalQuotientRepresentative N (-q).toMul)⟧) ≅
      (((D.restrict N).finiteDimensionalModuleOrbitSkeletonPushdown
        (k := k)).obj M)⟦q⟧ := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  letI : HasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C N) k)
      (Additive (G ⧸ N)) :=
    D.deckOrbitResidualLinearModuleHasShift N
  let R := D.deckOrbitResidualCoherentDeckShift N
  letI := R.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := R.finiteDimensionalModuleCategoryHasShift (k := k)
  let g := normalQuotientRepresentative N (-q).toMul
  let P := linearModuleOrbitSkeletonPushdown
    (k := k) (C := C) (G := N)
  let PF := (D.restrict N).finiteDimensionalModuleOrbitSkeletonPushdown
    (k := k)
  apply ObjectProperty.isoMk
  let e₀ := P.mapIso
    (D.finiteDimensionalModuleShiftUnderlyingIso (k := k) M
      (-Additive.ofMul g))
  let e₁ := D.linearModuleOrbitSkeletonPushdownResidualShiftIso M.obj N q
  let e₂ := R.finiteDimensionalModuleShiftUnderlyingIso
    (k := k) (PF.obj M) q
  exact e₀ ≪≫ e₁ ≪≫ e₂.symm

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
