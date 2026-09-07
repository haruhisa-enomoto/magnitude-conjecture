import MagnitudeConjecture.CategoryTheory.OrbitPushdownResidualShift
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownReflectsOrbits
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleTrivialStabilizer
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleOrbit

/-!
# Residual freeness after finite orbit push-down

For a normal subgroup of the torsion-free ambient deck group, this file proves
that the residual quotient action has trivial stabilizer on the subgroup
push-down of every indecomposable finite-dimensional module.  Orbit reflection
reduces a residual stabilizer to an ambient stabilizer, while an explicit
restriction comparison identifies subgroup shifts with their ambient shifts.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v uK

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {G : Type v} [Group G] [IsMulTorsionFree G]
variable [MulAction G C] [IsCancelSMul G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Restricting the deck shift to a subgroup does not change translation by
the underlying ambient group element. -/
noncomputable def finiteDimensionalModuleRestrictShiftIso
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (N : Subgroup G) (n : Additive N) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := (D.restrict N).isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := (D.restrict N).finiteDimensionalModuleCategoryHasShift (k := k)
    (shiftFunctor
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) n).obj M ≅
      (shiftFunctor
        (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
        (Additive.ofMul (n.toMul : G))).obj M := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := isLinearModule_stableUnderShift (k := k) (D.restrict N).core
  letI := linearModuleCategoryHasShift (k := k) (D.restrict N).core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI := (D.restrict N).isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := (D.restrict N).finiteDimensionalModuleCategoryHasShift (k := k)
  let a := Additive.ofMul (n.toMul : G)
  let J : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k ⥤
      (C ⥤ ModuleCat.{v} k) :=
    (IsFiniteDimensionalModule (C := C) k).ι ⋙
      (IsLinearModule (C := C) k).ι
  let eNfd := (D.restrict N).finiteDimensionalModuleShiftUnderlyingIso
    (k := k) M n
  let eNlinear := (IsLinearModule (C := C) k).ι.mapIso eNfd
  let eNpre := linearModuleShiftUnderlyingIso
    (k := k) (D.restrict N).core M.obj n
  let eN : J.obj ((shiftFunctor
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) n).obj M) ≅
      (D.restrict N).core.F (-n) ⋙ M.obj.obj :=
    eNlinear ≪≫ eNpre
  let eGfd := D.finiteDimensionalModuleShiftUnderlyingIso
    (k := k) M a
  let eGlinear := (IsLinearModule (C := C) k).ι.mapIso eGfd
  let eGpre := linearModuleShiftUnderlyingIso
    (k := k) D.core M.obj a
  let eG : J.obj ((shiftFunctor
      (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) a).obj M) ≅
      D.core.F (-a) ⋙ M.obj.obj :=
    eGlinear ≪≫ eGpre
  have hfunctor : (D.restrict N).core.F (-n) = D.core.F (-a) := by
    rfl
  exact J.preimageIso (eN ≪≫
    Functor.isoWhiskerRight (eqToIso hfunctor) M.obj.obj ≪≫ eG.symm)

/-- The quotient group acts freely on the isomorphism class of the subgroup
push-down of a nonzero indecomposable finite-dimensional module. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdown_residual_trivialStabilizer
    (M : FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
    (hM : Indecomposable M) (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := isLinearModule_stableUnderShift (k := k) (D.restrict N).core
    letI := linearModuleCategoryHasShift (k := k) (D.restrict N).core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := (D.restrict N).isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := (D.restrict N).finiteDimensionalModuleCategoryHasShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    letI := (D.deckOrbitResidualCoherentDeckShift N
      ).isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := (D.deckOrbitResidualCoherentDeckShift N
      ).finiteDimensionalModuleCategoryHasShift (k := k)
    ∀ q : Additive (G ⧸ N),
      Nonempty
        (((D.restrict N).finiteDimensionalModuleOrbitSkeletonPushdown
            (k := k)).obj M ≅
          (((D.restrict N).finiteDimensionalModuleOrbitSkeletonPushdown
            (k := k)).obj M)⟦q⟧) →
        q = 0 := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := isLinearModule_stableUnderShift (k := k) (D.restrict N).core
  letI := linearModuleCategoryHasShift (k := k) (D.restrict N).core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI := (D.restrict N).isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := (D.restrict N).finiteDimensionalModuleCategoryHasShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  let R := D.deckOrbitResidualCoherentDeckShift N
  letI := R.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := R.finiteDimensionalModuleCategoryHasShift (k := k)
  intro q hq
  let g : G := normalQuotientRepresentative N (-q).toMul
  let a : Additive G := -Additive.ofMul g
  let P := (D.restrict N).finiteDimensionalModuleOrbitSkeletonPushdown
    (k := k)
  let eResidual :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownResidualShiftIso M N q
  have hpush : Nonempty (P.obj M ≅ P.obj (M⟦a⟧)) := by
    obtain ⟨e⟩ := hq
    exact ⟨e ≪≫ eResidual.symm⟩
  have hMa : Indecomposable (M⟦a⟧) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      (shiftFunctor
        (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k) a)
      M).mpr hM
  have hNtrivial : ∀ n : Additive N,
      Nonempty (M ≅ M⟦n⟧) → n = 0 :=
    (D.restrict N).finiteDimensionalModule_trivialStabilizer
      (k := k) M hM.1
  obtain ⟨n, hn⟩ :=
    (D.restrict N).exists_shift_iso_of_pushdown_iso
      (k := k) M (M⟦a⟧) hM hMa hNtrivial hpush
  obtain ⟨e⟩ := hn
  let b : Additive G := Additive.ofMul (n.toMul : G)
  let eRestr := D.finiteDimensionalModuleRestrictShiftIso
    (k := k) (M⟦a⟧) N n
  let eAdd := (shiftFunctorAdd
    (FiniteDimensionalModuleCategory.{u, v, uK, v} (C := C) k)
      a b).symm.app M
  have hab : a + b = 0 :=
    D.finiteDimensionalModule_trivialStabilizer (k := k) M hM.1
      (a + b) ⟨e ≪≫ eRestr ≪≫ eAdd⟩
  have hg : g = (n.toMul : G) := by
    have hmul := congrArg Additive.toMul hab
    exact eq_of_inv_mul_eq_one (by simpa [a, b] using hmul)
  apply Additive.toMul.injective
  have hrepresentative : (g : G ⧸ N) = (-q).toMul :=
    normalQuotientRepresentative_mk N (-q).toMul
  have hneg : (-q).toMul = 1 := by
    rw [← hrepresentative, hg]
    exact (QuotientGroup.eq_one_iff _).mpr n.toMul.property
  simpa using inv_eq_one.mp hneg

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
