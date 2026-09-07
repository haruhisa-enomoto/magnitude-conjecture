import MagnitudeConjecture.CategoryTheory.AlmostSplitEssentialImage
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleEnoughInjectives
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleLocalRepresentationFinite
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownAuslanderReiten

/-!
# Auslander--Reiten component closure for finite orbit push-down

The density-free preservation of right and left almost-split maps gives both
local directions of Gabriel's component theorem.  Every irreducible
predecessor of a pushed nonprojective indecomposable is itself pushed; and,
whenever an upstairs indecomposable admits a left almost-split monomorphism,
every irreducible successor of its push-down is pushed as well.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

set_option linter.unusedVariables false in
/-- Gabriel 3.6(b), incoming nonprojective step: if `M` is an upstairs
nonprojective indecomposable, then every downstairs indecomposable with an
irreducible map to the push-down of `M` is the push-down of an upstairs
indecomposable. -/
theorem exists_pushedIndecomposable_of_irreducible_to_pushdown
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    [IsMulTorsionFree G]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : ¬ Projective M) (hMind : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ∀ {Y : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k}
      (hY : Indecomposable Y)
      (f : Y ⟶
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M)
      (hf : IsIrreducibleMorphism f)
      [hExtDown : HasExt.{w}
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)],
        ∃ Z : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
          Indecomposable Z ∧
            Nonempty
              ((D.finiteDimensionalModuleOrbitSkeletonPushdown
                (k := k)).obj Z ≅ Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro Y hY f hf hExtDown
  letI : HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) := hExtDown
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  obtain ⟨Q⟩ :=
    twoStepMinimalFiniteRepresentablePresentation_nonempty hP hlocal M
  obtain ⟨E, i, q, zero, hS, _, hqAS⟩ :=
    Q.exists_stableSocleClass_realization_rightAlmostSplit
      hI hM hMind
  obtain ⟨N, m, hmAS, hmMin⟩ :=
    finiteDimensionalModule_exists_rightMinimal_rightAlmostSplit q hqAS
  have hPmAS : IsRightAlmostSplit (P.map m) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isRightAlmostSplit
      (k := k) hP hI hlocal hfree Q hM hMind m hmAS hmMin
  apply
    MagnitudeConjecture.CategoryTheory.exists_essentialImage_of_irreducible_to_of_map_rightAlmostSplit
      P finiteDimensionalModule_finiteIndecomposableDecomposition
      (fun Z hZ ↦ ?_) m hPmAS hY
      (finiteDimensionalModule_end_isLocalRing k Y hY) f hf
  exact
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) Z hZ
        (D.finiteDimensionalModule_trivialStabilizer (k := k) Z hZ.1)

set_option linter.unusedVariables false in
/-- Gabriel 3.6(b), outgoing noninjective step: suppose an upstairs
indecomposable `M` admits a left almost-split monomorphism.  Then every
downstairs indecomposable receiving an irreducible map from the push-down of
`M` is the push-down of an upstairs indecomposable.  The supplied map need
not already be left minimal. -/
theorem exists_pushedIndecomposable_of_irreducible_from_pushdown
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    [IsMulTorsionFree G]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    {M E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (m : M ⟶ E) [Mono m]
    (hmAS : IsLeftAlmostSplit m) (hMind : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ∀ {Y : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k}
      (hY : Indecomposable Y)
      (f :
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M
          ⟶ Y)
      (hf : IsIrreducibleMorphism f)
      [hExtDown : HasExt.{w}
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)],
        ∃ Z : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
          Indecomposable Z ∧
            Nonempty
              ((D.finiteDimensionalModuleOrbitSkeletonPushdown
                (k := k)).obj Z ≅ Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro Y hY f hf hExtDown
  letI : HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) := hExtDown
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  obtain ⟨E', m', hm'AS, hm'Min⟩ :=
    finiteDimensionalModule_exists_leftMinimal_leftAlmostSplit m hmAS
  letI : Mono m' :=
    hm'AS.mono_of_nonsplit_mono m hmAS.not_isSplitMono
  have hPm'AS : IsLeftAlmostSplit (P.map m') :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isLeftAlmostSplit
      (k := k) hP hI hlocal hfree m' hm'AS hm'Min hMind
  apply
    MagnitudeConjecture.CategoryTheory.exists_essentialImage_of_irreducible_from_of_map_leftAlmostSplit
      P finiteDimensionalModule_finiteIndecomposableDecomposition
      (fun Z hZ ↦ ?_) m' hPm'AS hY
      (finiteDimensionalModule_end_isLocalRing k Y hY) f hf
  exact
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) Z hZ
        (D.finiteDimensionalModule_trivialStabilizer (k := k) Z hZ.1)

set_option linter.unusedVariables false in
/-- Gabriel 3.6(b), outgoing noninjective step under local
representation-finiteness: if `M` is an upstairs noninjective indecomposable,
then every downstairs indecomposable receiving an irreducible map from its
push-down is the push-down of an upstairs indecomposable. -/
theorem exists_pushedIndecomposable_of_irreducible_from_pushdown_of_noninjective
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    [IsMulTorsionFree G]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : ¬ Injective M) (hMind : Indecomposable M) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    ∀ {Y : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k}
      (hY : Indecomposable Y)
      (f :
        (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M
          ⟶ Y)
      (hf : IsIrreducibleMorphism f)
      [hExtDown : HasExt.{w}
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)],
        ∃ Z : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
          Indecomposable Z ∧
            Nonempty
              ((D.finiteDimensionalModuleOrbitSkeletonPushdown
                (k := k)).obj Z ≅ Y) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro Y hY f hf hExtDown
  letI : HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) := hExtDown
  letI : EnoughInjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    finiteDimensionalModuleCategoryEnoughInjectives hI
  obtain ⟨E, m, hmMono, hmAS⟩ :=
    finiteDimensionalModule_exists_mono_leftAlmostSplit_of_locallyRepresentationFinite
      hrep hMind hM
  letI : Mono m := hmMono
  exact
    D.exists_pushedIndecomposable_of_irreducible_from_pushdown
      hP hI hlocal hfree m hmAS hMind hY f hf

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
