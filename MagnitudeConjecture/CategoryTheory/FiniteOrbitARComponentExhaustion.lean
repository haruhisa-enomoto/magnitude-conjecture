import MagnitudeConjecture.CategoryTheory.FiniteARComponentExhaustion
import MagnitudeConjecture.CategoryTheory.FiniteOrbitInjectiveRadicalComponents
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushedFamily
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownARComponent
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownBoundary
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownDensity
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Exhaustion of a finite pushed Auslander--Reiten component

This file assembles the finite pushed family supplied by local
representation-finiteness into the hypotheses of Auslander's finite-component
exhaustion theorem.  Noninjective members use pushed minimal left
almost-split monomorphisms.  Injective members use the canonical dual-radical
projection.  Projective and injective boundary comparison then turns
component exhaustion into Gabriel push-down density.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

set_option linter.unusedVariables false in
private theorem exists_pushedLeftAlmostSplit
    [HasExt.{max u v}
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
    (hM : Indecomposable M) :
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
    ∀ [hExtDown : HasExt.{max u v}
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)],
      ∃ E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k,
        ∃ f :
          (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj M
            ⟶
          (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj E,
          IsLeftAlmostSplit f := by
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
  intro hExtDown
  letI : HasExt.{max u v}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) := hExtDown
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  by_cases hMinjective : Injective M
  · letI : Injective M := hMinjective
    obtain ⟨X, ⟨e⟩⟩ :=
      indecomposable_injective_iso_finiteDimensionalDualLinearYoneda
        hI hlocal M hM
    let I := finiteDimensionalDualLinearYoneda (k := k) X (hI X)
    let R := finiteDimensionalDualRadicalLinearYoneda
      (k := k) X (hI X)
    let m : I ⟶ R :=
      finiteDimensionalDualLinearYonedaRadicalProjection
        (k := k) X (hI X)
    have hm : IsLeftAlmostSplit (P.map m) :=
      D.finiteDimensionalModuleOrbitSkeletonPushdown_dualRadicalProjection_isLeftAlmostSplit
        (k' := k) hP hI hlocal hfree X
    refine ⟨R, (P.mapIso e).inv ≫ P.map m, ?_⟩
    exact hm.precomp_iso (P.mapIso e).symm
  · letI : EnoughInjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
      finiteDimensionalModuleCategoryEnoughInjectives hI
    obtain ⟨E, m, hmMono, hmAS⟩ :=
      finiteDimensionalModule_exists_mono_leftAlmostSplit_of_locallyRepresentationFinite
        hrep hM hMinjective
    obtain ⟨E', m', hm'AS, hm'Min⟩ :=
      finiteDimensionalModule_exists_leftMinimal_leftAlmostSplit m hmAS
    letI : Mono m' :=
      hm'AS.mono_of_nonsplit_mono m hmAS.not_isSplitMono
    exact ⟨E', P.map m',
      D.finiteDimensionalModuleOrbitSkeletonPushdown_map_isLeftAlmostSplit
        (k := k) hP hI hlocal hfree m' hm'AS hm'Min hM⟩

set_option linter.unusedVariables false in
/-- The finite pushed indecomposable family carries left almost-split maps
whose middle summands remain in that same family. -/
noncomputable def FinitePushedIndecomposableFamily.toFiniteLeftAlmostSplitFamily
    [HasExt.{max u v}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    [IsMulTorsionFree G]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : FinitePushedIndecomposableFamily (k := k) D) :
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
    ∀ [hExtDown : HasExt.{max u v}
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k)],
      FiniteLeftAlmostSplitFamily (k := k)
        (C := DeckOrbitSkeleton C G) := by
  classical
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
  intro hExtDown
  letI : HasExt.{max u v}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) := hExtDown
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let data (i : Fin S.n) := D.exists_pushedLeftAlmostSplit
    (k := k) hP hI hlocal hfree hrep (S.upstairsIndecomposable i)
  let E (i : Fin S.n) := (data i).choose
  let m (i : Fin S.n) := (data i).choose_spec.choose
  have hm (i : Fin S.n) : IsLeftAlmostSplit (m i) :=
    (data i).choose_spec.choose_spec
  let d (i : Fin S.n) := Classical.choice
    (finiteDimensionalModule_finiteIndecomposableDecomposition (E i))
  let label (i : Fin S.n) (t : Fin (d i).n) :=
    (S.covers ((d i).summand t) ((d i).indecomposable t)).choose
  let memberIso (i : Fin S.n) (t : Fin (d i).n) := Classical.choice
    (S.covers ((d i).summand t) ((d i).indecomposable t)).choose_spec
  let targetIso (i : Fin S.n) :
      P.obj (E i) ≅ ⨁ fun t : Fin (d i).n ↦
        FinitePushedIndecomposableFamily.obj D S (label i t) :=
    P.mapIso (d i).isoBiproduct ≪≫
      P.mapBiproduct (d i).summand ≪≫
        biproduct.mapIso (fun t ↦ (memberIso i t).symm)
  exact
    { n := S.n
      obj := FinitePushedIndecomposableFamily.obj D S
      indecomposable := S.downstairsIndecomposable
      middleMultiplicity := fun i ↦ (d i).n
      middleLabel := label
      map := fun i ↦ m i ≫ (targetIso i).hom
      leftAlmostSplit := fun i ↦ (hm i).postcomp_iso (targetIso i) }

/-- Gabriel density for a finite object-orbit quotient of a locally
representation-finite covering category. -/
theorem finiteOrbitPushdownDensity_of_locallyRepresentationFinite
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    FiniteOrbitPushdownDensity.{u, v, v, v, v} (k := k) D := by
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
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hIdown := D.orbitSkeletonDualLinearYonedaFinite (k := k) hI
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  letI : HasExt.{max u v}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  letI : HasExt.{max u v}
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  letI : EnoughInjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    finiteDimensionalModuleCategoryEnoughInjectives hIdown
  let S := D.finitePushedIndecomposableFamily (k := k) hrep
  let A := FinitePushedIndecomposableFamily.toFiniteLeftAlmostSplitFamily
    D (k := k) hP hI hlocal hfree hrep S
  have hinjective :
      ∀ (I : FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k),
        Indecomposable I → Injective I → A.Covers I := by
    intro I hIind hIinj
    letI : Injective I := hIinj
    obtain ⟨M, hMinj, hMind, ⟨eI⟩⟩ :=
      D.exists_injectiveIndecomposable_preimage
        (k := k) hP hI hlocal hfree hIind
    obtain ⟨i, ⟨eM⟩⟩ := S.covers M hMind
    exact ⟨i, ⟨eM ≪≫ eI⟩⟩
  have hprojective :
      ∀ (Q : FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k),
        Indecomposable Q → Projective Q → A.Covers Q := by
    intro Q hQind hQprojective
    letI : Projective Q := hQprojective
    obtain ⟨M, hMprojective, hMind, ⟨eQ⟩⟩ :=
      D.exists_projectiveIndecomposable_preimage
        (k := k) hP hlocal hfree hQind
    obtain ⟨i, ⟨eM⟩⟩ := S.covers M hMind
    exact ⟨i, ⟨eM ≪≫ eQ⟩⟩
  apply D.finiteOrbitPushdownDensity_of_indec_dense
  dsimp only
  intro Y hY
  obtain ⟨i, ⟨eY⟩⟩ :=
    A.covers_all_indecomposables hinjective hprojective Y hY
  exact ⟨S.upstairsObj i, ⟨eY⟩⟩

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
