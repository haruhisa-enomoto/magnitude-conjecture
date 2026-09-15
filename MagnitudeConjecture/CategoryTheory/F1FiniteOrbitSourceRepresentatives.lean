import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushedFamily
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownReflectsOrbits
import MagnitudeConjecture.CategoryTheory.F1FiniteOrbitSurplus
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteType
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleControlWindow
import MagnitudeConjecture.CategoryTheory.FiniteSkeletonIntrinsicLocalDensity
import MagnitudeConjecture.CategoryTheory.IncomingHomLocalDensity
import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalChangeSum

/-!
# Source representatives for the frozen finite orbit average

The finite orbit skeleton downstairs can be lifted to one indecomposable
upstairs module for each of its labels.  Push-down reflection then proves that
these lifts are representatives for the deck-shift orbits of all upstairs
indecomposables.  This is the finite source family used by the F1 averaging
identity; it does not introduce a finite-index subgroup.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

open MagnitudeConjecture.ObjectDeletion

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]

/- A duplicate-free presentation of a finite module family, obtained by
   retaining one chosen representative of each represented isomorphism class.
   The frozen incidence bridge uses this to turn occurrence labels into a
   genuine finite target family. -/
noncomputable def isoClassFamily
    (W : FiniteIndecomposableModuleFamily (k:=k) (C:=C)) :
    FiniteIndecomposableModuleFamily (k:=k) (C:=C) := by
  let e : Fin (Fintype.card W.IsoClass) ≃ W.IsoClass := (Fintype.equivFin _).symm
  let n := Fintype.card (W.IsoClass)
  refine
    { n := n
      obj := fun j => W.obj (Quotient.out (e j))
      indecomposable := fun j => W.indecomposable (Quotient.out (e j)) }

theorem isoClassFamily_mem
    (W : FiniteIndecomposableModuleFamily (k:=k) (C:=C))
    (i : Fin (isoClassFamily W).n) :
    (isoClassFamily W).obj i ∈ W.isoClosure := by
  refine ⟨Quotient.out ((Fintype.equivFin W.IsoClass).symm i), ?_⟩
  exact ⟨Iso.refl _⟩

theorem isoClassFamily_pairwise
    (W : FiniteIndecomposableModuleFamily (k:=k) (C:=C))
    {i j : Fin (isoClassFamily W).n}
    (h : Nonempty ((isoClassFamily W).obj i ≅ (isoClassFamily W).obj j)) : i = j := by
  have hij : ((Fintype.equivFin W.IsoClass).symm i) =
      ((Fintype.equivFin W.IsoClass).symm j) := by
    rw [← Quotient.out_eq ((Fintype.equivFin W.IsoClass).symm i),
      ← Quotient.out_eq ((Fintype.equivFin W.IsoClass).symm j)]
    apply Quotient.sound
    obtain ⟨e⟩ := h
    exact ⟨e⟩
  exact (Fintype.equivFin W.IsoClass).symm.injective hij

theorem isoClassFamily_isoClosure_eq
    (W : FiniteIndecomposableModuleFamily (k:=k) (C:=C)) :
    (isoClassFamily W).isoClosure = W.isoClosure := by
  apply Set.Subset.antisymm
  · intro M hM
    obtain ⟨i, ⟨e⟩⟩ := hM
    obtain ⟨j, ⟨ej⟩⟩ := isoClassFamily_mem W i
    exact ⟨j, ⟨ej.trans e⟩⟩
  · intro M hM
    obtain ⟨i, ⟨e⟩⟩ := hM
    let q : W.IsoClass := Quotient.mk W.isoSetoid i
    let j := (Fintype.equivFin W.IsoClass) q
    refine ⟨j, ?_⟩
    change Nonempty (W.obj (Quotient.out ((Fintype.equivFin W.IsoClass).symm j)) ≅ M)
    rw [show (Fintype.equivFin W.IsoClass).symm j = q by simp [j]]
    have hrel : W.obj (Quotient.out q) ≅ W.obj i :=
      Classical.choice (Quotient.exact (Quotient.out_eq q))
    exact ⟨hrel.trans e⟩
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The finite downstairs orbit skeleton used to choose one lift per target
isomorphism class. -/
noncomputable abbrev finiteOrbitTargetSkeleton
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI : Category (ShiftOrbitCategory C (Additive G)) :=
      ShiftOrbitCategory.category
    letI : Linear k (ShiftOrbitCategory C (Additive G)) :=
      inferInstance
    letI : Category (DeckOrbitSkeleton C G) :=
      InducedCategory.instCategory
    letI : Preadditive (DeckOrbitSkeleton C G) :=
      Preadditive.inducedCategory _
    letI : Linear k (DeckOrbitSkeleton C G) :=
      Linear.inducedCategory _
    MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := DeckOrbitSkeleton C G) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Category (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Linear k (ShiftOrbitCategory C (Additive G)) :=
    inferInstance
  letI : Category (DeckOrbitSkeleton C G) :=
    InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) :=
    Linear.inducedCategory _
  exact D.finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfree hrep

/-- A chosen upstairs lift of each target-skeleton module. -/
noncomputable def finiteOrbitSourceLift
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (j : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI : Category (ShiftOrbitCategory C (Additive G)) :=
        ShiftOrbitCategory.category
      letI : Linear k (ShiftOrbitCategory C (Additive G)) := inferInstance
      letI : Category (DeckOrbitSkeleton C G) := InducedCategory.instCategory
      letI : Preadditive (DeckOrbitSkeleton C G) :=
        Preadditive.inducedCategory _
      letI : Linear k (DeckOrbitSkeleton C G) := Linear.inducedCategory _
      Fin (D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep).n) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Category (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Linear k (ShiftOrbitCategory C (Additive G)) :=
    inferInstance
  letI : Category (DeckOrbitSkeleton C G) :=
    InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) :=
    Linear.inducedCategory _
  letI : Category (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Category (DeckOrbitSkeleton C G) :=
    InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) :=
    Linear.inducedCategory _
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  let T := D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep
  let PF := D.finitePushedIndecomposableFamily hrep
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown.{u, v, v, v, v} (k := k)
  letI : P.Faithful := D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful
    (k := k)
  let hDensity := D.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
    (k := k) hP hI hlocal hfree hrep
  let X := Classical.choose (hDensity.essSurj.mem_essImage (T.obj j))
  let eX : P.obj X ≅ T.obj j :=
    Classical.choice (Classical.choose_spec
      (hDensity.essSurj.mem_essImage (T.obj j)))
  have hPX : Indecomposable (P.obj X) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eX).2
      (T.indecomposable j)
  have hX : Indecomposable X :=
    MagnitudeConjecture.indecomposable_of_faithful_additive P X hPX
  exact PF.upstairsObj (Classical.choose (PF.covers X hX))

/-- The chosen lift is indecomposable and its push-down is the target module. -/
noncomputable def finiteOrbitSourceLiftPushdownIso
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (j : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI : Category (ShiftOrbitCategory C (Additive G)) :=
        ShiftOrbitCategory.category
      letI : Linear k (ShiftOrbitCategory C (Additive G)) := inferInstance
      letI : Category (DeckOrbitSkeleton C G) := InducedCategory.instCategory
      letI : Preadditive (DeckOrbitSkeleton C G) :=
        Preadditive.inducedCategory _
      letI : Linear k (DeckOrbitSkeleton C G) := Linear.inducedCategory _
      Fin (D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep).n) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI : Category (ShiftOrbitCategory C (Additive G)) :=
      ShiftOrbitCategory.category
    letI : Linear k (ShiftOrbitCategory C (Additive G)) := inferInstance
    letI : Category (DeckOrbitSkeleton C G) := InducedCategory.instCategory
    letI : Preadditive (DeckOrbitSkeleton C G) :=
      Preadditive.inducedCategory _
    letI : Linear k (DeckOrbitSkeleton C G) := Linear.inducedCategory _
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        (D.finiteOrbitSourceLift hP hI hlocal hfree hrep j) ≅
      (D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep).obj j := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Category (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Linear k (ShiftOrbitCategory C (Additive G)) := inferInstance
  letI : Category (DeckOrbitSkeleton C G) := InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) := Linear.inducedCategory _
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  let T := D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep
  let PF := D.finitePushedIndecomposableFamily hrep
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  letI : P.Faithful := D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful
    (k := k)
  let hDensity := D.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
    (k := k) hP hI hlocal hfree hrep
  let X := Classical.choose (hDensity.essSurj.mem_essImage (T.obj j))
  let eX : P.obj X ≅ T.obj j :=
    Classical.choice (Classical.choose_spec
      (hDensity.essSurj.mem_essImage (T.obj j)))
  have hPX : Indecomposable (P.obj X) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eX).2
      (T.indecomposable j)
  have hX : Indecomposable X :=
    MagnitudeConjecture.indecomposable_of_faithful_additive P X hPX
  let i := Classical.choose (PF.covers X hX)
  let ePF : P.obj (PF.upstairsObj i) ≅ P.obj X :=
    Classical.choice (Classical.choose_spec (PF.covers X hX))
  simpa only [finiteOrbitSourceLift, i] using
    ePF.trans eX

noncomputable def finiteOrbitSourceRepresentativeFamily
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    MagnitudeConjecture.CoveringHom.FiniteIndecomposableModuleFamily (k := k) (C := C) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Category (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Linear k (ShiftOrbitCategory C (Additive G)) := inferInstance
  letI : Category (DeckOrbitSkeleton C G) := InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) := Linear.inducedCategory _
  refine
    { n := (D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep).n
      obj := D.finiteOrbitSourceLift hP hI hlocal hfree hrep
      indecomposable := ?_ }
  intro j
  let T := D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep
  let PF := D.finitePushedIndecomposableFamily hrep
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  letI : P.Faithful := D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful
    (k := k)
  let hDensity := D.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
    (k := k) hP hI hlocal hfree hrep
  let X := Classical.choose (hDensity.essSurj.mem_essImage (T.obj j))
  let eX : P.obj X ≅ T.obj j :=
    Classical.choice (Classical.choose_spec
      (hDensity.essSurj.mem_essImage (T.obj j)))
  have hPX : Indecomposable (P.obj X) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eX).2
      (T.indecomposable j)
  have hX : Indecomposable X :=
    MagnitudeConjecture.indecomposable_of_faithful_additive P X hPX
  exact PF.upstairsIndecomposable (Classical.choose (PF.covers X hX))

/- The chosen family meets every source indecomposable up to a deck shift.
This is the source-side completeness statement needed to replace the old
finite-index residual tower in the frozen average. -/
theorem finiteOrbitSourceRepresentativeFamily_covers
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
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
    ∃ i : Fin
        (finiteOrbitSourceRepresentativeFamily (k := k) D hP hI hlocal hfree hrep).n,
      ∃ a : Additive G, Nonempty
        (M ≅
          (finiteOrbitSourceRepresentativeFamily
            (k := k) D hP hI hlocal hfree hrep).obj i⟦a⟧) := by
  classical
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : Category (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Linear k (ShiftOrbitCategory C (Additive G)) := inferInstance
  letI : Category (DeckOrbitSkeleton C G) := InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) := Linear.inducedCategory _
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let T := D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep
  let F := finiteOrbitSourceRepresentativeFamily
    (k := k) D hP hI hlocal hfree hrep
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  have htrivial : ∀ a : Additive G, Nonempty (M ≅ M⟦a⟧) → a = 0 := by
    exact D.finiteDimensionalModule_trivialStabilizer (k := k) M hM.1
  have hPM : Indecomposable (P.obj M) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) M hM htrivial
  obtain ⟨j, ⟨eM⟩⟩ := T.complete (P.obj M) hPM
  let eF : P.obj (F.obj j) ≅ T.obj j :=
    finiteOrbitSourceLiftPushdownIso
      (k := k) D hP hI hlocal hfree hrep j
  have hFM : P.obj M ≅ P.obj (F.obj j) := eM.trans eF.symm
  obtain ⟨a, ⟨e⟩⟩ :=
    D.exists_shift_iso_of_pushdown_iso (k := k) M (F.obj j) hM
      (F.indecomposable j) htrivial ⟨hFM⟩
  exact ⟨j, a, ⟨e⟩⟩

/- The source representatives recover the finite orbit surplus by intrinsic
local-density transport.  This is the numerical endpoint identity before the
deletion-order incidence argument is applied. -/
theorem finiteOrbitSourceRepresentativeFamily_sum_localDensity_eq_finiteOrbitSurplus
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    letI : Category (ShiftOrbitCategory C (Additive G)) :=
      ShiftOrbitCategory.category
    letI : Linear k (ShiftOrbitCategory C (Additive G)) := inferInstance
    letI : Category (DeckOrbitSkeleton C G) := InducedCategory.instCategory
    letI : Preadditive (DeckOrbitSkeleton C G) :=
      Preadditive.inducedCategory _
    letI : Linear k (DeckOrbitSkeleton C G) := Linear.inducedCategory _
    let T := D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep
    let F := finiteOrbitSourceRepresentativeFamily
      (k := k) D hP hI hlocal hfree hrep
    (∑ i : Fin F.n,
      finiteModuleLocalDensity hrep (F.obj i) (F.indecomposable i)) =
      D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep := by
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
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI : Category (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Linear k (ShiftOrbitCategory C (Additive G)) := inferInstance
  letI : Category (DeckOrbitSkeleton C G) := InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) := Linear.inducedCategory _
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let T := D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep
  let F := finiteOrbitSourceRepresentativeFamily
    (k := k) D hP hI hlocal hfree hrep
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown.{u, v, v, v, v} (k := k)
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  let hDown := T.isLocallyRepresentationFinite
  have hsumT :
      (∑ j : Fin T.n,
        finiteModuleLocalDensity hDown (T.obj j) (T.indecomposable j)) =
        D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep := by
    simpa only [finiteOrbitSurplus, T] using
      T.sum_finiteModuleLocalDensity_eq_surplus hDown
  have hterm : ∀ j : Fin T.n,
      finiteModuleLocalDensity hrep (F.obj j) (F.indecomposable j) =
        finiteModuleLocalDensity hDown (T.obj j) (T.indecomposable j) := by
    intro j
    let eF := finiteOrbitSourceLiftPushdownIso
      (k := k) D hP hI hlocal hfree hrep j
    have hPF := D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) (F.obj j) (F.indecomposable j)
      (D.finiteDimensionalModule_trivialStabilizer
        (k := k) (F.obj j) (F.indecomposable j).1)
    have hlocalPush := D.finiteDimensionalModuleOrbitSkeletonPushdown_localDensity_eq
      (k := k) hP hI hlocal hfree hrep (F.obj j) (F.indecomposable j)
    have hiso := finiteModuleLocalDensity_eq_of_iso hDown hPF
      (T.indecomposable j) eF
    exact hlocalPush hDown hPF |>.symm.trans hiso
  calc
    ∑ i : Fin F.n,
        finiteModuleLocalDensity hrep (F.obj i) (F.indecomposable i) =
      ∑ j : Fin T.n,
        finiteModuleLocalDensity hDown (T.obj j) (T.indecomposable j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j
    _ = D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep := hsumT

end MagnitudeConjecture.CoveringHom.CoherentDeckShift

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

open MagnitudeConjecture.ObjectDeletion

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Distinct target-skeleton labels cannot have source lifts related by a deck
shift.  This is the injectivity half of the source-orbit representative
certificate used by the frozen occurrence reindexing. -/
theorem finiteOrbitSourceRepresentativeFamily_no_shift_iso
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (i j : Fin
      (finiteOrbitSourceRepresentativeFamily (k := k) D hP hI hlocal hfree hrep).n)
    (a : Additive G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    ∀ e : (finiteOrbitSourceRepresentativeFamily (k := k) D hP hI hlocal hfree hrep).obj i ≅
      ((finiteOrbitSourceRepresentativeFamily (k := k) D hP hI hlocal hfree hrep).obj j)⟦a⟧,
      i = j := by
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
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  intro e
  letI : Category (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Linear k (ShiftOrbitCategory C (Additive G)) := inferInstance
  letI : Category (DeckOrbitSkeleton C G) := InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) := Linear.inducedCategory _
  let T := D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep
  let F := finiteOrbitSourceRepresentativeFamily
    (k := k) D hP hI hlocal hfree hrep
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  letI : P.Faithful := D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful
    (k := k)
  have hFi := finiteOrbitSourceLiftPushdownIso
    (k := k) D hP hI hlocal hfree hrep i
  have hFj := finiteOrbitSourceLiftPushdownIso
    (k := k) D hP hI hlocal hfree hrep j
  have hpush : P.obj (F.obj i) ≅ P.obj (F.obj j) := by
    exact (P.mapIso e).trans
      (finiteDimensionalModuleOrbitSkeletonPushdownShiftIso
        (k := k) D (F.obj j) a)
  have htarget : T.obj i ≅ T.obj j := by
    exact hFi.symm.trans (hpush.trans hFj)
  apply T.skeletal
  exact ⟨htarget⟩

/-- The dependency support attached to a source representative.  It is the
finite incoming-Hom support from the locality package, specialized to the
chosen orbit family. -/
noncomputable def finiteOrbitSourceRepresentativeDependencySupport
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (i : Fin
      (finiteOrbitSourceRepresentativeFamily (k := k) D hP hI hlocal hfree hrep).n) :
    Set C :=
  finiteIncomingHomDependencySupport (k := k) C hrep
    ((finiteOrbitSourceRepresentativeFamily
      (k := k) D hP hI hlocal hfree hrep).obj i)

theorem finiteOrbitSourceRepresentativeDependencySupport_finite
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (i : Fin
      (finiteOrbitSourceRepresentativeFamily (k := k) D hP hI hlocal hfree hrep).n) :
    (finiteOrbitSourceRepresentativeDependencySupport
      (k := k) D hP hI hlocal hfree hrep i).Finite := by
  exact finiteIncomingHomDependencySupport_finite
    (k := k) C hrep
      ((finiteOrbitSourceRepresentativeFamily
        (k := k) D hP hI hlocal hfree hrep).obj i)

/- The finitely many chosen source representatives have a single finite
   dependency envelope.  The averaging argument later restricts this envelope
   to the translates that can meet a prescribed lift of the deleted object. -/
noncomputable def finiteOrbitSourceRepresentativeDependencySupportUnion
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) : Set C :=
  ⋃ i : Fin (finiteOrbitSourceRepresentativeFamily
      (k := k) D hP hI hlocal hfree hrep).n,
    finiteOrbitSourceRepresentativeDependencySupport
      (k := k) D hP hI hlocal hfree hrep i

theorem finiteOrbitSourceRepresentativeDependencySupportUnion_finite
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) :
    (finiteOrbitSourceRepresentativeDependencySupportUnion
      (k := k) D hP hI hlocal hfree hrep).Finite := by
  classical
  unfold finiteOrbitSourceRepresentativeDependencySupportUnion
  exact Set.finite_iUnion fun i ↦
    finiteOrbitSourceRepresentativeDependencySupport_finite
      (k := k) D hP hI hlocal hfree hrep i

theorem finiteOrbitSourceRepresentative_support_subset_dependency
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (i : Fin
      (finiteOrbitSourceRepresentativeFamily (k := k) D hP hI hlocal hfree hrep).n) :
    moduleSupport k
        ((finiteOrbitSourceRepresentativeFamily
          (k := k) D hP hI hlocal hfree hrep).obj i).obj.obj ⊆
      finiteOrbitSourceRepresentativeDependencySupport
        (k := k) D hP hI hlocal hfree hrep i := by
  exact finiteIncomingHom_endpoint_support_subset_dependency
    (k := k) C hrep
      ((finiteOrbitSourceRepresentativeFamily
        (k := k) D hP hI hlocal hfree hrep).obj i)

theorem finiteOrbitSourceRepresentative_minimalSinkSource_support_subset_dependency
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (i : Fin
      (finiteOrbitSourceRepresentativeFamily (k := k) D hP hI hlocal hfree hrep).n) :
    moduleSupport k
        (finiteModuleMinimalSinkData
          hrep ((finiteOrbitSourceRepresentativeFamily
            (k := k) D hP hI hlocal hfree hrep).obj i)
          ((finiteOrbitSourceRepresentativeFamily
            (k := k) D hP hI hlocal hfree hrep).indecomposable i)).source.obj.obj ⊆
      finiteOrbitSourceRepresentativeDependencySupport
        (k := k) D hP hI hlocal hfree hrep i := by
  exact finiteIncomingHom_minimalSinkSource_support_subset_dependency
    (k := k) C hrep
      ((finiteOrbitSourceRepresentativeFamily
        (k := k) D hP hI hlocal hfree hrep).obj i)
      ((finiteOrbitSourceRepresentativeFamily
        (k := k) D hP hI hlocal hfree hrep).indecomposable i)

/- A finite family satisfying source-orbit coverage and no-shift uniqueness has
   the same density sum as the canonical orbit family.  This is the generic
   reindexing principle used by the frozen finite-support endpoint, and keeps
   the endpoint independent of any residual finite quotient. -/
set_option maxHeartbeats 4000000 in
theorem finiteOrbitSourceFamily_sum_localDensity_eq_finiteOrbitSurplus_of_covers
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hcover : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
      ∀ (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
        Indecomposable M → ∃ i : Fin W.n, ∃ a : Additive G,
          Nonempty (M ≅ W.obj i⟦a⟧))
    (hnostab : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
      ∀ i : Fin W.n, ∀ a : Additive G,
        Nonempty (W.obj i ≅ W.obj i⟦a⟧) → a = 0)
    (hnoiso : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
      ∀ i j : Fin W.n, ∀ a : Additive G,
        Nonempty (W.obj i ≅ W.obj j⟦a⟧) → i = j) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    (∑ i : Fin W.n,
      finiteModuleLocalDensity hrep (W.obj i) (W.indecomposable i)) =
      D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep := by
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
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI : Category (ShiftOrbitCategory C (Additive G)) :=
    ShiftOrbitCategory.category
  letI : Linear k (ShiftOrbitCategory C (Additive G)) := inferInstance
  letI : Category (DeckOrbitSkeleton C G) := InducedCategory.instCategory
  letI : Preadditive (DeckOrbitSkeleton C G) :=
    Preadditive.inducedCategory _
  letI : Linear k (DeckOrbitSkeleton C G) := Linear.inducedCategory _
  let T := D.finiteOrbitTargetSkeleton hP hI hlocal hfree hrep
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
  let hDown := T.isLocallyRepresentationFinite
  letI : P.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful (k := k)
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  let φ : Fin W.n → Fin T.n := fun i =>
    Classical.choose (T.complete (P.obj (W.obj i)) (by
      exact D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
        (k := k) (W.obj i) (W.indecomposable i) (hnostab i)))
  have hφsurj : Function.Surjective φ := by
    intro j
    let hDensity := D.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
      (k := k) hP hI hlocal hfree hrep
    obtain ⟨M, ⟨eM⟩⟩ := hDensity.essSurj.mem_essImage (T.obj j)
    have hPM : Indecomposable (P.obj M) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eM).2
        (T.indecomposable j)
    have hM : Indecomposable M :=
      MagnitudeConjecture.indecomposable_of_faithful_additive P M hPM
    obtain ⟨i, a, ⟨e⟩⟩ := hcover M hM
    have hWi := D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) (W.obj i) (W.indecomposable i) (hnostab i)
    have hφ : φ i = j := by
      apply T.skeletal
      let eφ := Classical.choice
        (Classical.choose_spec (T.complete (P.obj (W.obj i)) hWi))
      exact ⟨eφ.symm ≪≫
        (finiteDimensionalModuleOrbitSkeletonPushdownShiftIso
          (k := k) D (W.obj i) a).symm ≪≫
        (P.mapIso e).symm ≪≫ eM⟩
    exact ⟨i, hφ⟩
  have hφinj : Function.Injective φ := by
    intro i j hij
    have hi := D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) (W.obj i) (W.indecomposable i) (hnostab i)
    have hj := D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) (W.obj j) (W.indecomposable j) (hnostab j)
    let ei := Classical.choice
      (Classical.choose_spec (T.complete (P.obj (W.obj i)) hi))
    let ej := Classical.choice
      (Classical.choose_spec (T.complete (P.obj (W.obj j)) hj))
    have hp : P.obj (W.obj i) ≅ P.obj (W.obj j) :=
      ei.trans ((eqToIso (congrArg T.obj hij)).trans ej.symm)
    obtain ⟨a, ⟨e⟩⟩ := D.exists_shift_iso_of_pushdown_iso
      (k := k) (W.obj i) (W.obj j) (W.indecomposable i)
      (W.indecomposable j) (hnostab i) ⟨hp⟩
    exact hnoiso i j a ⟨e⟩
  let eFin : Fin W.n ≃ Fin T.n := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hterm : ∀ i : Fin W.n,
      finiteModuleLocalDensity hrep (W.obj i) (W.indecomposable i) =
        finiteModuleLocalDensity hDown (T.obj (eFin i))
          (T.indecomposable (eFin i)) := by
    intro i
    have hi := D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_trivial_stabilizer
      (k := k) (W.obj i) (W.indecomposable i) (hnostab i)
    let ei := Classical.choice
      (Classical.choose_spec (T.complete (P.obj (W.obj i)) hi))
    have hpush := D.finiteDimensionalModuleOrbitSkeletonPushdown_localDensity_eq
      (k := k) hP hI hlocal hfree hrep (W.obj i) (W.indecomposable i)
    have hiso := finiteModuleLocalDensity_eq_of_iso hDown hi
      (T.indecomposable (eFin i)) ei
    exact hpush hDown hi |>.symm.trans hiso
  have hsum :
      (∑ i : Fin W.n,
        finiteModuleLocalDensity hrep (W.obj i) (W.indecomposable i)) =
        ∑ j : Fin T.n,
          finiteModuleLocalDensity hDown (T.obj j) (T.indecomposable j) := by
    calc
      _ = ∑ i : Fin W.n,
          finiteModuleLocalDensity hDown (T.obj (eFin i))
            (T.indecomposable (eFin i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hterm i
      _ = _ := by
        exact Fintype.sum_equiv eFin
          (fun i ↦ finiteModuleLocalDensity hDown (T.obj (eFin i))
            (T.indecomposable (eFin i)))
          (fun j ↦ finiteModuleLocalDensity hDown (T.obj j)
            (T.indecomposable j)) (fun i ↦ by rfl)
  have hsumT :
      (∑ j : Fin T.n,
        finiteModuleLocalDensity hDown (T.obj j) (T.indecomposable j)) =
        D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep := by
    simpa only [finiteOrbitSurplus, T] using
      T.sum_finiteModuleLocalDensity_eq_surplus hDown
  exact hsum.trans hsumT

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
