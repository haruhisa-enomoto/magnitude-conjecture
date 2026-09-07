import MagnitudeConjecture.CategoryTheory.LocallyFiniteModuleLocalDensity
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageControlWindow
import MagnitudeConjecture.CategoryTheory.ObjectDeletionSurvivingWindows

/-!
# Local density under one object deletion

For an indecomposable ambient module, the manuscript extends the local
density after deleting an object by zero when the module does not survive.
This file makes that convention literal.  The minimal-sink comparison proves
that the resulting local change vanishes outside the two-step Hom core.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- The local density after deletion, extended by zero to an ambient
indecomposable which does not vanish on the deleted objects. -/
noncomputable def finiteDeletionExtendedLocalDensity
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) : ℤ := by
  classical
  exact
    if hvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj then
      finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) C S M hvanish)
        (finiteDimensionalModuleRestrictionToDeletion_indec
          (k := k) C S M hM hvanish)
    else 0

/-- The manuscript's pointwise local-density change across an arbitrary
object deletion. -/
noncomputable def finiteDeletionLocalChangeAt
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) : ℤ :=
  finiteModuleLocalDensity hlocal M hM -
    finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM

@[simp]
theorem finiteDeletionExtendedLocalDensity_eq_zero_of_not_vanishes
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hvanish : ¬ ModuleVanishesOnDeleted (k := k) C S M.obj.obj) :
    finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM = 0 := by
  simp [finiteDeletionExtendedLocalDensity, hvanish]

/-- The deletion-extended local density depends only on the ambient
indecomposable isomorphism class. -/
theorem finiteDeletionExtendedLocalDensity_eq_of_iso
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : Indecomposable M) (hN : Indecomposable N) (e : M ≅ N) :
    finiteDeletionExtendedLocalDensity (k := k) C hlocal S M hM =
      finiteDeletionExtendedLocalDensity (k := k) C hlocal S N hN := by
  classical
  by_cases hMv : ModuleVanishesOnDeleted (k := k) C S M.obj.obj
  · have hNv : ModuleVanishesOnDeleted (k := k) C S N.obj.obj :=
      moduleVanishesOnDeleted_of_iso (k := k) C S e hMv
    let RM := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C S M hMv
    let RN := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C S N hNv
    let F := finiteDimensionalModuleExtensionByZero (k := k) C S
    let eRM := finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C S M hMv
    let eRN := finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C S N hNv
    let eR : RM ≅ RN := F.preimageIso (eRM.trans (e.trans eRN.symm))
    have hRM : Indecomposable RM :=
      finiteDimensionalModuleRestrictionToDeletion_indec
        (k := k) C S M hM hMv
    have hRN : Indecomposable RN :=
      finiteDimensionalModuleRestrictionToDeletion_indec
        (k := k) C S N hN hNv
    simpa only [finiteDeletionExtendedLocalDensity, dif_pos hMv, dif_pos hNv]
      using finiteModuleLocalDensity_eq_of_iso
        (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
          hRM hRN eR
  · have hNv : ¬ ModuleVanishesOnDeleted (k := k) C S N.obj.obj :=
      fun hNvanish ↦ hMv
        (moduleVanishesOnDeleted_of_iso (k := k) C S e.symm hNvanish)
    simp only [finiteDeletionExtendedLocalDensity, dif_neg hMv, dif_neg hNv]

/-- The pointwise local change depends only on the ambient indecomposable
isomorphism class. -/
theorem finiteDeletionLocalChangeAt_eq_of_iso
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (hM : Indecomposable M) (hN : Indecomposable N) (e : M ≅ N) :
    finiteDeletionLocalChangeAt (k := k) C hlocal S M hM =
      finiteDeletionLocalChangeAt (k := k) C hlocal S N hN := by
  rw [finiteDeletionLocalChangeAt, finiteDeletionLocalChangeAt,
    finiteModuleLocalDensity_eq_of_iso hlocal hM hN e,
    finiteDeletionExtendedLocalDensity_eq_of_iso
      (k := k) C hlocal S hM hN e]

/-- If a surviving indecomposable has a minimal sink whose source already
vanishes on the deleted objects, restriction preserves its intrinsic local
density. -/
theorem finiteDeletion_restriction_localDensity_eq_of_minimalSink_source_vanishes
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj)
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (g : Y ⟶ M) (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g)
    (dY : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (hY : ModuleVanishesOnDeleted (k := k) C S Y.obj.obj) :
    finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) C S M hvanish)
        (finiteDimensionalModuleRestrictionToDeletion_indec
          (k := k) C S M hM hvanish) =
      finiteModuleLocalDensity hlocal M hM := by
  classical
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  let Z := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C S M hvanish
  let hZ : Indecomposable Z :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C S M hM hvanish
  let eZ := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C S M hvanish
  let gF : Y ⟶ F.obj Z := g ≫ eZ.inv
  have hgF : IsRightAlmostSplit gF := hg.postcomp_iso eZ.symm
  have hgFmin : IsRightMinimal gF := hgmin.postcomp_iso eZ.symm
  let R := finiteVanishingModuleRestriction
    (k := k) C S
      ((finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y)
  let dR := Classical.choice
    (finiteDimensionalModule_finiteIndecomposableDecomposition R)
  let q := finiteDeletionRightAdjointSinkCandidate (k := k) C S gF
  have hq : IsRightAlmostSplit q :=
    finiteDeletionRightAdjointSinkCandidate_isRightAlmostSplit
      (k := k) C S gF hgF
  have hqmin : IsRightMinimal q :=
    finiteDeletionRightAdjointSinkCandidate_isRightMinimal_of_source_vanishes
      (k := k) C S gF hgFmin hY
  have harity : dR.n = dY.n :=
    finiteMaximalVanishingSubmoduleRestriction_arity_eq_of_vanishesOnDeleted
      (k := k) C S Y hY dY dR
  have hprojective : Projective Z ↔ Projective (F.obj Z) :=
    finiteDeletion_projective_iff_of_minimal_sink_source_vanishes
      (k := k) C S hP gF hgF hgFmin hY
  have hAfter :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
      Z hZ dR hq hqmin
  have hBefore :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      hlocal (F.obj Z)
      (finiteDimensionalModuleExtensionByZero_indec
        (k := k) C S Z hZ)
      dY hgF hgFmin
  have hIso := finiteModuleLocalDensity_eq_of_iso hlocal
    (finiteDimensionalModuleExtensionByZero_indec
      (k := k) C S Z hZ) hM eZ
  rw [hAfter, ← hIso, hBefore,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    harity]
  by_cases h : Projective Z
  · have h' : Projective (F.obj Z) := hprojective.1 h
    simp [h, h']
  · have h' : ¬ Projective (F.obj Z) :=
      fun hF ↦ h (hprojective.2 hF)
    simp [h, h']

/-- If both a surviving indecomposable endpoint and the source of one of its
minimal right almost-split maps vanish on the deleted objects, its pointwise
deletion local change is zero. -/
theorem finiteDeletionLocalChangeAt_eq_zero_of_minimalSink_source_vanishes
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj)
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (g : Y ⟶ M) (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g)
    (dY : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (hY : ModuleVanishesOnDeleted (k := k) C S Y.obj.obj) :
    finiteDeletionLocalChangeAt (k := k) C hlocal S M hM = 0 := by
  have hDensity :=
    finiteDeletion_restriction_localDensity_eq_of_minimalSink_source_vanishes
      (k := k) C hP hlocal S M hM hvanish g hg hgmin dY hY
  rw [finiteDeletionLocalChangeAt, finiteDeletionExtendedLocalDensity,
    dif_pos hvanish, hDensity, sub_self]

/-- Outside the two-step core, a surviving indecomposable has the same
intrinsic local density before and after one object deletion. -/
theorem finiteDeletion_localDensity_eq_of_endpoint_not_mem_twoStep
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C)
    (Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C ({y} : Set C)) k)
    (hZ : Indecomposable Z)
    (houtside :
      (finiteDimensionalModuleExtensionByZero
          (k := k) C ({y} : Set C)).obj Z ∉
        ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
          hlocal 2).isoClosure) :
    finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion
          (k := k) C ({y} : Set C) hlocal) Z hZ =
      finiteModuleLocalDensity hlocal
        ((finiteDimensionalModuleExtensionByZero
          (k := k) C ({y} : Set C)).obj Z)
        (finiteDimensionalModuleExtensionByZero_indec
          (k := k) C ({y} : Set C) Z hZ) := by
  classical
  let F := finiteDimensionalModuleExtensionByZero
    (k := k) C ({y} : Set C)
  let hFZ : Indecomposable (F.obj Z) :=
    finiteDimensionalModuleExtensionByZero_indec
      (k := k) C ({y} : Set C) Z hZ
  let A := finiteModuleMinimalSinkData hlocal (F.obj Z) hFZ
  let R := finiteVanishingModuleRestriction
    (k := k) C ({y} : Set C)
      ((finiteMaximalVanishingSubmoduleFunctor
        (k := k) C ({y} : Set C)).obj A.source)
  let dR := Classical.choice
    (finiteDimensionalModule_finiteIndecomposableDecomposition R)
  have hdata := finiteDeletion_sink_localData_unchanged_of_endpoint_not_mem_twoStep
    (k := k) C hP hlocal y A.map
      A.rightAlmostSplit A.rightMinimal hFZ houtside A.decomposition dR
  have hBefore :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      hlocal (F.obj Z) hFZ A.decomposition
        A.rightAlmostSplit A.rightMinimal
  have hAfter :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      (isLocallyRepresentationFinite_deletion
        (k := k) C ({y} : Set C) hlocal) Z hZ dR hdata.1 hdata.2.1
  rw [hAfter, hBefore,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    hdata.2.2.1]
  by_cases h : Projective Z
  · have h' : Projective (F.obj Z) := hdata.2.2.2.1 h
    simp [h, h']
  · have h' : ¬ Projective (F.obj Z) :=
      fun hF ↦ h (hdata.2.2.2.2 hF)
    simp [h, h']

/-- At an intermediate deletion stage, a surviving endpoint outside the
fixed ambient two-step core has the same intrinsic density after deleting
the chosen surviving object. -/
theorem finiteDeletion_localDensity_eq_of_not_mem_deletionTwoStepModuleCore
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C) (S : Set C) (hy : y ∉ S)
    (hPstage : ∀ X : DeletionCategory (k := k) C S,
      IsFiniteDimensionalModule
        (C := DeletionCategory (k := k) C S) k
        (linearCoyonedaLinearModule (k := k) X))
    (Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k)
        (DeletionCategory (k := k) C S)
        ({survivingObj (k := k) C S hy} :
          Set (DeletionCategory (k := k) C S))) k)
    (hZ : Indecomposable Z)
    (houtside :
      (finiteDimensionalModuleExtensionByZero
        (k := k) (DeletionCategory (k := k) C S)
        ({survivingObj (k := k) C S hy} :
          Set (DeletionCategory (k := k) C S))).obj Z ∉
        deletionTwoStepModuleCore (k := k) C hlocal y S) :
    finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion
          (k := k) (DeletionCategory (k := k) C S)
          ({survivingObj (k := k) C S hy} :
            Set (DeletionCategory (k := k) C S))
          (isLocallyRepresentationFinite_deletion (k := k) C S hlocal))
        Z hZ =
      finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
        ((finiteDimensionalModuleExtensionByZero
          (k := k) (DeletionCategory (k := k) C S)
          ({survivingObj (k := k) C S hy} :
            Set (DeletionCategory (k := k) C S))).obj Z)
        (finiteDimensionalModuleExtensionByZero_indec
          (k := k) (DeletionCategory (k := k) C S)
          ({survivingObj (k := k) C S hy} :
            Set (DeletionCategory (k := k) C S)) Z hZ) := by
  classical
  let D := DeletionCategory (k := k) C S
  let yS := survivingObj (k := k) C S hy
  let hlocalD := isLocallyRepresentationFinite_deletion (k := k) C S hlocal
  let F := finiteDimensionalModuleExtensionByZero
    (k := k) D ({yS} : Set D)
  let hFZ : Indecomposable (F.obj Z) :=
    finiteDimensionalModuleExtensionByZero_indec
      (k := k) D ({yS} : Set D) Z hZ
  let A := finiteModuleMinimalSinkData hlocalD (F.obj Z) hFZ
  let R := finiteVanishingModuleRestriction
    (k := k) D ({yS} : Set D)
      ((finiteMaximalVanishingSubmoduleFunctor
        (k := k) D ({yS} : Set D)).obj A.source)
  let dR := Classical.choice
    (finiteDimensionalModule_finiteIndecomposableDecomposition R)
  have hdata :=
    finiteDeletion_sink_localData_unchanged_of_not_mem_deletionTwoStepModuleCore
      (k := k) C hlocal y S hy hPstage A.map A.rightAlmostSplit
        A.rightMinimal hFZ houtside A.decomposition dR
  have hBefore :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      hlocalD (F.obj Z) hFZ A.decomposition
        A.rightAlmostSplit A.rightMinimal
  have hAfter :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      (isLocallyRepresentationFinite_deletion
        (k := k) D ({yS} : Set D) hlocalD)
      Z hZ dR hdata.1 hdata.2.1
  rw [hAfter, hBefore,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    hdata.2.2.1]
  by_cases h : Projective Z
  · have h' : Projective (F.obj Z) := hdata.2.2.2.1 h
    simp [h, h']
  · have h' : ¬ Projective (F.obj Z) :=
      fun hF ↦ h (hdata.2.2.2.2 hF)
    simp [h, h']

/-- At an intermediate stage, the singleton local change at the next
surviving object is supported on the fixed ambient two-step core. -/
theorem finiteDeletionLocalChangeAt_eq_zero_of_not_mem_deletionTwoStepModuleCore
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C) (S : Set C) (hy : y ∉ S)
    (hPstage : ∀ X : DeletionCategory (k := k) C S,
      IsFiniteDimensionalModule
        (C := DeletionCategory (k := k) C S) k
        (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k)
    (hM : Indecomposable M)
    (houtside : M ∉ deletionTwoStepModuleCore (k := k) C hlocal y S) :
    finiteDeletionLocalChangeAt
      (k := k) (DeletionCategory (k := k) C S)
      (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
      ({survivingObj (k := k) C S hy} :
        Set (DeletionCategory (k := k) C S)) M hM = 0 := by
  classical
  let D := DeletionCategory (k := k) C S
  let yS := survivingObj (k := k) C S hy
  let hlocalD := isLocallyRepresentationFinite_deletion (k := k) C S hlocal
  have hvanish : ModuleVanishesOnDeleted
      (k := k) D ({yS} : Set D) M.obj.obj := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    by_contra hzero
    have hnontrivial : Nontrivial (M.obj.obj.obj yS) :=
      not_subsingleton_iff_nontrivial.mp fun hsub ↦
        hzero (ModuleCat.isZero_iff_subsingleton.mpr hsub)
    exact houtside
      (mem_deletionTwoStepModuleCore_of_nontrivial_at
        (k := k) C hlocal y S hy M hM hnontrivial)
  let Z := finiteDimensionalModuleRestrictionToDeletion
    (k := k) D ({yS} : Set D) M hvanish
  let hZ : Indecomposable Z :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) D ({yS} : Set D) M hM hvanish
  let Fnext := finiteDimensionalModuleExtensionByZero
    (k := k) D ({yS} : Set D)
  let Fstage := finiteDimensionalModuleExtensionByZero (k := k) C S
  let e := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) D ({yS} : Set D) M hvanish
  have houtsideZ : Fnext.obj Z ∉
      deletionTwoStepModuleCore (k := k) C hlocal y S := by
    intro hFZ
    change Fstage.obj (Fnext.obj Z) ∈
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal 2).isoClosure at hFZ
    obtain ⟨i, ⟨q⟩⟩ := hFZ
    apply houtside
    exact ⟨i, ⟨q.trans (Fstage.mapIso e)⟩⟩
  have hDensity :=
    finiteDeletion_localDensity_eq_of_not_mem_deletionTwoStepModuleCore
      (k := k) C hlocal y S hy hPstage Z hZ houtsideZ
  have hIso := finiteModuleLocalDensity_eq_of_iso hlocalD
    (finiteDimensionalModuleExtensionByZero_indec
      (k := k) D ({yS} : Set D) Z hZ) hM e
  rw [finiteDeletionLocalChangeAt,
    finiteDeletionExtendedLocalDensity, dif_pos hvanish,
    hDensity, hIso, sub_self]

/-- The singleton-deletion local change is supported on the manuscript's
two-step Hom neighborhood. -/
theorem finiteDeletionLocalChangeAt_eq_zero_of_not_mem_twoStep
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (houtside : M ∉
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal 2).isoClosure) :
    finiteDeletionLocalChangeAt
      (k := k) C hlocal ({y} : Set C) M hM = 0 := by
  classical
  have hvanish :
      ModuleVanishesOnDeleted (k := k) C ({y} : Set C) M.obj.obj := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    by_contra hzero
    have hnontrivial : Nontrivial (M.obj.obj.obj y) :=
      not_subsingleton_iff_nontrivial.mp fun hsub ↦
        hzero (ModuleCat.isZero_iff_subsingleton.mpr hsub)
    have h₀ : M ∈ (finiteFiberControlSeed hlocal y).isoClosure :=
      mem_finiteFiberControlSeed_isoClosure hlocal y hM hnontrivial
    have h₁ : M ∈
        ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
          hlocal 1).isoClosure :=
      (finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_homInteraction
        hlocal h₀ hM (Or.inl rfl)
    exact houtside
      ((finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_homInteraction
        hlocal h₁ hM (Or.inl rfl))
  let Z := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C ({y} : Set C) M hvanish
  let hZ : Indecomposable Z :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C ({y} : Set C) M hM hvanish
  let F := finiteDimensionalModuleExtensionByZero
    (k := k) C ({y} : Set C)
  let e := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C ({y} : Set C) M hvanish
  have houtsideZ : F.obj Z ∉
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal 2).isoClosure := by
    intro hFZ
    obtain ⟨i, ⟨q⟩⟩ := hFZ
    exact houtside ⟨i, ⟨q.trans e⟩⟩
  have hDensity := finiteDeletion_localDensity_eq_of_endpoint_not_mem_twoStep
    (k := k) C hP hlocal y Z hZ houtsideZ
  have hIso := finiteModuleLocalDensity_eq_of_iso hlocal
    (finiteDimensionalModuleExtensionByZero_indec
      (k := k) C ({y} : Set C) Z hZ) hM e
  rw [finiteDeletionLocalChangeAt,
    finiteDeletionExtendedLocalDensity, dif_pos hvanish,
    hDensity, hIso, sub_self]

end MagnitudeConjecture.ObjectDeletion
