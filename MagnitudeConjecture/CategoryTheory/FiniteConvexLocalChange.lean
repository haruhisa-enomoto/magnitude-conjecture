import MagnitudeConjecture.CategoryTheory.FiniteConvexDeletionOrder
import MagnitudeConjecture.CategoryTheory.FiniteDeletionSupportLocalChangeSum
import MagnitudeConjecture.CategoryTheory.FiniteModuleLocalDensityEquivalence

/-!
# Singleton local change inside a finite convex support window

Restriction to the finite convex object window containing the three-step
module neighborhood preserves the pointwise singleton-deletion local change
on the two-step endpoint core.  The proof compares the pre-deletion densities
directly and the post-deletion densities through the canonical equivalence
which commutes window restriction with singleton deletion.
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

/-- Vanishing at the ambient base object is equivalent to vanishing at its
surviving representative after restriction to a control window. -/
theorem finiteConvex_restriction_vanishesOn_base_iff
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C)
    (P : FiniteConvexModuleControlWindow (k := k) x
      (finiteThreeStepControlFamily hlocal x))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hWindow : ModuleVanishesOnDeleted
      (k := k) C P.objectsᶜ M.obj.obj) :
    ModuleVanishesOnDeleted
        (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
        ({P.baseObject C} : Set _)
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) C P.objectsᶜ M hWindow).obj.obj ↔
      ModuleVanishesOnDeleted
        (k := k) C ({x} : Set C) M.obj.obj := by
  constructor
  · intro h X hX
    rw [Set.mem_singleton_iff] at hX
    subst X
    have hzero := h (P.baseObject C) (by simp)
    change IsZero (M.obj.obj.obj x) at hzero
    exact hzero
  · intro h X hX
    rw [Set.mem_singleton_iff] at hX
    subst X
    change IsZero (M.obj.obj.obj x)
    exact h x (by simp)

/-- Restriction to a finite convex three-step support window preserves the
pointwise singleton local change on the ambient two-step module core. -/
theorem finiteConvex_restriction_localChangeAt_eq
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C)
    (P : FiniteConvexModuleControlWindow (k := k) x
      (finiteThreeStepControlFamily hlocal x))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hMtwo : M ∈
      ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
        hlocal 2).isoClosure) :
    let hWindow : ModuleVanishesOnDeleted
        (k := k) C P.objectsᶜ M.obj.obj :=
      moduleVanishesOnDeleted_compl_of_moduleSupport_subset
        (k := k) C P.objects M
          (P.moduleSupport_subset_of_mem_isoClosure
            ((finiteFiberControlSeed hlocal x).mem_iterateHomNeighborhood_succ_of_homInteraction
              hlocal hMtwo hM (Or.inl rfl)))
    let RM := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C P.objectsᶜ M hWindow
    let hRM := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C P.objectsᶜ M hM hWindow
    finiteDeletionLocalChangeAt
        (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
        (isLocallyRepresentationFinite_deletion
          (k := k) C P.objectsᶜ hlocal)
        ({P.baseObject C} : Set _) RM hRM =
      finiteDeletionLocalChangeAt
        (k := k) C hlocal ({x} : Set C) M hM := by
  classical
  let hMthree : M ∈ (finiteThreeStepControlFamily hlocal x).isoClosure :=
    (finiteFiberControlSeed hlocal x).mem_iterateHomNeighborhood_succ_of_homInteraction
      hlocal hMtwo hM (Or.inl rfl)
  let hWindow : ModuleVanishesOnDeleted
      (k := k) C P.objectsᶜ M.obj.obj :=
    moduleVanishesOnDeleted_compl_of_moduleSupport_subset
      (k := k) C P.objects M
        (P.moduleSupport_subset_of_mem_isoClosure hMthree)
  let RM := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C P.objectsᶜ M hWindow
  let hRM : Indecomposable RM :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C P.objectsᶜ M hM hWindow
  let hlocalWindow := isLocallyRepresentationFinite_deletion
    (k := k) C P.objectsᶜ hlocal
  have hPre : finiteModuleLocalDensity hlocalWindow RM hRM =
      finiteModuleLocalDensity hlocal M hM :=
    finiteConvex_restriction_localDensity_eq
      (k := k) C hP hlocal x P M hM hMtwo hWindow
  have hBaseIff := finiteConvex_restriction_vanishesOn_base_iff
    (k := k) C hlocal x P M hWindow
  change finiteDeletionLocalChangeAt
      (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
      hlocalWindow ({P.baseObject C} : Set _) RM hRM =
    finiteDeletionLocalChangeAt (k := k) C hlocal ({x} : Set C) M hM
  by_cases hBase : ModuleVanishesOnDeleted
      (k := k) C ({x} : Set C) M.obj.obj
  · have hRMBase : ModuleVanishesOnDeleted
        (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
        ({P.baseObject C} : Set _) RM.obj.obj :=
      hBaseIff.mpr hBase
    let RX := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C ({x} : Set C) M hBase
    let hRX : Indecomposable RX :=
      finiteDimensionalModuleRestrictionToDeletion_indec
        (k := k) C ({x} : Set C) M hM hBase
    let hWindowAfterBase : ModuleVanishesOnDeleted
        (k := k) (DeletionCategory (k := k) C ({x} : Set C))
        (AdditionalDeleted (k := k) C ({x} : Set C) P.objectsᶜ)
        RX.obj.obj := by
      intro Y hY
      change IsZero (M.obj.obj.obj Y.obj.as)
      exact hWindow Y.obj.as hY
    let RXWindow := finiteDimensionalModuleRestrictionToDeletion
      (k := k) (DeletionCategory (k := k) C ({x} : Set C))
      (AdditionalDeleted (k := k) C ({x} : Set C) P.objectsᶜ)
      RX hWindowAfterBase
    let hRXWindow : Indecomposable RXWindow :=
      finiteDimensionalModuleRestrictionToDeletion_indec
        (k := k) (DeletionCategory (k := k) C ({x} : Set C))
        (AdditionalDeleted (k := k) C ({x} : Set C) P.objectsᶜ)
        RX hRX hWindowAfterBase
    let RMBase := finiteDimensionalModuleRestrictionToDeletion
      (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
      ({P.baseObject C} : Set _)
      RM hRMBase
    let hRMBaseIndec : Indecomposable RMBase :=
      finiteDimensionalModuleRestrictionToDeletion_indec
        (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
        ({P.baseObject C} : Set _) RM hRM hRMBase
    let FBase := finiteDimensionalModuleExtensionByZero
      (k := k) C ({x} : Set C)
    let eRX := finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C ({x} : Set C) M hBase
    have hRXtwo : FBase.obj RX ∈
        ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
          hlocal 2).isoClosure := by
      obtain ⟨i, ⟨e⟩⟩ := hMtwo
      exact ⟨i, ⟨e.trans eRX.symm⟩⟩
    have hPostRestriction :
        finiteModuleLocalDensity
            (isLocallyRepresentationFinite_deletion
              (k := k) (DeletionCategory (k := k) C ({x} : Set C))
              (AdditionalDeleted (k := k) C ({x} : Set C) P.objectsᶜ)
              (isLocallyRepresentationFinite_deletion
                (k := k) C ({x} : Set C) hlocal))
            RXWindow hRXWindow =
          finiteModuleLocalDensity
            (isLocallyRepresentationFinite_deletion
              (k := k) C ({x} : Set C) hlocal) RX hRX :=
      finiteConvex_stage_restriction_localDensity_eq
        (k := k) C hP hlocal x P ({x} : Set C) RX hRX
          hRXtwo hWindowAfterBase
    let E := P.singletonSwapModuleEquivalence C
    let eSwap : E.functor.obj RXWindow ≅ RMBase :=
      P.singletonSwap_restrictionIso C M hWindow hBase
        hRMBase hWindowAfterBase
    let hlocalAfterBase := isLocallyRepresentationFinite_deletion
      (k := k) C ({x} : Set C) hlocal
    let hlocalRXWindow := isLocallyRepresentationFinite_deletion
      (k := k) (DeletionCategory (k := k) C ({x} : Set C))
      (AdditionalDeleted (k := k) C ({x} : Set C) P.objectsᶜ)
      hlocalAfterBase
    let hlocalRMBase := isLocallyRepresentationFinite_deletion
      (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
      ({P.baseObject C} : Set _) hlocalWindow
    have hMap := finiteModuleLocalDensity_map_equivalence
      hlocalRMBase hlocalRXWindow E RXWindow hRXWindow
    have hIso := finiteModuleLocalDensity_eq_of_iso hlocalRMBase
      ((MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        E.functor RXWindow).2 hRXWindow)
      hRMBaseIndec eSwap
    have hPost : finiteModuleLocalDensity hlocalRMBase RMBase hRMBaseIndec =
        finiteModuleLocalDensity hlocalAfterBase RX hRX :=
      hIso.symm.trans (hMap.trans hPostRestriction)
    simp only [finiteDeletionLocalChangeAt,
      finiteDeletionExtendedLocalDensity, dif_pos hRMBase, dif_pos hBase]
    exact congrArg₂ (fun a b : ℤ ↦ a - b) hPre hPost
  · have hRMBase : ¬ ModuleVanishesOnDeleted
        (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
        ({P.baseObject C} : Set _) RM.obj.obj :=
      fun h ↦ hBase (hBaseIff.mp h)
    rw [finiteDeletionLocalChangeAt, finiteDeletionLocalChangeAt,
      finiteDeletionExtendedLocalDensity_eq_zero_of_not_vanishes
        (k := k) (DeletionCategory (k := k) C P.objectsᶜ)
          hlocalWindow ({P.baseObject C} : Set _) RM hRM hRMBase,
      finiteDeletionExtendedLocalDensity_eq_zero_of_not_vanishes
        (k := k) C hlocal ({x} : Set C) M hM hBase,
      sub_zero, sub_zero]
    exact hPre

/-- The isomorphism-class local-change sum on the ambient two-step endpoint
family is exactly the corresponding sum after restriction to the finite
convex control category. -/
theorem finiteConvex_restriction_localChangeSum_eq
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C)
    (P : FiniteConvexModuleControlWindow (k := k) x
      (finiteThreeStepControlFamily hlocal x)) :
    let W₂ := (finiteFiberControlSeed hlocal x).iterateHomNeighborhood
      hlocal 2
    let P₂ := P.twoStepWindow hlocal x
    finiteDeletionLocalChangeSum
        (k := k) (DeletionCategory (k := k) C P₂.objectsᶜ)
        (isLocallyRepresentationFinite_deletion
          (k := k) C P₂.objectsᶜ hlocal)
        ({P₂.baseObject C} : Set _) (P₂.restrictionFamily C) =
      finiteDeletionLocalChangeSum
        (k := k) C hlocal ({x} : Set C) W₂ := by
  classical
  let W₂ := (finiteFiberControlSeed hlocal x).iterateHomNeighborhood
    hlocal 2
  let P₂ := P.twoStepWindow hlocal x
  let hlocalWindow := isLocallyRepresentationFinite_deletion
    (k := k) C P₂.objectsᶜ hlocal
  dsimp only
  unfold finiteDeletionLocalChangeSum
  rw [P₂.sum_isoClass_restrictionFamily C]
  apply Finset.sum_congr rfl
  intro q _hq
  induction q using Quotient.inductionOn with
  | _ i =>
      change finiteDeletionLocalChangeAt
          (k := k) (DeletionCategory (k := k) C P₂.objectsᶜ)
          hlocalWindow ({P₂.baseObject C} : Set _)
          ((P₂.restrictionFamily C).obj i)
          ((P₂.restrictionFamily C).indecomposable i) =
        finiteDeletionLocalChangeAt
          (k := k) C hlocal ({x} : Set C) (W₂.obj i)
            (W₂.indecomposable i)
      exact finiteConvex_restriction_localChangeAt_eq
        (k := k) C hP hlocal x P (W₂.obj i) (W₂.indecomposable i)
          (W₂.obj_mem_isoClosure i)

variable [IsAlgClosed k]

/-- Source-facing local directed deletion theorem: singleton local change in
an admissible category is nonnegative, and equality forces every
indecomposable nonzero at the deleted object to have one-dimensional fibre
there. -/
theorem admissible_finiteDeletionLocalChange_nonneg_and_rigidity
    (H : IsAdmissible (k := k) (C := C)) (x : C) :
    0 ≤ finiteDeletionLocalChange
        (k := k) C H.locallyRepresentationFinite x ∧
      (finiteDeletionLocalChange
          (k := k) C H.locallyRepresentationFinite x = 0 →
        ∀ (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k),
          Indecomposable M → ¬ IsZero (M.obj.obj.obj x) →
            Module.finrank k (M.obj.obj.obj x) = 1) := by
  classical
  let hlocal := H.locallyRepresentationFinite
  let W₂ := (finiteFiberControlSeed hlocal x).iterateHomNeighborhood
    hlocal 2
  let W₃ := finiteThreeStepControlFamily hlocal x
  let P : FiniteConvexModuleControlWindow (k := k) x W₃ :=
    Classical.choice
      (finiteConvexModuleControlWindow_nonempty
        (k := k) H.finiteConvexNeighborhoods x W₃)
  let P₂ := P.twoStepWindow hlocal x
  let D := DeletionCategory (k := k) C P₂.objectsᶜ
  let y : D := P₂.baseObject C
  let HD := isAdmissible_deletion
    (k := k) (C := C) P₂.objectsᶜ H
  let hlocalD := HD.locallyRepresentationFinite
  let hP_D := HD.locallyBounded.finiteCovariantRepresentables
  let hlocalDy := isLocallyRepresentationFinite_deletion
    (k := k) D ({y} : Set D) hlocalD
  have hx : x ∉ P₂.objectsᶜ := by
    simpa only [Set.mem_compl_iff, not_not] using P₂.base_mem
  letI : Finite D := complementDeletion_finite
    (k := k) C P₂.objects P₂.finite
  letI : Fintype D := Fintype.ofFinite D
  let Dy := DeletionCategory (k := k) D ({y} : Set D)
  letI : Finite Dy := ObjectDeletion.deletionCategory_finite
    (k := k) ({y} : Set D)
  letI : Fintype Dy := Fintype.ofFinite Dy
  let S := finiteCategoryModuleIndecomposableSkeleton hlocalD
  let T := finiteCategoryModuleIndecomposableSkeleton hlocalDy
  let Wrestrict := P₂.restrictionFamily C
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := D) k) :=
    enoughProjectives_of_finiteRepresentables hP_D
  let hP_Dy := fun Z ↦ deletion_linearCoyoneda_isFiniteDimensional
    (k := k) D hP_D ({y} : Set D) Z
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := Dy) k) :=
    enoughProjectives_of_finiteRepresentables hP_Dy
  have hsupport : ∀ i : Fin S.n, S.obj i ∉ Wrestrict.isoClosure →
      finiteDeletionLocalChangeAt
        (k := k) D hlocalD ({y} : Set D)
          (S.obj i) (S.indecomposable i) = 0 := by
    intro i houtside
    apply finiteDeletionLocalChangeAt_eq_zero_of_not_mem_deletionTwoStepModuleCore
      (k := k) C hlocal x P₂.objectsᶜ hx hP_D
        (S.obj i) (S.indecomposable i)
    intro hcore
    exact houtside
      (P₂.mem_restrictionFamily_isoClosure_of_extension_mem_isoClosure
        C (S.obj i) hcore)
  have hsum := finiteDeletionLocalChangeSum_eq_surplus_sub
    (k := k) D hlocalD ({y} : Set D) Wrestrict S T hsupport
  have hfiniteLe :=
    MagnitudeConjecture.CoveringHom.finiteCategoryProjectiveGenerator.singletonDeletion_surplus_le_of_fintype
    (k := k) (C := D) hP_D HD.locallyBounded.localEndomorphismRings
      HD.locallyBounded.skeletal hlocalD HD.directed y S T
  have hrestriction := finiteConvex_restriction_localChangeSum_eq
    (k := k) C H.locallyBounded.finiteCovariantRepresentables
      hlocal x P
  constructor
  · change 0 ≤ finiteDeletionLocalChangeSum
      (k := k) C hlocal ({x} : Set C) W₂
    rw [← hrestriction, hsum]
    exact sub_nonneg.mpr hfiniteLe
  · intro hzero M hM hMx
    have hrestrictedZero : finiteDeletionLocalChangeSum
        (k := k) D hlocalD ({y} : Set D) Wrestrict = 0 := by
      exact hrestriction.trans hzero
    have hsurplusDiffZero :
        @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              S.toFiniteRightTauCategoryData)
            S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) -
          @MagnitudeConjecture.ARCount.surplus (Fin T.n) inferInstance
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              T.toFiniteRightTauCategoryData)
            T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
          0 := hsum.symm.trans hrestrictedZero
    have hsurplusEq :
        @MagnitudeConjecture.ARCount.surplus (Fin T.n) inferInstance
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              T.toFiniteRightTauCategoryData)
            T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
          @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
            (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
              S.toFiniteRightTauCategoryData)
            S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) :=
      (sub_eq_zero.mp hsurplusDiffZero).symm
    have hMnontrivial : Nontrivial (M.obj.obj.obj x) :=
      not_subsingleton_iff_nontrivial.mp fun hsub ↦
        hMx (ModuleCat.isZero_iff_subsingleton.mpr hsub)
    have hMzero : M ∈ (finiteFiberControlSeed hlocal x).isoClosure :=
      mem_finiteFiberControlSeed_isoClosure hlocal x hM hMnontrivial
    have hMone : M ∈
        ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
          hlocal 1).isoClosure :=
      (finiteFiberControlSeed hlocal x).mem_iterateHomNeighborhood_succ_of_homInteraction
          hlocal hMzero hM (Or.inl rfl)
    have hMtwo : M ∈ W₂.isoClosure :=
      (finiteFiberControlSeed hlocal x).mem_iterateHomNeighborhood_succ_of_homInteraction
          hlocal hMone hM (Or.inl rfl)
    have hMthree : M ∈ W₃.isoClosure :=
      (finiteFiberControlSeed hlocal x).mem_iterateHomNeighborhood_succ_of_homInteraction
          hlocal hMtwo hM (Or.inl rfl)
    let hWindow : ModuleVanishesOnDeleted
        (k := k) C P.objectsᶜ M.obj.obj :=
      moduleVanishesOnDeleted_compl_of_moduleSupport_subset
        (k := k) C P.objects M
          (P.moduleSupport_subset_of_mem_isoClosure hMthree)
    let RM := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C P.objectsᶜ M hWindow
    let hRM : Indecomposable RM :=
      finiteDimensionalModuleRestrictionToDeletion_indec
        (k := k) C P.objectsᶜ M hM hWindow
    have hRMy : ¬ IsZero (RM.obj.obj.obj y) := by
      intro hzero
      apply hMx
      change IsZero (M.obj.obj.obj x) at hzero
      exact hzero
    have hdim :=
      MagnitudeConjecture.CoveringHom.finiteCategoryProjectiveGenerator.finrank_obj_eq_one_of_singletonDeletion_surplus_eq_of_fintype
      (k := k) (C := D) hP_D HD.locallyBounded.localEndomorphismRings
        HD.locallyBounded.skeletal hlocalD HD.directed y S T hsurplusEq
          RM hRM hRMy
    change Module.finrank k (M.obj.obj.obj x) = 1 at hdim
    exact hdim

/-- Nonnegativity clause of admissible local directed deletion. -/
theorem admissible_finiteDeletionLocalChange_nonneg
    (H : IsAdmissible (k := k) (C := C)) (x : C) :
    0 ≤ finiteDeletionLocalChange
      (k := k) C H.locallyRepresentationFinite x :=
  (admissible_finiteDeletionLocalChange_nonneg_and_rigidity
    (k := k) C H x).1

/-- Equality clause of admissible local directed deletion. -/
theorem admissible_finiteDeletionLocalChange_rigidity
    (H : IsAdmissible (k := k) (C := C)) (x : C)
    (hzero : finiteDeletionLocalChange
      (k := k) C H.locallyRepresentationFinite x = 0)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) (hMx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 :=
  (admissible_finiteDeletionLocalChange_nonneg_and_rigidity
    (k := k) C H x).2 hzero M hM hMx

end MagnitudeConjecture.ObjectDeletion
