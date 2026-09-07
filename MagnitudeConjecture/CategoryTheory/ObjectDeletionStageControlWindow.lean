import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageSeparation
import MagnitudeConjecture.CategoryTheory.ObjectDeletionControlWindow

/-!
# Certified control windows inside object-deletion stages

Extension by zero reflects the finite surviving part of an ambient module
family exactly.  It also transports the symmetric Hom-interaction relation.
Consequently the intrinsic Hom neighborhood of the surviving two-step core is
contained in the additive closure of the surviving three-step family.  This is
the control-window hypothesis required by the arbitrary-window finite
push-down theorem.
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

/-- A deletion-stage module belongs to the core cut out by an ambient module
window when its extension by zero belongs to that window. -/
def deletionStageModuleCore
    (S : Set C)
    (Core : Set
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)) :
    Set (FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :=
  fun M ↦
    (finiteDimensionalModuleExtensionByZero (k := k) C S).obj M ∈ Core

/-- The intrinsic surviving family has exactly the modules whose ambient
extensions belong to the original family's isomorphism closure. -/
theorem mem_deletionSurvivingModuleFamily_isoClosure_iff
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    M ∈ (deletionSurvivingModuleFamily (k := k) C W S).isoClosure ↔
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj M ∈
        W.isoClosure := by
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  constructor
  · rintro ⟨i, ⟨e⟩⟩
    obtain ⟨j, ⟨q⟩⟩ :=
      deletionSurvivingModuleFamily_extension_mem_isoClosure
        (k := k) C W S i
    exact ⟨j, ⟨q ≪≫ F.mapIso e⟩⟩
  · intro hFM
    have hvanish : ModuleVanishesOnDeleted (k := k) C S (F.obj M).obj.obj :=
      (finiteDimensionalModuleExtensionByZero_essImage_iff
        (k := k) C S (F.obj M)).1 ⟨M, ⟨Iso.refl _⟩⟩
    obtain ⟨i, ⟨e⟩⟩ :=
      mem_deletionSurvivingSubfamily_isoClosure (k := k) C W S hFM hvanish
    let T := deletionSurvivingSubfamily (k := k) C W S
    let hTi : ModuleVanishesOnDeleted (k := k) C S (T.obj i).obj.obj :=
      deletionSurvivingSubfamily_obj_vanishes (k := k) C W S i
    let q : F.obj
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) C S (T.obj i) hTi) ≅ T.obj i :=
      finiteDimensionalModuleRestrictionExtensionIso
        (k := k) C S (T.obj i) hTi
    refine ⟨i, ⟨?_⟩⟩
    exact F.preimageIso (q ≪≫ e)

/-- Full faithfulness of extension by zero transports equality or a nonzero
Hom in either direction, hence transports the symmetric Hom-interaction
relation. -/
theorem homInteraction_extensionByZero
    (S : Set C)
    {M N : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (hMN : CoveringSeparation.homInteraction M N) :
    CoveringSeparation.homInteraction
      ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj M)
      ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj N) := by
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  rcases hMN with hMN | hMN | hNM
  · exact Or.inl (congrArg F.obj hMN)
  · letI := hMN
    exact Or.inr (Or.inl F.map_injective.nontrivial)
  · letI := hNM
    exact Or.inr (Or.inr F.map_injective.nontrivial)

/-- The intrinsic iterated support neighborhood at a deletion stage embeds,
after extension by zero, into the corresponding ambient neighborhood.  The
exactly trimmed fibre and Hom-neighborhood families make this true for every
chosen representative, not only for the classes required by their coverage
certificates. -/
theorem iterateHomNeighborhood_extensionByZero_mem
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C) (S : Set C) (hy : y ∉ S) (n : ℕ)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k)
    (hM : Indecomposable M)
    (hmem : M ∈
      ((finiteFiberControlSeed
          (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
          (survivingObj (k := k) C S hy)).iterateHomNeighborhood
        (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
        n).isoClosure) :
    (finiteDimensionalModuleExtensionByZero (k := k) C S).obj M ∈
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal n).isoClosure := by
  let D := DeletionCategory (k := k) C S
  let yS := survivingObj (k := k) C S hy
  let hlocalD := isLocallyRepresentationFinite_deletion
    (k := k) C S hlocal
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  induction n generalizing M with
  | zero =>
      change M ∈ (finiteFiberControlSeed hlocalD yS).isoClosure at hmem
      change F.obj M ∈ (finiteFiberControlSeed hlocal y).isoClosure
      obtain ⟨i, ⟨e⟩⟩ := hmem
      have hseed : Nontrivial
          (((finiteFiberControlSeed hlocalD yS).obj i).obj.obj.obj yS) :=
        finiteFiberControlSeed_obj_nontrivial hlocalD yS i
      have hMy : Nontrivial (M.obj.obj.obj yS) :=
        (mem_moduleSupport_iff_of_iso e yS).mp hseed
      have hFMy : Nontrivial ((F.obj M).obj.obj.obj y) :=
        (moduleExtensionByZeroObjIsoAt
          (k := k) C S M.obj.obj yS).toLinearEquiv.toEquiv.nontrivial_congr.mpr
            hMy
      exact mem_finiteFiberControlSeed_isoClosure hlocal y
        (finiteDimensionalModuleExtensionByZero_indec
          (k := k) C S M hM) hFMy
  | succ n ih =>
      let StagePrevious :=
        (finiteFiberControlSeed hlocalD yS).iterateHomNeighborhood hlocalD n
      let AmbientPrevious :=
        (finiteFiberControlSeed hlocal y).iterateHomNeighborhood hlocal n
      change M ∈ (StagePrevious.homNeighborhood hlocalD).isoClosure at hmem
      change F.obj M ∈ (AmbientPrevious.homNeighborhood hlocal).isoClosure
      obtain ⟨t, ⟨e⟩⟩ := hmem
      obtain ⟨j, X, hPreviousX, hTermX⟩ :=
        StagePrevious.homNeighborhood_obj_commonSupport hlocalD t
      have hPreviousAmbient : F.obj (StagePrevious.obj j) ∈
          AmbientPrevious.isoClosure :=
        ih (StagePrevious.obj j) (StagePrevious.indecomposable j)
          (StagePrevious.obj_mem_isoClosure j)
      have hMX : X ∈ moduleSupport k M.obj.obj :=
        (mem_moduleSupport_iff_of_iso e X).mp hTermX
      have hFPreviousX : X.obj.as ∈
          moduleSupport k (F.obj (StagePrevious.obj j)).obj.obj :=
        (moduleExtensionByZeroObjIsoAt
          (k := k) C S (StagePrevious.obj j).obj.obj X).toLinearEquiv.toEquiv.nontrivial_congr.mpr
            hPreviousX
      have hFMX : X.obj.as ∈ moduleSupport k (F.obj M).obj.obj :=
        (moduleExtensionByZeroObjIsoAt
          (k := k) C S M.obj.obj X).toLinearEquiv.toEquiv.nontrivial_congr.mpr
            hMX
      obtain ⟨i, ⟨q⟩⟩ := hPreviousAmbient
      have hAmbientPreviousX : X.obj.as ∈
          moduleSupport k (AmbientPrevious.obj i).obj.obj :=
        (mem_moduleSupport_iff_of_iso q X.obj.as).mpr hFPreviousX
      exact AmbientPrevious.mem_homNeighborhood_isoClosure_of_commonSupport
        hlocal
        (finiteDimensionalModuleExtensionByZero_indec (k := k) C S M hM)
        ⟨i, X.obj.as, hAmbientPreviousX, hFMX⟩

/-- The surviving intrinsic part of the ambient two-step window is the
endpoint core used for deletion-stage push-down. -/
def deletionTwoStepModuleCore
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C) (S : Set C) :
    Set (FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :=
  deletionStageModuleCore (k := k) C S
    ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
      hlocal 2).isoClosure

/-- If an indecomposable stage endpoint lies outside the ambient two-step
core centered at a surviving object, the source of any right-minimal map to
that endpoint vanishes at that stage object. -/
theorem rightMinimal_source_vanishesAt_of_not_mem_deletionTwoStepModuleCore
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C) (S : Set C) (hy : y ∉ S)
    {Y Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (dY : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (g : Y ⟶ Z) (hgmin : IsRightMinimal g) (hZ : Indecomposable Z)
    (houtside : Z ∉ deletionTwoStepModuleCore (k := k) C hlocal y S) :
    ModuleVanishesOnDeleted
      (k := k) (DeletionCategory (k := k) C S)
        ({survivingObj (k := k) C S hy} :
          Set (DeletionCategory (k := k) C S)) Y.obj.obj := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  let D := DeletionCategory (k := k) C S
  let yS := survivingObj (k := k) C S hy
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  let E := finiteDimensionalModuleEvaluation (k := k) D yS
  have hzeroSummand (t : Fin dY.n) : IsZero (E.obj (dY.summand t)) := by
    by_contra hzero
    have hnontrivial : Nontrivial ((dY.summand t).obj.obj.obj yS) :=
      not_subsingleton_iff_nontrivial.mp fun hsub ↦
        hzero (ModuleCat.isZero_iff_subsingleton.mpr hsub)
    have hFnontrivial : Nontrivial ((F.obj (dY.summand t)).obj.obj.obj y) :=
      (moduleExtensionByZeroObjIsoAt (k := k) C S
        (dY.summand t).obj.obj yS).toLinearEquiv.toEquiv.nontrivial_congr.mpr
          hnontrivial
    have hFind : Indecomposable (F.obj (dY.summand t)) :=
      finiteDimensionalModuleExtensionByZero_indec
        (k := k) C S (dY.summand t) (dY.indecomposable t)
    have hseed : F.obj (dY.summand t) ∈
        (finiteFiberControlSeed hlocal y).isoClosure :=
      mem_finiteFiberControlSeed_isoClosure hlocal y hFind hFnontrivial
    have hcomponent : dY.inclusion t ≫ g ≠ 0 :=
      dY.inclusion_comp_ne_zero_of_isRightMinimal t g hgmin
    have hFcomponent : F.map (dY.inclusion t ≫ g) ≠ 0 := by
      intro hzeroMap
      exact hcomponent ((F.map_eq_zero_iff).mp hzeroMap)
    have hFZ : Indecomposable (F.obj Z) :=
      finiteDimensionalModuleExtensionByZero_indec (k := k) C S Z hZ
    have hone : F.obj Z ∈
        ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
          hlocal 1).isoClosure := by
      simpa only [FiniteIndecomposableModuleFamily.iterateHomNeighborhood] using
        (finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_ne_zero_to
          hlocal (n := 0) hseed hFZ
            (F.map (dY.inclusion t ≫ g)) hFcomponent
    have htwo : F.obj Z ∈
        ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
          hlocal 2).isoClosure :=
      (finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_homInteraction
        hlocal hone hFZ (Or.inl rfl)
    exact houtside htwo
  have hzeroSum : IsZero (⨁ fun t : Fin dY.n ↦ E.obj (dY.summand t)) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro t
    exact (hzeroSummand t).eq_of_tgt _ _
  letI : E.Additive := by
    dsimp only [E, finiteDimensionalModuleEvaluation]
    infer_instance
  have hzeroBiproduct : IsZero (E.obj (⨁ dY.summand)) :=
    hzeroSum.of_iso (E.mapBiproduct dY.summand)
  exact hzeroBiproduct.of_iso (E.mapIso dY.isoBiproduct)

/-- Outside the fixed ambient two-step core, a singleton deletion at a
surviving stage object preserves the sink's almost-split data, source arity,
and endpoint projectivity flag. -/
theorem finiteDeletion_sink_localData_unchanged_of_not_mem_deletionTwoStepModuleCore
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C) (S : Set C) (hy : y ∉ S)
    (hPstage : ∀ X : DeletionCategory (k := k) C S,
      IsFiniteDimensionalModule
        (C := DeletionCategory (k := k) C S) k
        (linearCoyonedaLinearModule (k := k) X))
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k)
        (DeletionCategory (k := k) C S)
        ({survivingObj (k := k) C S hy} :
          Set (DeletionCategory (k := k) C S))) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero
        (k := k) (DeletionCategory (k := k) C S)
        ({survivingObj (k := k) C S hy} :
          Set (DeletionCategory (k := k) C S))).obj Z)
    (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g)
    (hZ : Indecomposable
      ((finiteDimensionalModuleExtensionByZero
        (k := k) (DeletionCategory (k := k) C S)
        ({survivingObj (k := k) C S hy} :
          Set (DeletionCategory (k := k) C S))).obj Z))
    (houtside :
      (finiteDimensionalModuleExtensionByZero
        (k := k) (DeletionCategory (k := k) C S)
        ({survivingObj (k := k) C S hy} :
          Set (DeletionCategory (k := k) C S))).obj Z ∉
        deletionTwoStepModuleCore (k := k) C hlocal y S)
    (dY : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (dR : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (finiteVanishingModuleRestriction
        (k := k) (DeletionCategory (k := k) C S)
        ({survivingObj (k := k) C S hy} :
          Set (DeletionCategory (k := k) C S))
        ((finiteMaximalVanishingSubmoduleFunctor
          (k := k) (DeletionCategory (k := k) C S)
          ({survivingObj (k := k) C S hy} :
            Set (DeletionCategory (k := k) C S))).obj Y))) :
    IsRightAlmostSplit
        (finiteDeletionRightAdjointSinkCandidate
          (k := k) (DeletionCategory (k := k) C S)
          ({survivingObj (k := k) C S hy} :
            Set (DeletionCategory (k := k) C S)) g) ∧
      IsRightMinimal
        (finiteDeletionRightAdjointSinkCandidate
          (k := k) (DeletionCategory (k := k) C S)
          ({survivingObj (k := k) C S hy} :
            Set (DeletionCategory (k := k) C S)) g) ∧
      dR.n = dY.n ∧
      (Projective Z ↔
        Projective
          ((finiteDimensionalModuleExtensionByZero
            (k := k) (DeletionCategory (k := k) C S)
            ({survivingObj (k := k) C S hy} :
              Set (DeletionCategory (k := k) C S))).obj Z)) := by
  let D := DeletionCategory (k := k) C S
  let yS := survivingObj (k := k) C S hy
  have hY : ModuleVanishesOnDeleted
      (k := k) D ({yS} : Set D) Y.obj.obj :=
    rightMinimal_source_vanishesAt_of_not_mem_deletionTwoStepModuleCore
      (k := k) C hlocal y S hy dY g hgmin hZ houtside
  exact ⟨
    finiteDeletionRightAdjointSinkCandidate_isRightAlmostSplit
      (k := k) D ({yS} : Set D) g hg,
    finiteDeletionRightAdjointSinkCandidate_isRightMinimal_of_source_vanishes
      (k := k) D ({yS} : Set D) g hgmin hY,
    finiteMaximalVanishingSubmoduleRestriction_arity_eq_of_vanishesOnDeleted
      (k := k) D ({yS} : Set D) Y hY dY dR,
    finiteDeletion_projective_iff_of_minimal_sink_source_vanishes
      (k := k) D ({yS} : Set D) hPstage g hg hgmin hY⟩

/-- Every indecomposable deletion-stage module nonzero at a surviving object
belongs to the two-step core centered at that object.  In particular, every
module removed by the next object deletion is already inside the endpoint
core used by finite push-down. -/
theorem mem_deletionTwoStepModuleCore_of_nontrivial_at
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C) (S : Set C) (hy : y ∉ S)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k)
    (hM : Indecomposable M)
    (hMy : Nontrivial
      (M.obj.obj.obj (survivingObj (k := k) C S hy))) :
    M ∈ deletionTwoStepModuleCore (k := k) C hlocal y S := by
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  have hFM : Indecomposable (F.obj M) :=
    finiteDimensionalModuleExtensionByZero_indec (k := k) C S M hM
  have hFMy : Nontrivial ((F.obj M).obj.obj.obj y) := by
    exact (moduleExtensionByZeroObjIsoAt (k := k) C S M.obj.obj
      (survivingObj (k := k) C S hy)).toLinearEquiv.toEquiv.nontrivial_congr.mpr
        hMy
  have h₀ : F.obj M ∈ (finiteFiberControlSeed hlocal y).isoClosure :=
    mem_finiteFiberControlSeed_isoClosure hlocal y hFM hFMy
  have h₁ : F.obj M ∈
      ((finiteFiberControlSeed hlocal y).iterateHomNeighborhood
        hlocal 1).isoClosure :=
    (finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_homInteraction
      hlocal h₀ hFM (Or.inl rfl)
  exact
    (finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_homInteraction
      hlocal h₁ hFM (Or.inl rfl)

/-- Every indecomposable deletion-stage module interacting with the surviving
two-step core belongs to the surviving three-step family, hence to its
additive control window. -/
theorem deletionTwoStepModuleCore_interactionNeighborhood_subset
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (y : C) (S : Set C) :
    CoveringSeparation.interactionNeighborhood
        (fun M N ↦ Indecomposable N ∧
          CoveringSeparation.homInteraction M N)
        (deletionTwoStepModuleCore (k := k) C hlocal y S) ⊆
      (deletionSurvivingModuleFamily (k := k) C
        (finiteThreeStepControlFamily hlocal y) S).additiveClosure := by
  intro N hN
  obtain ⟨M, hM, hNind, hMN⟩ := hN
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  have hFNind : Indecomposable (F.obj N) :=
    finiteDimensionalModuleExtensionByZero_indec (k := k) C S N hNind
  have hFMN : CoveringSeparation.homInteraction (F.obj M) (F.obj N) :=
    homInteraction_extensionByZero (k := k) C S hMN
  have hFN : F.obj N ∈
      (finiteThreeStepControlFamily hlocal y).isoClosure :=
    (finiteFiberControlSeed hlocal y).mem_iterateHomNeighborhood_succ_of_homInteraction
      hlocal hM hFNind hFMN
  apply (deletionSurvivingModuleFamily (k := k) C
    (finiteThreeStepControlFamily hlocal y) S).isoClosure_subset_additiveClosure
  exact (mem_deletionSurvivingModuleFamily_isoClosure_iff
    (k := k) C (finiteThreeStepControlFamily hlocal y) S N).2 hFN

end MagnitudeConjecture.ObjectDeletion
