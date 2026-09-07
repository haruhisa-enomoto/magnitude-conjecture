import MagnitudeConjecture.CategoryTheory.FiniteOrbitARComponentExhaustion
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStagePushedLocalChange

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]

/-- Every indecomposable downstairs module nonzero at the orbit deleted in
this stage is represented by the pushed two-step support family. -/
theorem stagePushedTwoStepModuleFamily_mem_isoClosure_of_nontrivial
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G)) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let y := stageNextObject (k := k) R x i
    let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
      (Quotient.mk'' y : MulAction.orbitRel.Quotient
        (N : Subgroup G) C₀)
    let P₂ := stagePushedTwoStepModuleFamily
      (k := k) (C := C) D hC hrep N R x i havoid
    ∀ (Y : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C₀ (N : Subgroup G)) k),
      Indecomposable Y → Nontrivial (Y.obj.obj.obj q) →
        Y ∈ P₂.isoClosure := by
  dsimp
  let S := stageDeletedSet (N : Subgroup G)
    R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
  haveI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G) C) :=
    CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  haveI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)) :=
    finite_deletionOrbitQuotient (k := k) C S
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) R.representative x i.castSucc)
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
    (Quotient.mk'' y : MulAction.orbitRel.Quotient
      (N : Subgroup G) C₀)
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let P₂ := stagePushedTwoStepModuleFamily
    (k := k) (C := C) D hC hrep N R x i havoid
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hIstage := fun X ↦
    deletion_dualLinearYoneda_isFiniteDimensional (k := k) C hI S X
  let hlocalStage := fun X ↦
    deletion_end_isLocalRing (k := k) C hC hlocal S X
  let hrepStage := isLocallyRepresentationFinite_deletion
    (k := k) C S hrep
  let hfreeStage :=
    Dstage.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hPstage hlocalStage
  let hDensity :=
    Dstage.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
      (k := k) hPstage hIstage hlocalStage hfreeStage hrepStage
  intro Y hY hYq
  obtain ⟨V, hV, _, hVy, ⟨e⟩⟩ :=
    Dstage.finiteOrbitPushdown_exists_seed_lift_of_nontrivial
      hrepStage hDensity y Y hY hYq
  have hVW₂ : V ∈ W₂.isoClosure := by
    rw [mem_stageTwoStepModuleFamily_isoClosure_iff
      (k := k) hrep R x i V]
    exact mem_deletionTwoStepModuleCore_of_nontrivial_at
      (k := k) C hrep (R.representative i • x) S
        (R.representative_smul_not_mem_stageDeletedSet x i) V
        hV hVy
  obtain ⟨t, ⟨s⟩⟩ := hVW₂
  refine ⟨t, ⟨?_⟩⟩
  exact Dstage.finiteDimensionalModuleOrbitSkeletonPushdown.mapIso s ≪≫ e

/-- If an indecomposable downstairs source is nonzero at the orbit deleted
in this stage, every indecomposable target of a nonzero map from it is
represented by the pushed two-step support family. -/
theorem stagePushedTwoStepModuleFamily_mem_isoClosure_of_ne_zero_from_nontrivial
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G)) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let y := stageNextObject (k := k) R x i
    let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
      (Quotient.mk'' y : MulAction.orbitRel.Quotient
        (N : Subgroup G) C₀)
    let P₂ := stagePushedTwoStepModuleFamily
      (k := k) (C := C) D hC hrep N R x i havoid
    ∀ (X Y : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C₀ (N : Subgroup G)) k),
      Indecomposable X → Nontrivial (X.obj.obj.obj q) →
      Indecomposable Y → ∀ (f : X ⟶ Y), f ≠ 0 →
        Y ∈ P₂.isoClosure := by
  dsimp
  let S := stageDeletedSet (N : Subgroup G)
    R.representative x i.castSucc
  let y₀ := R.representative i • x
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
  haveI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G) C) :=
    CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  haveI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)) :=
    finite_deletionOrbitQuotient (k := k) C S
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) R.representative x i.castSucc)
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
    (Quotient.mk'' y : MulAction.orbitRel.Quotient
      (N : Subgroup G) C₀)
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let P₂ := stagePushedTwoStepModuleFamily
    (k := k) (C := C) D hC hrep N R x i havoid
  let hPstage := fun Z ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S Z
  let hIstage := fun Z ↦
    deletion_dualLinearYoneda_isFiniteDimensional (k := k) C hI S Z
  let hlocalStage := fun Z ↦
    deletion_end_isLocalRing (k := k) C hC hlocal S Z
  let hrepStage := isLocallyRepresentationFinite_deletion
    (k := k) C S hrep
  let hfreeStage :=
    Dstage.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hPstage hlocalStage
  let hDensity :=
    Dstage.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
      (k := k) hPstage hIstage hlocalStage hfreeStage hrepStage
  let H := finiteFiberControlSeed hrep y₀
  let U : Set (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C₀) k) :=
    deletionStageModuleCore (k := k) C S H.isoClosure
  let W : Set (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C₀) k) :=
    deletionTwoStepModuleCore (k := k) C hrep y₀ S
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  have hUW : CoveringSeparation.interactionNeighborhood
      (fun M Z ↦ Indecomposable Z ∧
        CoveringSeparation.homInteraction M Z) U ⊆ W := by
    intro Z hZ
    obtain ⟨M, hMU, hZind, hMZ⟩ := hZ
    change F.obj M ∈ H.isoClosure at hMU
    have hFZind : Indecomposable (F.obj Z) :=
      finiteDimensionalModuleExtensionByZero_indec (k := k) C S Z hZind
    have hFMZ : CoveringSeparation.homInteraction (F.obj M) (F.obj Z) :=
      homInteraction_extensionByZero (k := k) C S hMZ
    have hFZone : F.obj Z ∈ (H.iterateHomNeighborhood hrep 1).isoClosure := by
      simpa only [FiniteIndecomposableModuleFamily.iterateHomNeighborhood] using
        H.mem_iterateHomNeighborhood_succ_of_homInteraction
          hrep (n := 0) hMU hFZind hFMZ
    exact H.mem_iterateHomNeighborhood_succ_of_homInteraction
      hrep hFZone hFZind (Or.inl rfl)
  intro X Y hX hXq hY f hf
  obtain ⟨V, hV, _, hVy, ⟨eX⟩⟩ :=
    Dstage.finiteOrbitPushdown_exists_seed_lift_of_nontrivial
      hrepStage hDensity y X hX hXq
  have hFV : Indecomposable (F.obj V) :=
    finiteDimensionalModuleExtensionByZero_indec (k := k) C S V hV
  have hFVy : Nontrivial ((F.obj V).obj.obj.obj y₀) :=
    (moduleExtensionByZeroObjIsoAt (k := k) C S V.obj.obj y).toLinearEquiv.toEquiv
      |>.nontrivial_congr.mpr hVy
  have hVU : V ∈ U :=
    mem_finiteFiberControlSeed_isoClosure hrep y₀ hFV hFVy
  have hVW : V ∈ W := by
    exact H.mem_iterateHomNeighborhood_succ_of_homInteraction hrep
      (H.mem_iterateHomNeighborhood_succ_of_homInteraction hrep
        hVU hFV (Or.inl rfl)) hFV (Or.inl rfl)
  let Vw : CoveringSeparation.WindowCategory W := ⟨V, hVW⟩
  have hef : eX.hom ≫ f ≠ 0 := by
    intro hzero
    apply hf
    apply (cancel_epi eX.hom).1
    simpa using hzero
  obtain ⟨Z, ⟨eY⟩⟩ :=
    Dstage.finiteOrbitPushdownWindow_exists_target_lift_of_ne_zero
      U W hUW hDensity Vw hVU Y hY (eX.hom ≫ f) hef
  have hZW₂ : Z.1 ∈ W₂.isoClosure := by
    rw [mem_stageTwoStepModuleFamily_isoClosure_iff
      (k := k) hrep R x i Z.1]
    exact Z.2
  obtain ⟨t, ⟨s⟩⟩ := hZW₂
  refine ⟨t, ⟨?_⟩⟩
  exact Dstage.finiteDimensionalModuleOrbitSkeletonPushdown.mapIso s ≪≫ eY

/-- The source of a right-minimal map to an indecomposable outside the
pushed two-step family vanishes at the orbit deleted in this stage. -/
theorem stagePushedTwoStepModuleFamily_source_vanishes_of_not_mem
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G)) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let y := stageNextObject (k := k) R x i
    let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
      (Quotient.mk'' y : MulAction.orbitRel.Quotient
        (N : Subgroup G) C₀)
    let P₂ := stagePushedTwoStepModuleFamily
      (k := k) (C := C) D hC hrep N R x i havoid
    ∀ {Y Z : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C₀ (N : Subgroup G)) k}
      (_dY : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
      (g : Y ⟶ Z) (_hgmin : IsRightMinimal g) (_hZ : Indecomposable Z),
      Z ∉ P₂.isoClosure →
        ModuleVanishesOnDeleted
          (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
          ({q} : Set (DeckOrbitSkeleton C₀ (N : Subgroup G))) Y.obj.obj := by
  dsimp
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
    (Quotient.mk'' y : MulAction.orbitRel.Quotient
      (N : Subgroup G) C₀)
  let P₂ := stagePushedTwoStepModuleFamily
    (k := k) (C := C) D hC hrep N R x i havoid
  intro Y Z dY g hgmin hZ houtside z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  let E := finiteDimensionalModuleEvaluation
    (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G)) q
  have hzeroSummand (t : Fin dY.n) : IsZero (E.obj (dY.summand t)) := by
    by_contra hzero
    have hnontrivial : Nontrivial ((dY.summand t).obj.obj.obj q) :=
      not_subsingleton_iff_nontrivial.mp fun hsub ↦
        hzero (ModuleCat.isZero_iff_subsingleton.mpr hsub)
    have hcomponent : dY.inclusion t ≫ g ≠ 0 :=
      dY.inclusion_comp_ne_zero_of_isRightMinimal t g hgmin
    exact houtside
      (stagePushedTwoStepModuleFamily_mem_isoClosure_of_ne_zero_from_nontrivial
        (k := k) (C := C) D hC hP hI hlocal hrep N R x i havoid
        (dY.summand t) Z (dY.indecomposable t) hnontrivial hZ
          (dY.inclusion t ≫ g) hcomponent)
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

/-- The downstairs singleton-deletion local change vanishes away from the
pushed two-step support family. -/
theorem stagePushedTwoStepModuleFamily_localChangeAt_eq_zero_of_not_mem
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G)) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let y := stageNextObject (k := k) R x i
    let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
      (Quotient.mk'' y : MulAction.orbitRel.Quotient
        (N : Subgroup G) C₀)
    let P₂ := stagePushedTwoStepModuleFamily
      (k := k) (C := C) D hC hrep N R x i havoid
    let Down := stageFiniteOrbitModuleIndecomposableSkeleton
      (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
    ∀ (Y : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C₀ (N : Subgroup G)) k)
      (hY : Indecomposable Y),
      Y ∉ P₂.isoClosure →
        finiteDeletionLocalChangeAt
          (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
          Down.isLocallyRepresentationFinite ({q} : Set _) Y hY = 0 := by
  dsimp
  let S := stageDeletedSet (N : Subgroup G)
    R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
    (Quotient.mk'' y : MulAction.orbitRel.Quotient
      (N : Subgroup G) C₀)
  let P₂ := stagePushedTwoStepModuleFamily
    (k := k) (C := C) D hC hrep N R x i havoid
  let Down := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hPdown := Dstage.orbitSkeletonLinearCoyonedaFinite (k := k) hPstage
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C₀ (N : Subgroup G)) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  intro Y hY houtside
  have hYvanish : ModuleVanishesOnDeleted
      (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
      ({q} : Set (DeckOrbitSkeleton C₀ (N : Subgroup G))) Y.obj.obj := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    by_contra hzero
    have hnontrivial : Nontrivial (Y.obj.obj.obj q) :=
      not_subsingleton_iff_nontrivial.mp fun hsub ↦
        hzero (ModuleCat.isZero_iff_subsingleton.mpr hsub)
    exact houtside
      (stagePushedTwoStepModuleFamily_mem_isoClosure_of_nontrivial
        (k := k) (C := C) D hC hP hI hlocal hrep N R x i havoid
          Y hY hnontrivial)
  let A := finiteModuleMinimalSinkData
    Down.isLocallyRepresentationFinite Y hY
  have hsource : ModuleVanishesOnDeleted
      (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
      ({q} : Set (DeckOrbitSkeleton C₀ (N : Subgroup G))) A.source.obj.obj :=
    stagePushedTwoStepModuleFamily_source_vanishes_of_not_mem
      (k := k) (C := C) D hC hP hI hlocal hrep N R x i havoid
        A.decomposition A.map A.rightMinimal hY houtside
  exact finiteDeletionLocalChangeAt_eq_zero_of_minimalSink_source_vanishes
    (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
      hPdown Down.isLocallyRepresentationFinite ({q} : Set _)
      Y hY hYvanish A.map A.rightAlmostSplit A.rightMinimal
        A.decomposition hsource

end MagnitudeConjecture.ObjectDeletion
