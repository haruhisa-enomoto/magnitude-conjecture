import MagnitudeConjecture.CategoryTheory.FiniteDeletionSupportLocalChangeSum
import MagnitudeConjecture.CategoryTheory.FiniteModuleFamilyFunctor
import MagnitudeConjecture.CategoryTheory.ObjectDeletionDeckOrbit
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageDownstairsSkeleton
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageIntrinsicLocalDensity
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageLocalChange

/-!
# Pushing the finite stage-local change family downstairs

The surviving two-step family which supports singleton deletion change is
contained in the surviving three-step additive control window.  The separated
finite push-down therefore sends every chosen member to an indecomposable and
is full and faithful on the surrounding window.  This gives a literal finite
family downstairs with exactly the same represented isomorphism classes.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]

omit [IsCancelSMul G C] in
/-- Every chosen member of the stage two-step support family belongs to the
surviving three-step additive control window. -/
theorem stageTwoStepModuleFamily_obj_mem_threeStepAdditiveClosure
    {N : Subgroup G} [N.Normal]
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (R : FiniteQuotientRepresentatives N) (x : C) (i : Fin R.m)
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n) :
    (stageTwoStepModuleFamily (k := k) hrep R x i).obj t ∈
      (deletionSurvivingModuleFamily (k := k) C
        (finiteThreeStepControlFamily hrep (R.representative i • x))
        (stageDeletedSet N R.representative x i.castSucc)).additiveClosure := by
  let S := stageDeletedSet N R.representative x i.castSucc
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let W₃ := deletionSurvivingModuleFamily (k := k) C
    (finiteThreeStepControlFamily hrep (R.representative i • x)) S
  apply deletionTwoStepModuleCore_interactionNeighborhood_subset
    (k := k) C hrep (R.representative i • x) S
  refine ⟨W₂.obj t, ?_, W₂.indecomposable t, Or.inl rfl⟩
  exact (mem_stageTwoStepModuleFamily_isoClosure_iff
    (k := k) hrep R x i (W₂.obj t)).1 (W₂.obj_mem_isoClosure t)

/-- A finite representable and a nonzero local endomorphism ring ensure that
the chosen fiber seed has an actual representative nonzero at its base
object. -/
theorem exists_finiteFiberControlSeed_obj_nontrivial
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C)) (X : C)
    (hP : IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hEnd : IsLocalRing (End X)) :
    ∃ i : Fin (finiteFiberControlSeed hrep X).n,
      Nontrivial ((finiteFiberControlSeed hrep X).obj i |>.obj.obj.obj X) := by
  classical
  let P : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
    ⟨linearCoyonedaLinearModule (k := k) X, hP⟩
  obtain ⟨d⟩ := finiteDimensionalModule_finiteIndecomposableDecomposition P
  let E := finiteDimensionalModuleEvaluation (k := k) C X
  have hPX : Nontrivial (P.obj.obj.obj X) := by
    change Nontrivial (End X)
    letI : IsLocalRing (End X) := hEnd
    infer_instance
  have hsummand : ∃ t : Fin d.n,
      Nontrivial ((d.summand t).obj.obj.obj X) := by
    by_contra hall
    push Not at hall
    have hzero (t : Fin d.n) : IsZero (E.obj (d.summand t)) :=
      ModuleCat.isZero_iff_subsingleton.mpr (hall t)
    have hzeroSum : IsZero (⨁ fun t : Fin d.n ↦ E.obj (d.summand t)) := by
      rw [IsZero.iff_id_eq_zero]
      apply biproduct.hom_ext
      intro t
      exact (hzero t).eq_of_tgt _ _
    letI : E.Additive := by
      dsimp only [E, finiteDimensionalModuleEvaluation]
      infer_instance
    have hzeroBiproduct : IsZero (E.obj (⨁ d.summand)) :=
      hzeroSum.of_iso (E.mapBiproduct d.summand)
    have hzeroP : IsZero (E.obj P) :=
      hzeroBiproduct.of_iso (E.mapIso d.isoBiproduct)
    exact (not_nontrivial_iff_subsingleton.mpr
      (ModuleCat.isZero_iff_subsingleton.mp hzeroP)) hPX
  obtain ⟨t, ht⟩ := hsummand
  obtain ⟨i, _hi⟩ := mem_finiteFiberControlSeed_isoClosure
    hrep X (d.indecomposable t) ht
  exact ⟨i, finiteFiberControlSeed_obj_nontrivial hrep X i⟩

/-- Under the stage separation certificate, any stage module whose ambient
extension belongs to the three-step control family can be nonzero on the next
deleted subgroup orbit only at its distinguished representative. -/
theorem stageThreeStepModule_nontrivial_at_smul_imp_eq_one
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) k)
    (hMthree :
      (finiteDimensionalModuleExtensionByZero (k := k) C
        (stageDeletedSet (N : Subgroup G)
          R.representative x i.castSucc)).obj M ∈
        (finiteThreeStepControlFamily hrep
          (R.representative i • x)).isoClosure)
    (n : (N : Subgroup G)) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    Nontrivial
        (M.obj.obj.obj (n • stageNextObject (k := k) R x i)) →
      n = 1 := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
  let y₀ := R.representative i • x
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let H := finiteFiberControlSeed hrep y₀
  let U := finiteThreeStepControlFamily hrep y₀
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  intro hMny
  by_contra hn
  have hgne : (n : G) ≠ 1 := by
    intro h
    exact hn (Subtype.ext h)
  obtain ⟨s, hs⟩ := exists_finiteFiberControlSeed_obj_nontrivial
    (k := k) hrep y₀ (hP y₀) (hlocal y₀)
  have hs₀ : H.obj s ∈ (H.iterateHomNeighborhood hrep 0).isoClosure := by
    exact H.obj_mem_isoClosure s
  have hs₁ : H.obj s ∈ (H.iterateHomNeighborhood hrep 1).isoClosure := by
    exact H.mem_iterateHomNeighborhood_succ_of_homInteraction
      hrep hs₀ (H.indecomposable s) (Or.inl rfl)
  have hs₂ : H.obj s ∈ (H.iterateHomNeighborhood hrep 2).isoClosure := by
    exact H.mem_iterateHomNeighborhood_succ_of_homInteraction
      hrep hs₁ (H.indecomposable s) (Or.inl rfl)
  have hs₃ : H.obj s ∈ U.isoClosure := by
    exact H.mem_iterateHomNeighborhood_succ_of_homInteraction
      hrep hs₂ (H.indecomposable s) (Or.inl rfl)
  obtain ⟨p, ⟨ep⟩⟩ := hs₃
  obtain ⟨q, ⟨eq⟩⟩ := hMthree
  let J := (IsFiniteDimensionalModule.{u, v, v, v} (C := C) k).ι
  let K := (IsLinearModule.{u, v, v, v} (C := C) k).ι
  have hpy : y₀ ∈ moduleSupport k (U.obj p).obj.obj := by
    let epX := (K.mapIso (J.mapIso ep)).app y₀
    exact epX.toLinearEquiv.toEquiv.nontrivial_congr.mpr hs
  have hstageSupport : n • y ∈ moduleSupport k M.obj.obj := hMny
  have hambientSupport : (n : G) • y₀ ∈
      moduleSupport k (F.obj M).obj.obj := by
    change (n : G) • y₀ ∈ moduleSupport k
      (moduleExtensionByZero C S M.obj.obj)
    have h := mem_moduleSupport_moduleExtensionByZero_of_mem
      (k := k) C S M.obj (n • y) hstageSupport
    change (n : G) • y.obj.as ∈
      moduleSupport k (moduleExtensionByZero C S M.obj.obj) at h
    have hy : y.obj.as = y₀ := rfl
    simpa only [hy] using h
  have hqny : (n : G) • y₀ ∈ moduleSupport k (U.obj q).obj.obj := by
    let eqX := (K.mapIso (J.mapIso eq)).app ((n : G) • y₀)
    exact eqX.toLinearEquiv.toEquiv.nontrivial_congr.mpr hambientSupport
  have hbad : (n : G) ∈
      finiteModuleFamilySupportBadDegrees (G := G) U :=
    ⟨hgne, p, q, y₀, hpy, hqny⟩
  exact (havoid (n : G) hbad n.property).elim

/-- Under the stage separation certificate, a member of the two-step family
can be nonzero on the next deleted subgroup orbit only at its distinguished
representative. -/
theorem stageTwoStepModuleFamily_nontrivial_at_smul_imp_eq_one
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n)
    (n : (N : Subgroup G)) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    Nontrivial
        ((stageTwoStepModuleFamily (k := k) hrep R x i).obj t |>.obj.obj.obj
          (n • stageNextObject (k := k) R x i)) →
      n = 1 := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y₀ := R.representative i • x
  let H := finiteFiberControlSeed hrep y₀
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  have hFM₂ : F.obj (W₂.obj t) ∈
      (H.iterateHomNeighborhood hrep 2).isoClosure := by
    exact deletionSurvivingModuleFamily_extension_mem_isoClosure
      (k := k) C (H.iterateHomNeighborhood hrep 2) S t
  have hFMind : Indecomposable (F.obj (W₂.obj t)) :=
    (finiteDimensionalModuleExtensionByZero_indec_iff
      (k := k) C S (W₂.obj t)).2 (W₂.indecomposable t)
  have hFM₃ : F.obj (W₂.obj t) ∈
      (finiteThreeStepControlFamily hrep y₀).isoClosure := by
    exact H.mem_iterateHomNeighborhood_succ_of_homInteraction
      hrep hFM₂ hFMind (Or.inl rfl)
  exact stageThreeStepModule_nontrivial_at_smul_imp_eq_one
    (k := k) hP hlocal hrep N R x i havoid (W₂.obj t) hFM₃ n

/-- A two-step endpoint which survives singleton deletion at the
distinguished representative also vanishes on all remaining objects of that
subgroup orbit. -/
theorem stageTwoStepRestriction_vanishesOn_remainingOrbit
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n)
    (hvanish : ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      ({stageNextObject (k := k) R x i} :
        Set (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc))
      ((stageTwoStepModuleFamily (k := k) hrep R x i).obj t).obj.obj) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    ModuleVanishesOnDeleted
      (k := k)
      (DeletionCategory (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)))
      (AdditionalDeleted (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc))
        (StageAdditionalDeleted (k := k) (N : Subgroup G)
          R.representative x i))
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc))
        ((stageTwoStepModuleFamily (k := k) hrep R x i).obj t)
        hvanish).obj.obj := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y₀ := R.representative i • x
  let y := stageNextObject (k := k) R x i
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let M := W₂.obj t
  let Z := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C₀ ({y} : Set C₀) M hvanish
  let F₁ := finiteDimensionalModuleExtensionByZero
    (k := k) C₀ ({y} : Set C₀)
  let eZ := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C₀ ({y} : Set C₀) M hvanish
  intro z hz
  by_contra hzero
  have hzNontrivial : Nontrivial (Z.obj.obj.obj z) :=
    not_subsingleton_iff_nontrivial.mp fun hsub ↦
      hzero (ModuleCat.isZero_iff_subsingleton.mpr hsub)
  have hF₁z : Nontrivial ((F₁.obj Z).obj.obj.obj z.obj.as) :=
    (moduleExtensionByZeroObjIsoAt (k := k) C₀ ({y} : Set C₀)
      Z.obj.obj z).toLinearEquiv.toEquiv.nontrivial_congr.mpr hzNontrivial
  let J := (IsFiniteDimensionalModule.{u, v, v, v} (C := C₀) k).ι
  let K := (IsLinearModule.{u, v, v, v} (C := C₀) k).ι
  have hMz : Nontrivial (M.obj.obj.obj z.obj.as) := by
    let ez := (K.mapIso (J.mapIso eZ)).app z.obj.as
    exact ez.toLinearEquiv.toEquiv.nontrivial_congr.mp hF₁z
  change z.obj.as ∈ StageAdditionalDeleted (k := k)
    (N : Subgroup G) R.representative x i at hz
  change z.obj.as.obj.as ∈ subgroupOrbit (N : Subgroup G) y₀ at hz
  obtain ⟨n, hn⟩ := hz
  have hnStage : n • y = z.obj.as := by
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    have hy : y.obj.as = y₀ := rfl
    simpa only [deletion_smul_obj_as, MulAction.subgroup_smul_def, hy] using hn
  have hMny : Nontrivial (M.obj.obj.obj (n • y)) := by
    simpa only [hnStage] using hMz
  have hnOne := stageTwoStepModuleFamily_nontrivial_at_smul_imp_eq_one
    (k := k) hP hlocal hrep N R x i havoid t n hMny
  have hzy : z.obj.as = y := by
    rw [← hnStage, hnOne, one_smul]
  exact z.property (by simpa only [Set.mem_singleton_iff] using hzy)

/-- After singleton deletion at the distinguished representative, the source
of any right-minimal sink ending at a surviving two-step endpoint vanishes on
the rest of the subgroup orbit. -/
theorem stageSingletonSinkSource_vanishesOn_remainingOrbit
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n)
    (hvanish : ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      ({stageNextObject (k := k) R x i} :
        Set (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc))
      ((stageTwoStepModuleFamily (k := k) hrep R x i).obj t).obj.obj)
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc))) k}
    (g : Y ⟶ finiteDimensionalModuleRestrictionToDeletion
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      ({stageNextObject (k := k) R x i} :
        Set (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc))
      ((stageTwoStepModuleFamily (k := k) hrep R x i).obj t) hvanish)
    (hgmin : IsRightMinimal g)
    (dY : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    ModuleVanishesOnDeleted
      (k := k)
      (DeletionCategory (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)))
      (AdditionalDeleted (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc))
        (StageAdditionalDeleted (k := k) (N : Subgroup G)
          R.representative x i))
      Y.obj.obj := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y₀ := R.representative i • x
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let H := finiteFiberControlSeed hrep y₀
  let F₀ := finiteDimensionalModuleExtensionByZero (k := k) C S
  let F₁ := finiteDimensionalModuleExtensionByZero
    (k := k) C₀ ({y} : Set C₀)
  let Z := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C₀ ({y} : Set C₀) (W₂.obj t) hvanish
  let eZ := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C₀ ({y} : Set C₀) (W₂.obj t) hvanish
  have hMtwo : F₀.obj (W₂.obj t) ∈
      (H.iterateHomNeighborhood hrep 2).isoClosure := by
    exact deletionSurvivingModuleFamily_extension_mem_isoClosure
      (k := k) C (H.iterateHomNeighborhood hrep 2) S t
  have hsourceThree (r : Fin dY.n) :
      F₀.obj (F₁.obj (dY.summand r)) ∈
        (finiteThreeStepControlFamily hrep y₀).isoClosure := by
    have hcomponent : dY.inclusion r ≫ g ≠ 0 :=
      dY.inclusion_comp_ne_zero_of_isRightMinimal r g hgmin
    have hF₁component : F₁.map (dY.inclusion r ≫ g) ≠ 0 := by
      intro hzero
      exact hcomponent ((F₁.map_eq_zero_iff).mp hzero)
    let component : F₁.obj (dY.summand r) ⟶ W₂.obj t :=
      F₁.map (dY.inclusion r ≫ g) ≫ eZ.hom
    have hcomponent' : component ≠ 0 := by
      intro hzero
      apply hF₁component
      apply (cancel_mono eZ.hom).1
      simpa only [zero_comp] using hzero
    have hF₀component : F₀.map component ≠ 0 := by
      intro hzero
      exact hcomponent' ((F₀.map_eq_zero_iff).mp hzero)
    have hind : Indecomposable (F₀.obj (F₁.obj (dY.summand r))) :=
      finiteDimensionalModuleExtensionByZero_indec
        (k := k) C S (F₁.obj (dY.summand r))
        (finiteDimensionalModuleExtensionByZero_indec
          (k := k) C₀ ({y} : Set C₀) (dY.summand r)
          (dY.indecomposable r))
    exact H.mem_iterateHomNeighborhood_succ_of_ne_zero_from
      hrep hMtwo hind (F₀.map component) hF₀component
  intro z hz
  let E := finiteDimensionalModuleEvaluation (k := k)
    (DeletionCategory (k := k) C₀ ({y} : Set C₀)) z
  have hzeroSummand (r : Fin dY.n) : IsZero (E.obj (dY.summand r)) := by
    by_contra hzero
    have hzNontrivial : Nontrivial ((dY.summand r).obj.obj.obj z) :=
      not_subsingleton_iff_nontrivial.mp fun hsub ↦
        hzero (ModuleCat.isZero_iff_subsingleton.mpr hsub)
    have hF₁z : Nontrivial
        ((F₁.obj (dY.summand r)).obj.obj.obj z.obj.as) :=
      (moduleExtensionByZeroObjIsoAt (k := k) C₀ ({y} : Set C₀)
        (dY.summand r).obj.obj z).toLinearEquiv.toEquiv.nontrivial_congr.mpr
          hzNontrivial
    change z.obj.as ∈ StageAdditionalDeleted (k := k)
      (N : Subgroup G) R.representative x i at hz
    change z.obj.as.obj.as ∈ subgroupOrbit (N : Subgroup G) y₀ at hz
    obtain ⟨n, hn⟩ := hz
    have hnStage : n • y = z.obj.as := by
      apply ObjectProperty.FullSubcategory.ext
      apply CategoryTheory.Quotient.ext
      have hy : y.obj.as = y₀ := rfl
      simpa only [deletion_smul_obj_as, MulAction.subgroup_smul_def, hy] using hn
    have hF₁ny : Nontrivial
        ((F₁.obj (dY.summand r)).obj.obj.obj (n • y)) := by
      simpa only [hnStage] using hF₁z
    have hnOne := stageThreeStepModule_nontrivial_at_smul_imp_eq_one
      (k := k) hP hlocal hrep N R x i havoid
        (F₁.obj (dY.summand r)) (hsourceThree r) n hF₁ny
    have hzy : z.obj.as = y := by
      rw [← hnStage, hnOne, one_smul]
    exact z.property (by simpa only [Set.mem_singleton_iff] using hzy)
  have hzeroSum : IsZero (⨁ fun r : Fin dY.n ↦ E.obj (dY.summand r)) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro r
    exact (hzeroSummand r).eq_of_tgt _ _
  letI : E.Additive := by
    dsimp only [E, finiteDimensionalModuleEvaluation]
    infer_instance
  have hzeroBiproduct : IsZero (E.obj (⨁ dY.summand)) :=
    hzeroSum.of_iso (E.mapBiproduct dY.summand)
  exact hzeroBiproduct.of_iso (E.mapIso dY.isoBiproduct)

/-- For a surviving two-step endpoint, deleting the rest of the next
subgroup orbit after singleton deletion does not change intrinsic local
density. -/
theorem stageTwoStepRestriction_remainingOrbitExtendedLocalDensity
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n)
    (hvanish : ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      ({stageNextObject (k := k) R x i} :
        Set (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc))
      ((stageTwoStepModuleFamily (k := k) hrep R x i).obj t).obj.obj) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let y := stageNextObject (k := k) R x i
    let C₁ := DeletionCategory (k := k) C₀ ({y} : Set C₀)
    let T := AdditionalDeleted (k := k) C₀ ({y} : Set C₀)
      (StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i)
    let M := (stageTwoStepModuleFamily (k := k) hrep R x i).obj t
    let Z := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C₀ ({y} : Set C₀) M hvanish
    let hZ := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C₀ ({y} : Set C₀) M
        ((stageTwoStepModuleFamily (k := k) hrep R x i).indecomposable t)
        hvanish
    let hlocal₀ := isLocallyRepresentationFinite_deletion
      (k := k) C
      (stageDeletedSet (N : Subgroup G) R.representative x i.castSucc) hrep
    let hlocal₁ := isLocallyRepresentationFinite_deletion
      (k := k) C₀ ({y} : Set C₀) hlocal₀
    finiteDeletionExtendedLocalDensity (k := k) C₁ hlocal₁ T Z hZ =
      finiteModuleLocalDensity hlocal₁ Z hZ := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let C₁ := DeletionCategory (k := k) C₀ ({y} : Set C₀)
  let T := AdditionalDeleted (k := k) C₀ ({y} : Set C₀)
    (StageAdditionalDeleted (k := k) (N : Subgroup G)
      R.representative x i)
  let M := (stageTwoStepModuleFamily (k := k) hrep R x i).obj t
  let Z := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C₀ ({y} : Set C₀) M hvanish
  let hZ : Indecomposable Z :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C₀ ({y} : Set C₀) M
        ((stageTwoStepModuleFamily (k := k) hrep R x i).indecomposable t)
        hvanish
  let hlocal₀ := isLocallyRepresentationFinite_deletion
    (k := k) C S hrep
  let hlocal₁ := isLocallyRepresentationFinite_deletion
    (k := k) C₀ ({y} : Set C₀) hlocal₀
  have hremaining : ModuleVanishesOnDeleted
      (k := k) C₁ T Z.obj.obj :=
    stageTwoStepRestriction_vanishesOn_remainingOrbit
      (k := k) hP hlocal hrep N R x i havoid t hvanish
  let A := finiteModuleMinimalSinkData hlocal₁ Z hZ
  have hsource : ModuleVanishesOnDeleted
      (k := k) C₁ T A.source.obj.obj :=
    stageSingletonSinkSource_vanishesOn_remainingOrbit
      (k := k) hP hlocal hrep N R x i havoid t hvanish
        A.map A.rightMinimal A.decomposition
  let hP₀ := fun X ↦ deletion_linearCoyoneda_isFiniteDimensional
    (k := k) C hP S X
  let hP₁ := fun X ↦ deletion_linearCoyoneda_isFiniteDimensional
    (k := k) C₀ hP₀ ({y} : Set C₀) X
  have hDensity :=
    finiteDeletion_restriction_localDensity_eq_of_minimalSink_source_vanishes
      (k := k) C₁ hP₁ hlocal₁ T Z hZ hremaining
        A.map A.rightAlmostSplit A.rightMinimal A.decomposition hsource
  change finiteDeletionExtendedLocalDensity (k := k) C₁ hlocal₁ T Z hZ =
    finiteModuleLocalDensity hlocal₁ Z hZ
  rw [finiteDeletionExtendedLocalDensity, dif_pos hremaining]
  exact hDensity

/-- For a separated stage window, push-down vanishes at the orbit of the next
deleted object exactly when the upstairs module vanishes at the distinguished
representative of that orbit. -/
theorem stageTwoStepModuleFamily_orbitSkeletonPushdown_obj_isZero_iff
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let y := stageNextObject (k := k) R x i
    let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
    IsZero
        ((orbitSkeletonPushdown (G := (N : Subgroup G))
          (W₂.obj t).obj.obj).obj
            (Quotient.mk'' y : MulAction.orbitRel.Quotient
              (N : Subgroup G)
              (StageCategory (k := k) (N : Subgroup G)
                R.representative x i.castSucc))) ↔
      IsZero ((W₂.obj t).obj.obj.obj y) := by
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
  let y := stageNextObject (k := k) R x i
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let M := W₂.obj t
  let q : DeckOrbitSkeleton
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      (N : Subgroup G) := Quotient.mk'' y
  let r := deckOrbitRepresentative
    (C := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc)
    (G := (N : Subgroup G))
    (show MulAction.orbitRel.Quotient (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) from q)
  obtain ⟨n, hn⟩ := deckOrbitRepresentative_mk_mem_orbit
    (G := (N : Subgroup G)) y
  change n • y = r at hn
  have hpush := Dstage.orbitSkeletonPushdown_obj_isZero_iff
    (k := k) M q
  change IsZero
      ((orbitSkeletonPushdown (G := (N : Subgroup G)) M.obj.obj).obj q) ↔
    IsZero (M.obj.obj.obj y)
  rw [hpush]
  constructor
  · intro hall
    rw [ModuleCat.isZero_iff_subsingleton,
      ← not_nontrivial_iff_subsingleton]
    intro hy
    let b : Additive (N : Subgroup G) := Additive.ofMul n
    have hb : Nontrivial
        (M.obj.obj.obj ((shiftFunctor
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc) b).obj r)) := by
      apply (Dstage.nontrivial_shift_value_iff (k := k) M b r).2
      change n⁻¹ • r ∈ moduleSupport k M.obj.obj
      rw [← hn, inv_smul_smul]
      exact hy
    have hbzero := hall b
    letI : Subsingleton
        (M.obj.obj.obj ((shiftFunctor
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc) b).obj r)) :=
      ModuleCat.isZero_iff_subsingleton.mp hbzero
    exact not_nontrivial _ hb
  · intro hy b
    rw [ModuleCat.isZero_iff_subsingleton,
      ← not_nontrivial_iff_subsingleton]
    intro hb
    have hsupport :=
      (Dstage.nontrivial_shift_value_iff (k := k) M b r).1 hb
    let n' : (N : Subgroup G) := b.toMul⁻¹ * n
    have hnSupport : n' • y ∈ moduleSupport k M.obj.obj := by
      change (b.toMul⁻¹ * n) • y ∈ moduleSupport k M.obj.obj
      rw [mul_smul, hn]
      exact hsupport
    have hn' : n' = 1 :=
      stageTwoStepModuleFamily_nontrivial_at_smul_imp_eq_one
        (k := k) (C := C) hP hlocal hrep N R x i havoid t n' hnSupport
    have hyNontrivial : Nontrivial (M.obj.obj.obj y) := by
      change Nontrivial (M.obj.obj.obj (n' • y)) at hnSupport
      simpa only [hn', one_smul] using hnSupport
    letI : Subsingleton (M.obj.obj.obj y) :=
      ModuleCat.isZero_iff_subsingleton.mp hy
    exact not_nontrivial _ hyNontrivial

variable [IsAlgClosed k]

/-- The finite family downstairs obtained by pushing the literal two-step
stage support family through the separated three-step control window. -/
noncomputable def stagePushedTwoStepModuleFamily
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
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
    FiniteIndecomposableModuleFamily
      (k := k)
      (C := DeckOrbitSkeleton
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (N : Subgroup G)) := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
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
  letI := isLinearModule_stableUnderShift (k := k) Dstage.core
  letI := linearModuleCategoryHasShift (k := k) Dstage.core
  letI := linearModuleCategoryAdditiveShift (R := k) Dstage.core
  letI := linearModuleCategoryLinearShift (R := k) Dstage.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (Additive (N : Subgroup G))) k)
    (Additive (N : Subgroup G))
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let W₃ := deletionSurvivingModuleFamily (k := k) C
    (finiteThreeStepControlFamily hrep (R.representative i • x)) S
  let P := Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow
    (k := k) W₃.additiveClosure
  let hW (t : Fin W₂.n) : W₃.additiveClosure (W₂.obj t) :=
    stageTwoStepModuleFamily_obj_mem_threeStepAdditiveClosure
      (k := k) hrep R x i t
  have horthogonal : Dstage.FiniteModuleWindowShiftHomOrthogonal
      (k := k) W₃.additiveClosure :=
    stage_survivingModuleFamily_shiftHomOrthogonal_of_ambient_avoids
      (k := k) C D hC (N : Subgroup G) R.representative x i.castSucc
        (finiteThreeStepControlFamily hrep (R.representative i • x)) havoid
  let hP (t : Fin W₂.n) : Indecomposable (P.obj ⟨W₂.obj t, hW t⟩) :=
    Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow_obj_indecomposable
      (k := k) W₃.additiveClosure horthogonal
        ⟨W₂.obj t, hW t⟩ (W₂.indecomposable t)
  exact W₂.mapWindowFunctor W₃.additiveClosure hW P hP

omit [IsAlgClosed k] in
/-- The literal pushed two-step family preserves vanishing at the object
deleted in this stage, after that object is replaced by its orbit class. -/
theorem stagePushedTwoStepModuleFamily_obj_isZero_iff
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let y := stageNextObject (k := k) R x i
    let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
    let P₂ := stagePushedTwoStepModuleFamily
      (k := k) (C := C) D hC hrep N R x i havoid
    IsZero ((P₂.obj t).obj.obj.obj
        (Quotient.mk'' y : MulAction.orbitRel.Quotient
          (N : Subgroup G)
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc))) ↔
      IsZero ((W₂.obj t).obj.obj.obj y) := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
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
  letI := isLinearModule_stableUnderShift (k := k) Dstage.core
  letI := linearModuleCategoryHasShift (k := k) Dstage.core
  letI := linearModuleCategoryAdditiveShift (R := k) Dstage.core
  letI := linearModuleCategoryLinearShift (R := k) Dstage.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (Additive (N : Subgroup G))) k)
    (Additive (N : Subgroup G))
  let y := stageNextObject (k := k) R x i
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let P₂ := stagePushedTwoStepModuleFamily
    (k := k) (C := C) D hC hrep N R x i havoid
  change IsZero
      ((orbitSkeletonPushdown (G := (N : Subgroup G))
        (W₂.obj t).obj.obj).obj
          (Quotient.mk'' y : MulAction.orbitRel.Quotient
            (N : Subgroup G)
            (StageCategory (k := k) (N : Subgroup G)
              R.representative x i.castSucc))) ↔
    IsZero ((W₂.obj t).obj.obj.obj y)
  exact stageTwoStepModuleFamily_orbitSkeletonPushdown_obj_isZero_iff
    (k := k) (C := C) D hC hP hlocal hrep N R x i havoid t

/-- At every represented two-step endpoint, the intrinsic density of the
pushed downstairs module is the intrinsic density of its upstairs stage
representative. -/
theorem stagePushedTwoStepModuleFamily_preLocalDensity
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
      g ∉ (N : Subgroup G))
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
    let P₂ := stagePushedTwoStepModuleFamily
      (k := k) (C := C) D hC hrep N R x i havoid
    let T := stageFiniteOrbitModuleIndecomposableSkeleton
      (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
    finiteModuleLocalDensity T.isLocallyRepresentationFinite
        (P₂.obj t) (P₂.indecomposable t) =
      finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion
          (k := k) C
          (stageDeletedSet (N : Subgroup G)
            R.representative x i.castSucc) hrep)
        (W₂.obj t) (W₂.indecomposable t) := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
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
  letI := isLinearModule_stableUnderShift (k := k) Dstage.core
  letI := linearModuleCategoryHasShift (k := k) Dstage.core
  letI := linearModuleCategoryAdditiveShift (R := k) Dstage.core
  letI := linearModuleCategoryLinearShift (R := k) Dstage.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (Additive (N : Subgroup G))) k)
    (Additive (N : Subgroup G))
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let W₃ := deletionSurvivingModuleFamily (k := k) C
    (finiteThreeStepControlFamily hrep (R.representative i • x)) S
  let hW (q : Fin W₂.n) : W₃.additiveClosure (W₂.obj q) :=
    stageTwoStepModuleFamily_obj_mem_threeStepAdditiveClosure
      (k := k) hrep R x i q
  let Y : CoveringSeparation.WindowCategory W₃.additiveClosure :=
    ⟨W₂.obj t, hW t⟩
  let P := Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow
    (k := k) W₃.additiveClosure
  let P₂ := stagePushedTwoStepModuleFamily
    (k := k) (C := C) D hC hrep N R x i havoid
  let T := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hPdown := Dstage.orbitSkeletonLinearCoyonedaFinite (k := k) hPstage
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)
          (N : Subgroup G)) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  have hPY : Indecomposable (P.obj Y) := by
    change Indecomposable (P₂.obj t)
    exact P₂.indecomposable t
  let y := Classical.choose (T.complete (P.obj Y) hPY)
  let eY : P.obj Y ≅ T.obj y :=
    Classical.choice (Classical.choose_spec (T.complete (P.obj Y) hPY))
  letI : DecidablePred T.toFiniteRightTauCategoryData.IsProjective :=
    Classical.decPred _
  have hYCore : Y.1 ∈ deletionTwoStepModuleCore
      (k := k) C hrep (R.representative i • x) S :=
    (mem_stageTwoStepModuleFamily_isoClosure_iff
      (k := k) hrep R x i (W₂.obj t)).1 (W₂.obj_mem_isoClosure t)
  have hpush := stage_finiteOrbitPushdown_intrinsicLocalDensity
    (k := k) C D hC hP hI hlocal hrep N R x i havoid
      Y (W₂.indecomposable t) hYCore
      T.toFiniteRightTauCategoryData y eY
  calc
    finiteModuleLocalDensity T.isLocallyRepresentationFinite
        (P₂.obj t) (P₂.indecomposable t) =
        finiteModuleLocalDensity T.isLocallyRepresentationFinite
          (T.obj y) (T.indecomposable y) := by
      apply finiteModuleLocalDensity_eq_of_iso
      exact eY
    _ = T.rightTauLocalDensity y :=
      T.finiteModuleLocalDensity_eq_rightTauLocalDensity
        T.isLocallyRepresentationFinite y
    _ = finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C S hrep)
        (W₂.obj t) (W₂.indecomposable t) := hpush

/-- Summing once per represented isomorphism class, the pre-deletion density
of the pushed two-step family is exactly the pre-deletion density of the
upstairs stage family. -/
theorem stagePushedTwoStepModuleFamily_preLocalDensitySum
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
    let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
    let P₂ := stagePushedTwoStepModuleFamily
      (k := k) (C := C) D hC hrep N R x i havoid
    let T := stageFiniteOrbitModuleIndecomposableSkeleton
      (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
    finiteModuleLocalDensitySum (k := k)
        (DeckOrbitSkeleton
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)
          (N : Subgroup G))
        T.isLocallyRepresentationFinite P₂ =
      finiteModuleLocalDensitySum (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (isLocallyRepresentationFinite_deletion
          (k := k) C
          (stageDeletedSet (N : Subgroup G)
            R.representative x i.castSucc) hrep)
        W₂ := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x i.castSucc
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
  letI := isLinearModule_stableUnderShift (k := k) Dstage.core
  letI := linearModuleCategoryHasShift (k := k) Dstage.core
  letI := linearModuleCategoryAdditiveShift (R := k) Dstage.core
  letI := linearModuleCategoryLinearShift (R := k) Dstage.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (Additive (N : Subgroup G))) k)
    (Additive (N : Subgroup G))
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let W₃ := deletionSurvivingModuleFamily (k := k) C
    (finiteThreeStepControlFamily hrep (R.representative i • x)) S
  let hW (q : Fin W₂.n) : W₃.additiveClosure (W₂.obj q) :=
    stageTwoStepModuleFamily_obj_mem_threeStepAdditiveClosure
      (k := k) hrep R x i q
  let P := Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow
    (k := k) W₃.additiveClosure
  have horthogonal : Dstage.FiniteModuleWindowShiftHomOrthogonal
      (k := k) W₃.additiveClosure :=
    stage_survivingModuleFamily_shiftHomOrthogonal_of_ambient_avoids
      (k := k) C D hC (N : Subgroup G) R.representative x i.castSucc
        (finiteThreeStepControlFamily hrep (R.representative i • x)) havoid
  let hFull : P.Full :=
    Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow_full
      (k := k) W₃.additiveClosure horthogonal
  let hFaithful : P.Faithful :=
    Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow_faithful
      (k := k) W₃.additiveClosure
  let hPushed (q : Fin W₂.n) :
      Indecomposable (P.obj ⟨W₂.obj q, hW q⟩) :=
    Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow_obj_indecomposable
      (k := k) W₃.additiveClosure horthogonal
        ⟨W₂.obj q, hW q⟩ (W₂.indecomposable q)
  let P₂ := W₂.mapWindowFunctor W₃.additiveClosure hW P hPushed
  let T := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
  change finiteModuleLocalDensitySum (k := k)
      (DeckOrbitSkeleton
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (N : Subgroup G))
      T.isLocallyRepresentationFinite P₂ =
    finiteModuleLocalDensitySum (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      (isLocallyRepresentationFinite_deletion (k := k) C S hrep) W₂
  unfold finiteModuleLocalDensitySum
  let e : W₂.IsoClass ≃ P₂.IsoClass :=
    W₂.isoClassWindowEquiv W₃.additiveClosure hW P hPushed
      hFull hFaithful
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | _ t =>
      exact stagePushedTwoStepModuleFamily_preLocalDensity
        (k := k) (C := C) D hC hP hI hlocal hrep N R x i havoid t

end MagnitudeConjecture.ObjectDeletion
