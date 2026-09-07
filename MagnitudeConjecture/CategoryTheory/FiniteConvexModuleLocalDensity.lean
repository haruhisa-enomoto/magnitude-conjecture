import MagnitudeConjecture.CategoryTheory.FiniteConvexModuleControlWindow
import MagnitudeConjecture.CategoryTheory.ObjectDeletionControlWindow
import MagnitudeConjecture.CategoryTheory.ObjectDeletionLocalDensity

/-!
# Local density inside a finite convex support window

The three-step module window contains both every endpoint which can contribute
to singleton-deletion change and every indecomposable summand of its minimal
sink source.  Once their object supports lie in a finite convex object window,
restriction to the complementary object deletion preserves the endpoint's
intrinsic local density.
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

/-- If every displayed indecomposable summand of a finite decomposition
vanishes on a deleted object set, then so does the decomposed module. -/
theorem moduleVanishesOnDeleted_of_decomposition_summands
    (S : Set C)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (hvanish : ∀ i, ModuleVanishesOnDeleted
      (k := k) C S (d.summand i).obj.obj) :
    ModuleVanishesOnDeleted (k := k) C S Y.obj.obj := by
  intro X hXS
  let E := finiteDimensionalModuleEvaluation (k := k) C X
  have hzeroSummand (i : Fin d.n) : IsZero (E.obj (d.summand i)) :=
    hvanish i X hXS
  have hzeroSum : IsZero (⨁ fun i : Fin d.n ↦ E.obj (d.summand i)) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro i
    exact (hzeroSummand i).eq_of_tgt _ _
  letI : E.Additive := by
    dsimp only [E, finiteDimensionalModuleEvaluation]
    infer_instance
  have hzeroBiproduct : IsZero (E.obj (⨁ d.summand)) :=
    hzeroSum.of_iso (E.mapBiproduct d.summand)
  exact hzeroBiproduct.of_iso (E.mapIso d.isoBiproduct)

/-- If the ambient extension of a deletion-stage module is supported in
`U`, then the stage module vanishes on the surviving representatives of the
complement of `U`. -/
theorem moduleVanishesOnAdditionalDeleted_of_extension_support_subset
    (S U : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k)
    (hM : moduleSupport k
      ((finiteDimensionalModuleExtensionByZero
        (k := k) C S).obj M).obj.obj ⊆ U) :
    ModuleVanishesOnDeleted
      (k := k) (DeletionCategory (k := k) C S)
      (AdditionalDeleted (k := k) C S Uᶜ) M.obj.obj := by
  intro X hX
  have hXU : X.obj.as ∉ U := hX
  have hzeroAmbient : IsZero
      (((finiteDimensionalModuleExtensionByZero
        (k := k) C S).obj M).obj.obj.obj X.obj.as) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact not_nontrivial_iff_subsingleton.mp fun hnontrivial ↦
      hXU (hM hnontrivial)
  exact (moduleExtensionByZeroObjIsoAt
    (k := k) C S M.obj.obj X).isZero_iff.mp hzeroAmbient

/-- Restriction from the ambient admissible category to a finite convex
three-step support window preserves intrinsic local density on the two-step
endpoint core. -/
theorem finiteConvex_restriction_localDensity_eq
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
        hlocal 2).isoClosure)
    (hMvanish : ModuleVanishesOnDeleted
      (k := k) C P.objectsᶜ M.obj.obj) :
    finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion
          (k := k) C P.objectsᶜ hlocal)
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) C P.objectsᶜ M hMvanish)
        (finiteDimensionalModuleRestrictionToDeletion_indec
          (k := k) C P.objectsᶜ M hM hMvanish) =
      finiteModuleLocalDensity hlocal M hM := by
  let W₀ := finiteFiberControlSeed hlocal x
  let A := finiteModuleMinimalSinkData hlocal M hM
  have hsourceSummand (i : Fin A.decomposition.n) :
      ModuleVanishesOnDeleted
        (k := k) C P.objectsᶜ (A.decomposition.summand i).obj.obj := by
    have hiThree : A.decomposition.summand i ∈
        (finiteThreeStepControlFamily hlocal x).isoClosure := by
      exact rightMinimal_middleSummand_mem_nextHomNeighborhood
        hlocal W₀ A.decomposition A.map A.rightMinimal hMtwo i
    exact moduleVanishesOnDeleted_compl_of_moduleSupport_subset
      (k := k) C P.objects (A.decomposition.summand i)
        (P.moduleSupport_subset_of_mem_isoClosure hiThree)
  have hsource : ModuleVanishesOnDeleted
      (k := k) C P.objectsᶜ A.source.obj.obj :=
    moduleVanishesOnDeleted_of_decomposition_summands
      (k := k) C P.objectsᶜ A.source A.decomposition hsourceSummand
  exact finiteDeletion_restriction_localDensity_eq_of_minimalSink_source_vanishes
    (k := k) C hP hlocal P.objectsᶜ M hM hMvanish A.map
      A.rightAlmostSplit A.rightMinimal A.decomposition hsource

/-- At any previous object-deletion stage, further restriction to the
surviving part of a finite convex three-step support window preserves local
density on the fixed ambient two-step endpoint core. -/
theorem finiteConvex_stage_restriction_localDensity_eq
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (x : C)
    (P : FiniteConvexModuleControlWindow (k := k) x
      (finiteThreeStepControlFamily hlocal x))
    (S : Set C)
    (Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k)
    (hZ : Indecomposable Z)
    (hZtwo :
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z ∈
        ((finiteFiberControlSeed hlocal x).iterateHomNeighborhood
          hlocal 2).isoClosure)
    (hZvanish : ModuleVanishesOnDeleted
      (k := k) (DeletionCategory (k := k) C S)
      (AdditionalDeleted (k := k) C S P.objectsᶜ) Z.obj.obj) :
    finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion
          (k := k) (DeletionCategory (k := k) C S)
          (AdditionalDeleted (k := k) C S P.objectsᶜ)
          (isLocallyRepresentationFinite_deletion (k := k) C S hlocal))
        (finiteDimensionalModuleRestrictionToDeletion
          (k := k) (DeletionCategory (k := k) C S)
            (AdditionalDeleted (k := k) C S P.objectsᶜ) Z hZvanish)
        (finiteDimensionalModuleRestrictionToDeletion_indec
          (k := k) (DeletionCategory (k := k) C S)
            (AdditionalDeleted (k := k) C S P.objectsᶜ)
              Z hZ hZvanish) =
      finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C S hlocal) Z hZ := by
  let D := DeletionCategory (k := k) C S
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  let W₀ := finiteFiberControlSeed hlocal x
  let hlocalD := isLocallyRepresentationFinite_deletion (k := k) C S hlocal
  let A := finiteModuleMinimalSinkData hlocalD Z hZ
  have hsourceSummand (i : Fin A.decomposition.n) :
      ModuleVanishesOnDeleted
        (k := k) D (AdditionalDeleted (k := k) C S P.objectsᶜ)
          (A.decomposition.summand i).obj.obj := by
    have hcomponent : A.decomposition.inclusion i ≫ A.map ≠ 0 :=
      A.decomposition.inclusion_comp_ne_zero_of_isRightMinimal
        i A.map A.rightMinimal
    have hFcomponent : F.map
        (A.decomposition.inclusion i ≫ A.map) ≠ 0 := by
      intro hzero
      exact hcomponent ((F.map_eq_zero_iff).mp hzero)
    have hFind : Indecomposable (F.obj (A.decomposition.summand i)) :=
      finiteDimensionalModuleExtensionByZero_indec
        (k := k) C S (A.decomposition.summand i)
          (A.decomposition.indecomposable i)
    have hiThree : F.obj (A.decomposition.summand i) ∈
        (finiteThreeStepControlFamily hlocal x).isoClosure :=
      W₀.mem_iterateHomNeighborhood_succ_of_ne_zero_from
        hlocal hZtwo hFind (F.map
          (A.decomposition.inclusion i ≫ A.map)) hFcomponent
    exact moduleVanishesOnAdditionalDeleted_of_extension_support_subset
      (k := k) C S P.objects (A.decomposition.summand i)
        (P.moduleSupport_subset_of_mem_isoClosure hiThree)
  have hsource : ModuleVanishesOnDeleted
      (k := k) D (AdditionalDeleted (k := k) C S P.objectsᶜ)
        A.source.obj.obj :=
    moduleVanishesOnDeleted_of_decomposition_summands
      (k := k) D (AdditionalDeleted (k := k) C S P.objectsᶜ)
        A.source A.decomposition hsourceSummand
  let hPstage := fun Y ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S Y
  exact finiteDeletion_restriction_localDensity_eq_of_minimalSink_source_vanishes
    (k := k) D hPstage hlocalD
      (AdditionalDeleted (k := k) C S P.objectsᶜ) Z hZ hZvanish A.map
        A.rightAlmostSplit A.rightMinimal A.decomposition hsource

end MagnitudeConjecture.ObjectDeletion
