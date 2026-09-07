import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleAdjoints
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleAlmostSplitMinimal
import MagnitudeConjecture.CategoryTheory.AlmostSplitLocalFunctor
import MagnitudeConjecture.CategoryTheory.AlmostSplitMultiplicity
import MagnitudeConjecture.CategoryTheory.AlmostSplitCokernel
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStructure
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectivePresentation

/-!
# Almost-split maps under object deletion

The finite modules vanishing on a set of deleted objects form a reflective
and coreflective full subcategory of the ambient finite-module category.
This file proves the manuscript's intrinsic source/sink comparison: applying
the right adjoint to the source of an ambient sink map produces a right
almost-split map in the vanishing subcategory, and applying the left adjoint
to the target of an ambient source map produces a left almost-split map there.
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
variable (S : Set C)

/-- Restrict an ambient map into a vanishing module to the maximal vanishing
submodule of its source. -/
def finiteMaximalVanishingSubmoduleRestriction
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : VanishingFiniteModuleCategory (k := k) C S}
    (g : Y ⟶ Z.obj) :
    (finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y ⟶ Z :=
  ObjectProperty.homMk
    (finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y ≫ g)

@[simp]
theorem finiteMaximalVanishingSubmoduleRestriction_hom
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : VanishingFiniteModuleCategory (k := k) C S}
    (g : Y ⟶ Z.obj) :
    (finiteMaximalVanishingSubmoduleRestriction (k := k) C S g).hom =
      finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y ≫ g := rfl

/-- Restricting an ambient right almost-split map by the right adjoint gives
a right almost-split map in the vanishing subcategory. -/
theorem finiteMaximalVanishingSubmoduleRestriction_isRightAlmostSplit
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : VanishingFiniteModuleCategory (k := k) C S}
    (g : Y ⟶ Z.obj) (hg : IsRightAlmostSplit g) :
    IsRightAlmostSplit
      (finiteMaximalVanishingSubmoduleRestriction (k := k) C S g) := by
  let I := (finiteModuleVanishesOnDeleted (k := k) C S).ι
  constructor
  · intro hs
    apply hg.not_isSplitEpi
    letI : IsSplitEpi
        (finiteMaximalVanishingSubmoduleRestriction (k := k) C S g) := hs
    have hsAmbient : IsSplitEpi
        (finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y ≫ g) := by
      change IsSplitEpi
        (I.map (finiteMaximalVanishingSubmoduleRestriction (k := k) C S g))
      infer_instance
    obtain ⟨s⟩ := hsAmbient.exists_splitEpi
    exact IsSplitEpi.mk'
      { section_ := s.section_ ≫
          finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y
        id := by simpa only [Category.assoc] using s.id }
  · intro W h hh
    have hhAmbient : ¬ IsSplitEpi h.hom := by
      intro hs
      apply hh
      apply (I.isSplitEpi_iff h).mp
      change IsSplitEpi h.hom
      exact hs
    obtain ⟨a, ha⟩ := hg.factors h.hom hhAmbient
    refine ⟨finiteMaximalVanishingSubmoduleLift (k := k) C S a, ?_⟩
    apply ObjectProperty.hom_ext
    calc
      (finiteMaximalVanishingSubmoduleLift (k := k) C S a).hom ≫
          (finiteMaximalVanishingSubmoduleRestriction (k := k) C S g).hom =
        ((finiteMaximalVanishingSubmoduleLift (k := k) C S a).hom ≫
          finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y) ≫ g := by
            exact (Category.assoc _ _ _).symm
      _ = a ≫ g := by
        rw [finiteMaximalVanishingSubmoduleLift_comp_inclusion]
      _ = h.hom := ha

/-- Compose an ambient map out of a vanishing module with the projection to
the maximal vanishing quotient of its target. -/
def finiteMaximalVanishingQuotientExtension
    {Z : VanishingFiniteModuleCategory (k := k) C S}
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : Z.obj ⟶ Y) :
    Z ⟶ (finiteMaximalVanishingQuotientFunctor (k := k) C S).obj Y :=
  ObjectProperty.homMk
    (f ≫ finiteMaximalVanishingQuotientProjection (k := k) C S Y)

@[simp]
theorem finiteMaximalVanishingQuotientExtension_hom
    {Z : VanishingFiniteModuleCategory (k := k) C S}
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : Z.obj ⟶ Y) :
    (finiteMaximalVanishingQuotientExtension (k := k) C S f).hom =
      f ≫ finiteMaximalVanishingQuotientProjection (k := k) C S Y := rfl

/-- Extending an ambient left almost-split map by the left adjoint gives a
left almost-split map in the vanishing subcategory. -/
theorem finiteMaximalVanishingQuotientExtension_isLeftAlmostSplit
    {Z : VanishingFiniteModuleCategory (k := k) C S}
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : Z.obj ⟶ Y) (hf : IsLeftAlmostSplit f) :
    IsLeftAlmostSplit
      (finiteMaximalVanishingQuotientExtension (k := k) C S f) := by
  let I := (finiteModuleVanishesOnDeleted (k := k) C S).ι
  constructor
  · intro hs
    apply hf.not_isSplitMono
    letI : IsSplitMono
        (finiteMaximalVanishingQuotientExtension (k := k) C S f) := hs
    have hsAmbient : IsSplitMono
        (f ≫ finiteMaximalVanishingQuotientProjection (k := k) C S Y) := by
      change IsSplitMono
        (I.map (finiteMaximalVanishingQuotientExtension (k := k) C S f))
      infer_instance
    obtain ⟨s⟩ := hsAmbient.exists_splitMono
    exact IsSplitMono.mk'
      { retraction := finiteMaximalVanishingQuotientProjection
          (k := k) C S Y ≫ s.retraction
        id := by simpa only [Category.assoc] using s.id }
  · intro W h hh
    have hhAmbient : ¬ IsSplitMono h.hom := by
      intro hs
      apply hh
      apply (I.isSplitMono_iff h).mp
      change IsSplitMono h.hom
      exact hs
    obtain ⟨a, ha⟩ := hf.factors h.hom hhAmbient
    refine ⟨finiteMaximalVanishingQuotientDescend (k := k) C S a, ?_⟩
    apply ObjectProperty.hom_ext
    calc
      (finiteMaximalVanishingQuotientExtension (k := k) C S f).hom ≫
          (finiteMaximalVanishingQuotientDescend (k := k) C S a).hom =
        f ≫ (finiteMaximalVanishingQuotientProjection (k := k) C S Y ≫
          (finiteMaximalVanishingQuotientDescend (k := k) C S a).hom) := by
            exact Category.assoc _ _ _
      _ = f ≫ a := by
        rw [projection_comp_finiteMaximalVanishingQuotientDescend]
      _ = h.hom := ha

/-- Extension by zero, corestricted to the full subcategory of finite ambient
modules vanishing on the deleted objects. -/
def finiteDimensionalModuleExtensionByZeroToVanishing :
    FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C S) k ⥤
      VanishingFiniteModuleCategory (k := k) C S :=
    (finiteModuleVanishesOnDeleted (k := k) C S).lift
    (finiteDimensionalModuleExtensionByZero (k := k) C S)
    (fun M _ hX ↦
      moduleExtensionByZero_obj_isZero_of_mem
        (k := k) C S M.obj.obj hX)

noncomputable instance finiteDimensionalModuleExtensionByZeroToVanishing_faithful :
    (finiteDimensionalModuleExtensionByZeroToVanishing
      (k := k) C S).Faithful where
  map_injective {M N} f g h := by
    apply (finiteDimensionalModuleExtensionByZero
      (k := k) C S).map_injective
    exact congrArg (fun q ↦ q.hom) h

noncomputable instance finiteDimensionalModuleExtensionByZeroToVanishing_full :
    (finiteDimensionalModuleExtensionByZeroToVanishing
      (k := k) C S).Full where
  map_surjective {M N} f := by
    let F := finiteDimensionalModuleExtensionByZero (k := k) C S
    refine ⟨F.preimage f.hom, ?_⟩
    apply ObjectProperty.hom_ext
    exact F.map_preimage f.hom

noncomputable instance finiteDimensionalModuleExtensionByZeroToVanishing_isEquivalence :
    (finiteDimensionalModuleExtensionByZeroToVanishing
      (k := k) C S).IsEquivalence where
  essSurj :=
    { mem_essImage := fun M ↦
        ⟨finiteDimensionalModuleRestrictionToDeletion
            (k := k) C S M.obj M.property,
          ⟨ObjectProperty.isoMk _
            (finiteDimensionalModuleRestrictionExtensionIso
              (k := k) C S M.obj M.property)⟩⟩ }

/-- The deletion-stage finite-module category is equivalent to the full
vanishing subcategory of ambient finite modules. -/
def finiteDimensionalModuleExtensionByZeroVanishingEquivalence :
    FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C S) k ≌
      VanishingFiniteModuleCategory (k := k) C S :=
  (finiteDimensionalModuleExtensionByZeroToVanishing (k := k) C S).asEquivalence

/-- The explicit deletion-stage module underlying a finite ambient module
which vanishes on the deleted objects. -/
def finiteVanishingModuleRestriction
    (M : VanishingFiniteModuleCategory (k := k) C S) :
    FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k :=
  finiteDimensionalModuleRestrictionToDeletion
    (k := k) C S M.obj M.property

/-- Extending the explicit restriction of a vanishing finite module recovers
that module inside the vanishing full subcategory. -/
def finiteVanishingModuleRestrictionExtensionIso
    (M : VanishingFiniteModuleCategory (k := k) C S) :
    (finiteDimensionalModuleExtensionByZeroToVanishing
      (k := k) C S).obj
        (finiteVanishingModuleRestriction (k := k) C S M) ≅ M :=
  ObjectProperty.isoMk _
    (finiteDimensionalModuleRestrictionExtensionIso
      (k := k) C S M.obj M.property)

/-- The intrinsic deletion-stage sink candidate obtained from an ambient
right almost-split map by the maximal-vanishing-submodule construction. -/
def finiteDeletionRightAdjointSinkCandidate
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z) :
    finiteVanishingModuleRestriction (k := k) C S
        ((finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y) ⟶ Z :=
  let F := finiteDimensionalModuleExtensionByZeroToVanishing (k := k) C S
  let R := (finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y
  F.preimage
    ((finiteVanishingModuleRestrictionExtensionIso (k := k) C S R).hom ≫
      finiteMaximalVanishingSubmoduleRestriction
        (k := k) C S (Z := F.obj Z) g)

/-- After extension by zero, the intrinsic deletion-stage sink candidate is
the ambient map restricted along the canonical source isomorphism and the
maximal-vanishing-submodule inclusion. -/
theorem finiteDimensionalModuleExtensionByZero_map_finiteDeletionRightAdjointSinkCandidate
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z) :
    (finiteDimensionalModuleExtensionByZero (k := k) C S).map
        (finiteDeletionRightAdjointSinkCandidate (k := k) C S g) =
      (finiteVanishingModuleRestrictionExtensionIso (k := k) C S
          ((finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y)).hom.hom ≫
        finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y ≫ g := by
  let F := finiteDimensionalModuleExtensionByZeroToVanishing (k := k) C S
  let R := (finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y
  let e := finiteVanishingModuleRestrictionExtensionIso (k := k) C S R
  change (F.map (F.preimage
    (e.hom ≫ finiteMaximalVanishingSubmoduleRestriction
      (k := k) C S (Z := F.obj Z) g))).hom = _
  rw [F.map_preimage]
  rfl

/-- If an ambient finite module already vanishes on the deleted objects,
restricting its maximal vanishing submodule preserves the number of terms in
every finite indecomposable decomposition. -/
theorem finiteMaximalVanishingSubmoduleRestriction_arity_eq_of_vanishesOnDeleted
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hY : ModuleVanishesOnDeleted (k := k) C S Y.obj.obj)
    (dY : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition Y)
    (dR : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (finiteVanishingModuleRestriction (k := k) C S
        ((finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y))) :
    dR.n = dY.n := by
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  let I := (finiteModuleVanishesOnDeleted (k := k) C S).ι
  let R := (finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y
  let e := finiteVanishingModuleRestrictionExtensionIso (k := k) C S R
  have hIndec (i : Fin dR.n) : Indecomposable (F.obj (dR.summand i)) :=
    finiteDimensionalModuleExtensionByZero_indec
      (k := k) C S (dR.summand i) (dR.indecomposable i)
  let dMap := dR.mapOfIndecomposable F hIndec
  have hlocal (i : Fin dMap.n) : IsLocalRing (End (dMap.summand i)) :=
    finiteDimensionalModule_end_isLocalRing k _ (hIndec i)
  letI : IsIso (finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y) :=
    finiteMaximalVanishingSubmoduleInclusion_isIso_of_vanishesOnDeleted
      (k := k) C S Y hY
  let sourceIso :=
    I.mapIso e ≪≫
      asIso (finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y)
  exact dMap.n_eq_of_iso dY hlocal sourceIso

/-- If the ambient source vanishes on the deleted objects, the intrinsic
deletion-stage sink candidate is monic exactly when the ambient sink is. -/
theorem finiteDeletionRightAdjointSinkCandidate_mono_iff_of_source_vanishes
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z)
    (hY : ModuleVanishesOnDeleted (k := k) C S Y.obj.obj) :
    Mono (finiteDeletionRightAdjointSinkCandidate (k := k) C S g) ↔ Mono g := by
  let F := finiteDimensionalModuleExtensionByZero (k := k) C S
  let V := finiteModuleVanishesOnDeleted (k := k) C S
  let I := V.ι
  let Fv := finiteDimensionalModuleExtensionByZeroToVanishing (k := k) C S
  let R := (finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y
  let e := finiteVanishingModuleRestrictionExtensionIso (k := k) C S R
  let i := finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y
  let q := finiteDeletionRightAdjointSinkCandidate (k := k) C S g
  have hmap : F.map q = e.hom.hom ≫ i ≫ g :=
    finiteDimensionalModuleExtensionByZero_map_finiteDeletionRightAdjointSinkCandidate
      (k := k) C S g
  letI : IsIso i :=
    finiteMaximalVanishingSubmoduleInclusion_isIso_of_vanishesOnDeleted
      (k := k) C S Y hY
  haveI : IsIso e.hom.hom := by
    change IsIso (I.map e.hom)
    infer_instance
  letI : I.PreservesMonomorphisms :=
    V.preservesMonomorphisms_ι_of_isNormalEpiCategory
  constructor
  · intro hq
    letI : Mono q := hq
    haveI hFvq : Mono ((Fv ⋙ I).map q) := (Fv ⋙ I).map_mono q
    haveI hFq : Mono (F.map q) := by
      change Mono ((Fv ⋙ I).map q)
      infer_instance
    have hcomp : Mono (e.hom.hom ≫ i ≫ g) := hmap ▸ hFq
    have hicomp : Mono (i ≫ g) :=
      (mono_comp_iff_of_isIso e.hom.hom (i ≫ g)).mp hcomp
    exact (mono_comp_iff_of_isIso i g).mp hicomp
  · intro hg
    letI : Mono g := hg
    have hcomp : Mono (e.hom.hom ≫ i ≫ g) :=
      mono_comp' (IsIso.mono_of_iso e.hom.hom)
        (mono_comp' (IsIso.mono_of_iso i) hg)
    have hFq : Mono (F.map q) := hmap.symm ▸ hcomp
    exact F.mono_of_mono_map hFq

/-- The right-adjoint sink candidate is right almost split in the literal
deletion-stage module category. -/
theorem finiteDeletionRightAdjointSinkCandidate_isRightAlmostSplit
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z)
    (hg : IsRightAlmostSplit g) :
    IsRightAlmostSplit
      (finiteDeletionRightAdjointSinkCandidate (k := k) C S g) := by
  let F := finiteDimensionalModuleExtensionByZeroToVanishing (k := k) C S
  let R := (finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y
  let e := finiteVanishingModuleRestrictionExtensionIso (k := k) C S R
  have hR : IsRightAlmostSplit
      (finiteMaximalVanishingSubmoduleRestriction
        (k := k) C S (Z := F.obj Z) g) :=
    finiteMaximalVanishingSubmoduleRestriction_isRightAlmostSplit
    (k := k) C S
      (Z := F.obj Z) g hg
  apply IsRightAlmostSplit.of_map_fully_faithful F
  change IsRightAlmostSplit
    (F.map (F.preimage (e.hom ≫
      finiteMaximalVanishingSubmoduleRestriction
        (k := k) C S (Z := F.obj Z) g)))
  rw [F.map_preimage]
  exact MagnitudeConjecture.CategoryTheory.rightAlmostSplit_precomp_iso e hR

/-- If the source of an ambient right-minimal sink already vanishes on the
deleted objects, its intrinsic deletion-stage sink candidate remains right
minimal. -/
theorem finiteDeletionRightAdjointSinkCandidate_isRightMinimal_of_source_vanishes
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z)
    (hg : IsRightMinimal g)
    (hY : ModuleVanishesOnDeleted (k := k) C S Y.obj.obj) :
    IsRightMinimal
      (finiteDeletionRightAdjointSinkCandidate (k := k) C S g) := by
  let I := (finiteModuleVanishesOnDeleted (k := k) C S).ι
  let F := finiteDimensionalModuleExtensionByZeroToVanishing (k := k) C S
  let R := (finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y
  let e := finiteVanishingModuleRestrictionExtensionIso (k := k) C S R
  let q := finiteMaximalVanishingSubmoduleRestriction
    (k := k) C S (Z := F.obj Z) g
  letI : IsIso (finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y) :=
    finiteMaximalVanishingSubmoduleInclusion_isIso_of_vanishesOnDeleted
      (k := k) C S Y hY
  have hIq : IsRightMinimal (I.map q) := by
    change IsRightMinimal
      (finiteMaximalVanishingSubmoduleInclusion (k := k) C S Y ≫ g)
    exact hg.precomp_splitMono _
  have hq : IsRightMinimal q :=
    MagnitudeConjecture.rightMinimal_of_map_full_faithful I hIq
  apply MagnitudeConjecture.rightMinimal_of_map_full_faithful F
  change IsRightMinimal (F.map (F.preimage (e.hom ≫ q)))
  rw [F.map_preimage]
  exact hq.precomp_splitMono _

/-- If the source of an ambient minimal sink already vanishes on the deleted
objects, deleting those objects preserves projectivity of the endpoint. -/
theorem finiteDeletion_projective_iff_of_minimal_sink_source_vanishes
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z)
    (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g)
    (hY : ModuleVanishesOnDeleted (k := k) C S Y.obj.obj) :
    Projective Z ↔
      Projective ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z) := by
  let q := finiteDeletionRightAdjointSinkCandidate (k := k) C S g
  have hq : IsRightAlmostSplit q :=
    finiteDeletionRightAdjointSinkCandidate_isRightAlmostSplit
      (k := k) C S g hg
  have hqmin : IsRightMinimal q :=
    finiteDeletionRightAdjointSinkCandidate_isRightMinimal_of_source_vanishes
      (k := k) C S g hgmin hY
  have hmono : Mono q ↔ Mono g :=
    finiteDeletionRightAdjointSinkCandidate_mono_iff_of_source_vanishes
      (k := k) C S g hY
  let hPdown := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    enoughProjectives_of_finiteRepresentables hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C S) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  constructor
  · intro hZ
    letI : Projective Z := hZ
    have hqmono : Mono q :=
      MagnitudeConjecture.CategoryTheory.rightAlmostSplit_mono_of_projective_target
        q hq hqmin
    letI : Mono g := hmono.mp hqmono
    exact MagnitudeConjecture.CategoryTheory.projective_of_mono_rightAlmostSplit
      g hg
  · intro hZ
    letI : Projective
        ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z) := hZ
    have hgmono : Mono g :=
      MagnitudeConjecture.CategoryTheory.rightAlmostSplit_mono_of_projective_target
        g hg hgmin
    letI : Mono q := hmono.mpr hgmono
    exact MagnitudeConjecture.CategoryTheory.projective_of_mono_rightAlmostSplit
      q hq

/-- The deletion-stage sink map is obtained by right-minimalizing the
right-adjoint image of an ambient sink map. -/
theorem exists_finiteDeletion_rightMinimal_sink_of_ambient
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z)
    (hg : IsRightAlmostSplit g) :
    ∃ (Y' : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C S) k)
      (g' : Y' ⟶ Z), IsRightAlmostSplit g' ∧ IsRightMinimal g' :=
  finiteDimensionalModule_exists_rightMinimal_rightAlmostSplit
    (finiteDeletionRightAdjointSinkCandidate (k := k) C S g)
    (finiteDeletionRightAdjointSinkCandidate_isRightAlmostSplit
      (k := k) C S g hg)

/-- A right-minimal deletion-stage sink has middle term a retract of the
right-adjoint sink candidate. -/
theorem exists_finiteDeletion_rightMinimal_sink_retract_of_ambient
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    (g : Y ⟶
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z)
    (hg : IsRightAlmostSplit g) :
    ∃ (Y' : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C S) k)
      (g' : Y' ⟶ Z)
      (i : Y' ⟶
        finiteVanishingModuleRestriction (k := k) C S
          ((finiteMaximalVanishingSubmoduleFunctor (k := k) C S).obj Y)),
      IsRightAlmostSplit g' ∧ IsRightMinimal g' ∧
        IsSplitMono i ∧
        i ≫ finiteDeletionRightAdjointSinkCandidate (k := k) C S g = g' := by
  let q := finiteDeletionRightAdjointSinkCandidate (k := k) C S g
  have hq : IsRightAlmostSplit q :=
    finiteDeletionRightAdjointSinkCandidate_isRightAlmostSplit
      (k := k) C S g hg
  obtain ⟨Y', g', hg', hg'min⟩ :=
    exists_finiteDeletion_rightMinimal_sink_of_ambient
      (k := k) C S g hg
  obtain ⟨a, ha⟩ := hg'.factors q hq.not_isSplitEpi
  obtain ⟨b, hb⟩ := hq.factors g' hg'.not_isSplitEpi
  have hba : (b ≫ a) ≫ g' = g' := by
    simp only [Category.assoc, ha, hb]
  letI : IsIso (b ≫ a) := hg'min (b ≫ a) hba
  have hbmono : IsSplitMono b := IsSplitMono.mk'
    { retraction := a ≫ inv (b ≫ a)
      id := by simp only [← Category.assoc, IsIso.hom_inv_id] }
  exact ⟨Y', g', b, hg', hg'min, hbmono, hb⟩

/-- The intrinsic deletion-stage source candidate obtained from an ambient
left almost-split map by the maximal-vanishing-quotient construction. -/
def finiteDeletionLeftAdjointSourceCandidate
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z ⟶ Y) :
    Z ⟶
      finiteVanishingModuleRestriction (k := k) C S
        ((finiteMaximalVanishingQuotientFunctor (k := k) C S).obj Y) :=
  let F := finiteDimensionalModuleExtensionByZeroToVanishing (k := k) C S
  let L := (finiteMaximalVanishingQuotientFunctor (k := k) C S).obj Y
  F.preimage
    (finiteMaximalVanishingQuotientExtension
        (k := k) C S (Z := F.obj Z) f ≫
      (finiteVanishingModuleRestrictionExtensionIso (k := k) C S L).inv)

/-- The left-adjoint source candidate is left almost split in the literal
deletion-stage module category. -/
theorem finiteDeletionLeftAdjointSourceCandidate_isLeftAlmostSplit
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z ⟶ Y)
    (hf : IsLeftAlmostSplit f) :
    IsLeftAlmostSplit
      (finiteDeletionLeftAdjointSourceCandidate (k := k) C S f) := by
  let F := finiteDimensionalModuleExtensionByZeroToVanishing (k := k) C S
  let L := (finiteMaximalVanishingQuotientFunctor (k := k) C S).obj Y
  let e := finiteVanishingModuleRestrictionExtensionIso (k := k) C S L
  have hL : IsLeftAlmostSplit
      (finiteMaximalVanishingQuotientExtension
        (k := k) C S (Z := F.obj Z) f) :=
    finiteMaximalVanishingQuotientExtension_isLeftAlmostSplit
    (k := k) C S
      (Z := F.obj Z) f hf
  apply IsLeftAlmostSplit.of_map_fully_faithful F
  change IsLeftAlmostSplit
    (F.map (F.preimage
      (finiteMaximalVanishingQuotientExtension
          (k := k) C S (Z := F.obj Z) f ≫ e.inv)))
  rw [F.map_preimage]
  exact hL.postcomp_iso e.symm

/-- The deletion-stage source map is obtained by left-minimalizing the
left-adjoint image of an ambient source map. -/
theorem exists_finiteDeletion_leftMinimal_source_of_ambient
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z ⟶ Y)
    (hf : IsLeftAlmostSplit f) :
    ∃ (Y' : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C S) k)
      (f' : Z ⟶ Y'), IsLeftAlmostSplit f' ∧ IsLeftMinimal f' :=
  finiteDimensionalModule_exists_leftMinimal_leftAlmostSplit
    (finiteDeletionLeftAdjointSourceCandidate (k := k) C S f)
    (finiteDeletionLeftAdjointSourceCandidate_isLeftAlmostSplit
      (k := k) C S f hf)

/-- A left-minimal deletion-stage source has middle term a retract of the
left-adjoint source candidate. -/
theorem exists_finiteDeletion_leftMinimal_source_retract_of_ambient
    {Z : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k}
    {Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (f : (finiteDimensionalModuleExtensionByZero (k := k) C S).obj Z ⟶ Y)
    (hf : IsLeftAlmostSplit f) :
    ∃ (Y' : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeletionCategory (k := k) C S) k)
      (f' : Z ⟶ Y')
      (i : Y' ⟶
        finiteVanishingModuleRestriction (k := k) C S
          ((finiteMaximalVanishingQuotientFunctor (k := k) C S).obj Y)),
      IsLeftAlmostSplit f' ∧ IsLeftMinimal f' ∧
        IsSplitMono i ∧
        f' ≫ i = finiteDeletionLeftAdjointSourceCandidate (k := k) C S f := by
  let q := finiteDeletionLeftAdjointSourceCandidate (k := k) C S f
  have hq : IsLeftAlmostSplit q :=
    finiteDeletionLeftAdjointSourceCandidate_isLeftAlmostSplit
      (k := k) C S f hf
  obtain ⟨Y', f', hf', hf'min⟩ :=
    exists_finiteDeletion_leftMinimal_source_of_ambient
      (k := k) C S f hf
  obtain ⟨a, ha⟩ := hf'.factors q hq.not_isSplitMono
  obtain ⟨b, hb⟩ := hq.factors f' hf'.not_isSplitMono
  have hab : f' ≫ (a ≫ b) = f' := by
    simp only [← Category.assoc, ha, hb]
  letI : IsIso (a ≫ b) := hf'min (a ≫ b) hab
  have hamono : IsSplitMono a := IsSplitMono.mk'
    { retraction := b ≫ inv (a ≫ b)
      id := by simp only [← Category.assoc, IsIso.hom_inv_id] }
  exact ⟨Y', f', a, hf', hf'min, hamono, ha⟩

end MagnitudeConjecture.ObjectDeletion
