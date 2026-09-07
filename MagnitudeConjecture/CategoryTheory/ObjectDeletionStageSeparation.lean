import MagnitudeConjecture.CategoryTheory.ObjectDeletionUniformSeparation
import MagnitudeConjecture.CategoryTheory.ObjectDeletionDeckShift
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStage

/-!
# Residual separation inside object-deletion stages

The residual subgroup is selected from support-overlap degrees of one ambient
finite module family.  A nonzero shifted map in an invariant deletion stage
already produces an overlap of the corresponding extended ambient supports.
Consequently the same avoidance certificate makes every deletion-stage
subfamily whose extensions lie in the ambient window shift-Hom orthogonal.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C]

/-- The intrinsic deletion-stage representatives obtained by descending the
members of an ambient finite family that survive the deleted set. -/
def deletionSurvivingModuleFamily
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (S : Set C) :
    FiniteIndecomposableModuleFamily
      (k := k) (C := DeletionCategory (k := k) C S) := by
  let T := deletionSurvivingSubfamily (k := k) C W S
  refine
    { n := T.n
      obj := fun i ↦ finiteDimensionalModuleRestrictionToDeletion
        (k := k) C S (T.obj i)
          (deletionSurvivingSubfamily_obj_vanishes (k := k) C W S i)
      indecomposable := ?_ }
  intro i
  let M := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C S (T.obj i)
      (deletionSurvivingSubfamily_obj_vanishes (k := k) C W S i)
  let e := finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C S (T.obj i)
      (deletionSurvivingSubfamily_obj_vanishes (k := k) C W S i)
  have hFM : Indecomposable
      ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj M) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).2
      (T.indecomposable i)
  exact (finiteDimensionalModuleExtensionByZero_indec_iff
    (k := k) C S M).1 hFM

/-- Every descended surviving representative extends to an object in the
original ambient family's isomorphism closure. -/
theorem deletionSurvivingModuleFamily_extension_mem_isoClosure
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (S : Set C)
    (i : Fin (deletionSurvivingModuleFamily (k := k) C W S).n) :
    (finiteDimensionalModuleExtensionByZero (k := k) C S).obj
        ((deletionSurvivingModuleFamily (k := k) C W S).obj i) ∈
      W.isoClosure := by
  let I := deletionSurvivingIndices (k := k) C W S
  let eI : Fin I.card ≃ I := I.equivFin.symm
  refine ⟨(eI i).1, ?_⟩
  exact ⟨finiteDimensionalModuleRestrictionExtensionIso
    (k := k) C S (W.obj (eI i).1)
      ((mem_deletionSurvivingIndices_iff (k := k) C W S (eI i).1).1
        (eI i).2) |>.symm⟩

/-- Avoidance of the ambient family's bad support degrees transfers to
shift-Hom orthogonality on every finite family of deletion-stage modules whose
extensions belong to the ambient isomorphism closure.  The proof uses support
overlap directly and therefore needs no separate compatibility structure on
extension by zero. -/
theorem deletion_finiteModuleWindowShiftHomOrthogonal_of_ambient_avoids
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (N : Subgroup G) (S : Set C)
    [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := N) S)
    (U : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (V : FiniteIndecomposableModuleFamily
      (k := k) (C := DeletionCategory (k := k) C S))
    (hV : ∀ i,
      (finiteDimensionalModuleExtensionByZero (k := k) C S).obj (V.obj i) ∈
        U.isoClosure)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G) U,
      g ∉ N) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    let hShift :=
      CoherentDeckShift.shiftInvariant_of_actionInvariant (D.restrict N) S hS
    letI := rawHasShift (k := k) S hShift
    letI := deletionHasShift (k := k) S hShift
    letI := deletionMulAction (k := k) S hS
    let Dstage := CoherentDeckShift.deletionCoherentDeckShift
      (k := k) (D.restrict N) S hS
    Dstage.FiniteModuleWindowShiftHomOrthogonal
      (k := k) (Set.range V.obj) := by
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  let hShift :=
    CoherentDeckShift.shiftInvariant_of_actionInvariant (D.restrict N) S hS
  letI := rawHasShift (k := k) S hShift
  letI := deletionHasShift (k := k) S hShift
  letI := deletionMulAction (k := k) S hS
  let Dstage := CoherentDeckShift.deletionCoherentDeckShift
    (k := k) (D.restrict N) S hS
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) Dstage.core
  letI := linearModuleCategoryHasShift (k := k) Dstage.core
  dsimp only [CoherentDeckShift.FiniteModuleWindowShiftHomOrthogonal]
  intro M M' a ha
  obtain ⟨i, hi⟩ := M.2
  obtain ⟨j, hj⟩ := M'.2
  constructor
  intro q r
  have eq_zero (t : ShiftHom M.1.obj M'.1.obj a) : t = 0 := by
    by_contra ht
    have hgne : (a.toMul : G) ≠ 1 := by
      intro hg
      apply ha
      apply Additive.toMul.injective
      apply Subtype.ext
      exact hg
    obtain ⟨X, hXM, hXM'⟩ :=
      Dstage.exists_support_overlap_of_shiftHom_ne_zero
        (k := k) M.1 M'.1 a.toMul t ht
    have hXVi : X ∈ moduleSupport k (V.obj i).obj.obj := by
      simpa only [hi] using hXM
    have hXVia : X.obj.as ∈ moduleSupport k
        ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj
          (V.obj i)).obj.obj := by
      exact mem_moduleSupport_moduleExtensionByZero_of_mem
        (k := k) C S (V.obj i).obj X hXVi
    have hXVj : a.toMul • X ∈ moduleSupport k (V.obj j).obj.obj := by
      simpa only [hj] using hXM'
    have hXVja : (a.toMul • X).obj.as ∈ moduleSupport k
        ((finiteDimensionalModuleExtensionByZero (k := k) C S).obj
          (V.obj j)).obj.obj := by
      exact mem_moduleSupport_moduleExtensionByZero_of_mem
        (k := k) C S (V.obj j).obj (a.toMul • X) hXVj
    obtain ⟨p, ⟨ep⟩⟩ := hV i
    obtain ⟨q, ⟨eq⟩⟩ := hV j
    let J := (IsFiniteDimensionalModule.{u, v, v, v} (C := C) k).ι
    let K := (IsLinearModule.{u, v, v, v} (C := C) k).ι
    have hXp : X.obj.as ∈ moduleSupport k (U.obj p).obj.obj := by
      let epX := (K.mapIso (J.mapIso ep)).app X.obj.as
      exact epX.toLinearEquiv.toEquiv.nontrivial_congr.mpr hXVia
    have hXq : (a.toMul : G) • X.obj.as ∈
        moduleSupport k (U.obj q).obj.obj := by
      let eqX := (K.mapIso (J.mapIso eq)).app ((a.toMul : G) • X.obj.as)
      apply eqX.toLinearEquiv.toEquiv.nontrivial_congr.mpr
      change Nontrivial
        (((finiteDimensionalModuleExtensionByZero (k := k) C S).obj
          (V.obj j)).obj.obj.obj ((a.toMul : G) • X.obj.as))
      change Nontrivial
        (((finiteDimensionalModuleExtensionByZero (k := k) C S).obj
          (V.obj j)).obj.obj.obj (a.toMul • X).obj.as) at hXVja
      simpa only [deletion_smul_obj_as, MulAction.subgroup_smul_def] using hXVja
    have hbad : (a.toMul : G) ∈
        finiteModuleFamilySupportBadDegrees (G := G) U :=
      ⟨hgne, p, q, X.obj.as, hXp, hXq⟩
    exact (havoid (a.toMul : G) hbad a.toMul.property).elim
  exact (eq_zero q).trans (eq_zero r).symm

/-- The intrinsic family obtained by descending every surviving member of the
ambient window is shift-Hom orthogonal at the deletion stage. -/
theorem deletion_survivingModuleFamily_shiftHomOrthogonal_of_ambient_avoids
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (N : Subgroup G) (S : Set C)
    [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := N) S)
    (U : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G) U,
      g ∉ N) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    let hShift :=
      CoherentDeckShift.shiftInvariant_of_actionInvariant (D.restrict N) S hS
    letI := rawHasShift (k := k) S hShift
    letI := deletionHasShift (k := k) S hShift
    letI := deletionMulAction (k := k) S hS
    let Dstage := CoherentDeckShift.deletionCoherentDeckShift
      (k := k) (D.restrict N) S hS
    Dstage.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (Set.range (deletionSurvivingModuleFamily (k := k) C U S).obj) :=
  deletion_finiteModuleWindowShiftHomOrthogonal_of_ambient_avoids
    (D := D)
    (k := k) C N S hS U
      (deletionSurvivingModuleFamily (k := k) C U S)
      (deletionSurvivingModuleFamily_extension_mem_isoClosure
        (k := k) C U S)
      havoid

/-- Shift-Hom orthogonality extends from the descended surviving
representatives to their full additive closure, the window used for source and
sink middle terms. -/
theorem deletion_survivingModuleFamily_additiveClosure_shiftHomOrthogonal_of_ambient_avoids
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (N : Subgroup G) (S : Set C)
    [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := N) S)
    (U : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G) U,
      g ∉ N) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    let hShift :=
      CoherentDeckShift.shiftInvariant_of_actionInvariant (D.restrict N) S hS
    letI := rawHasShift (k := k) S hShift
    letI := deletionHasShift (k := k) S hShift
    letI := deletionMulAction (k := k) S hS
    let Dstage := CoherentDeckShift.deletionCoherentDeckShift
      (k := k) (D.restrict N) S hS
    Dstage.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (deletionSurvivingModuleFamily (k := k) C U S).additiveClosure := by
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  let hShift :=
    CoherentDeckShift.shiftInvariant_of_actionInvariant (D.restrict N) S hS
  letI := rawHasShift (k := k) S hShift
  letI := deletionHasShift (k := k) S hShift
  letI := deletionMulAction (k := k) S hS
  let Dstage := CoherentDeckShift.deletionCoherentDeckShift
    (k := k) (D.restrict N) S hS
  have hRange :=
    deletion_survivingModuleFamily_shiftHomOrthogonal_of_ambient_avoids
      (k := k) (D := D) C N S hS U havoid
  exact Dstage.finiteModuleWindowShiftHomOrthogonal_additiveClosure
    (deletionSurvivingModuleFamily (k := k) C U S)
    (Dstage.finiteModuleWindowShiftHomOrthogonal_isoClosure
      (deletionSurvivingModuleFamily (k := k) C U S) hRange)

/-- The preceding transfer specialized to every literal accumulated
subgroup-orbit deletion stage of the covering-average telescope. -/
theorem stage_survivingModuleFamily_shiftHomOrthogonal_of_ambient_avoids
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (j : Fin (m + 1))
    (U : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G) U,
      g ∉ N) :
    letI := stageMulAction (k := k) N representative x j
    let Dstage := stageCoherentDeckShift (k := k)
      D hC N representative x j
    Dstage.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (deletionSurvivingModuleFamily (k := k) C U
        (stageDeletedSet N representative x j)).additiveClosure := by
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (stageDeletedSet N representative x j) :=
    isClosedUnderIsomorphisms_of_skeletal hC _
  exact deletion_survivingModuleFamily_additiveClosure_shiftHomOrthogonal_of_ambient_avoids
    (k := k) (D := D) C N (stageDeletedSet N representative x j)
      (stageDeletedSet_actionInvariant N representative x j) U havoid

end MagnitudeConjecture.ObjectDeletion
