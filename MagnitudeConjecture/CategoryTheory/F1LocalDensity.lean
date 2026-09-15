import MagnitudeConjecture.CategoryTheory.LocallyFiniteModuleLocalDensity
import MagnitudeConjecture.CategoryTheory.ObjectDeletionAlmostSplit

/-!
# Foundational deletion-local density for the frozen proof

This module contains only the restriction/extension comparison needed by the
incoming-Hom locality argument.  It deliberately does not import the former
control-window or surviving-window developments.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion.Frozen

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]

/-- The local density after deletion, extended by zero when the ambient
module does not survive the deleted objects. -/
noncomputable def extendedLocalDensity
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) : ℤ := by
  classical
  exact if hvanish : ModuleVanishesOnDeleted (k := k) C S M.obj.obj then
    finiteModuleLocalDensity
      (isLocallyRepresentationFinite_deletion (k := k) C S hlocal)
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k) C S M hvanish)
      (finiteDimensionalModuleRestrictionToDeletion_indec
        (k := k) C S M hM hvanish)
  else 0

/-- The pointwise local-density change across an arbitrary object deletion. -/
noncomputable def localChange
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : Set C)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M) : ℤ :=
  finiteModuleLocalDensity hlocal M hM -
    extendedLocalDensity (k := k) C hlocal S M hM

/-- Restriction preserves the intrinsic local density when a minimal sink
source also survives. -/
theorem restriction_localDensity_eq_of_minimalSink_source_vanishes
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

/-- If the endpoint and one of its minimal sink sources survive, its local
density change is zero. -/
theorem localChange_eq_zero_of_minimalSink_source_vanishes
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
    localChange (k := k) C hlocal S M hM = 0 := by
  have hDensity :=
    restriction_localDensity_eq_of_minimalSink_source_vanishes
      (k := k) C hP hlocal S M hM hvanish g hg hgmin dY hY
  rw [localChange, extendedLocalDensity, dif_pos hvanish, hDensity,
    sub_self]

end MagnitudeConjecture.ObjectDeletion.Frozen
