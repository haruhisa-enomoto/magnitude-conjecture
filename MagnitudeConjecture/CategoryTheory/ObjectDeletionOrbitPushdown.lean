import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdown
import MagnitudeConjecture.CategoryTheory.ObjectDeletionDeckOrbit
import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleInheritance
import MagnitudeConjecture.CategoryTheory.ObjectDeletionOrbit
import MagnitudeConjecture.CategoryTheory.OrbitPushdownChangeBase

/-!
# Gabriel push-down across object deletion

For a shift-invariant set of objects, extension by zero followed by Gabriel
push-down vanishes on the corresponding objects of the shift-orbit category.
This is the vanishing input for the natural comparison between deleting
before and after push-down.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {A : Type v} [AddGroup A]
variable [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]
variable [∀ a : A, (shiftFunctor C a).Linear k]

/-- Push-down of an extension-by-zero module vanishes at every deleted orbit
object. -/
theorem orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
    (S : Set C) (hS : ShiftInvariant (C := C) A S)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    ModuleVanishesOnDeleted
      (k := k) (ShiftOrbitCategory C A) S
      (orbitPushdown (A := A)
        (moduleExtensionByZero (k := k) C S M.obj)) := by
  intro X hX
  rw [ModuleCat.isZero_iff_subsingleton]
  change Subsingleton
    (DirectSum A fun a ↦
      (moduleExtensionByZero (k := k) C S M.obj).obj
        ((shiftFunctor C a).obj X))
  rw [subsingleton_directSum_iff]
  intro a
  apply ModuleCat.isZero_iff_subsingleton.mp
  apply moduleExtensionByZero_obj_isZero_of_mem (k := k) C S M.obj
  exact (hS a X).2 hX

/-- The raw deletion-quotient module underlying extension by zero. -/
noncomputable def moduleExtensionByZeroRawQuotient
    (S : Set C)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    RawCategory (k := k) C S ⥤ ModuleCat.{v} k :=
  (ideal (k := k) C S).quotientLift
    (moduleExtensionByZero (k := k) C S M.obj)
    (module_isKilledBy_of_vanishesOnDeleted (k := k) C S
      (moduleExtensionByZero (k := k) C S M.obj)
      (fun _X hX ↦
        moduleExtensionByZero_obj_isZero_of_mem (k := k) C S M.obj hX))

noncomputable instance moduleExtensionByZeroRawQuotient_additive
    (S : Set C)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    (moduleExtensionByZeroRawQuotient (k := k) (C := C) S M).Additive := by
  unfold moduleExtensionByZeroRawQuotient
  exact
    QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.quotientLift_additive
      (ideal (k := k) C S)
      (moduleExtensionByZero (k := k) C S M.obj)
      (module_isKilledBy_of_vanishesOnDeleted (k := k) C S
        (moduleExtensionByZero (k := k) C S M.obj)
        (fun X hX ↦
          moduleExtensionByZero_obj_isZero_of_mem (k := k) C S M.obj hX))

noncomputable instance moduleExtensionByZeroRawQuotient_linear
    (S : Set C)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    (moduleExtensionByZeroRawQuotient (k := k) (C := C) S M).Linear k := by
  unfold moduleExtensionByZeroRawQuotient
  exact
    QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal.quotientLift_linear
      (ideal (k := k) C S)
      (moduleExtensionByZero (k := k) C S M.obj)
      (module_isKilledBy_of_vanishesOnDeleted (k := k) C S
        (moduleExtensionByZero (k := k) C S M.obj)
        (fun X hX ↦
          moduleExtensionByZero_obj_isZero_of_mem (k := k) C S M.obj hX))

set_option backward.isDefEq.respectTransparency false in
/-- Push-down of a deletion module is the change-of-base pullback of
push-down of its raw quotient module. -/
noncomputable def orbitPushdownDeletionToRawIso
    (S : Set C) (hS : ShiftInvariant (C := C) A S)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hS a
    orbitPushdown (A := A) M.obj ≅
      shiftOrbitMapFunctor (k := k) (A := A)
          (IsSurvivingRaw (k := k) C S).ι ⋙
        orbitPushdown (A := A)
          (moduleExtensionByZeroRawQuotient (k := k) (C := C) S M) := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  let P := IsSurvivingRaw (k := k) C S
  letI : P.ι.CommShift A := deletionInclusionCommShift (k := k) S hS
  let F := linearModuleExtensionByZero (k := k) C S
  let hvanish : ModuleVanishesOnDeleted (k := k) C S
      (F.obj M).obj := fun X hX ↦
    moduleExtensionByZero_obj_isZero_of_mem (k := k) C S M.obj hX
  let R := linearModuleRestrictionToDeletion
    (k := k) C S (F.obj M) hvanish
  let eR : R ≅ M := linearModuleExtensionRestrictionIso
    (k := k) C S M
  let Push := linearModuleOrbitPushdown
    (k := k) (C := DeletionCategory (k := k) C S) (A := A)
  let J := (IsLinearModule.{u, v, v, v}
    (C := ShiftOrbitCategory (DeletionCategory (k := k) C S) A) k).ι
  let eMapped : orbitPushdown (A := A) R.obj ≅
      orbitPushdown (A := A) M.obj := J.mapIso (Push.mapIso eR)
  let Q := moduleExtensionByZeroRawQuotient (k := k) (C := C) S M
  have eChange : orbitPushdown (A := A) (P.ι ⋙ Q) ≅
      shiftOrbitMapFunctor (k := k) (A := A) P.ι ⋙
        orbitPushdown (A := A) Q :=
    orbitPushdownCommShiftIso (k := k) (A := A) P.ι Q
  exact eMapped.symm ≪≫ eChange

set_option backward.isDefEq.respectTransparency false in
/-- Push-down of an extension by zero is the change-of-base pullback of the
same raw quotient push-down. -/
noncomputable def orbitPushdownExtensionToRawIso
    (S : Set C) (hS : ShiftInvariant (C := C) A S)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI : (rawFunctor (k := k) C S).CommShift A :=
      rawFunctorCommShift (k := k) S hS
    orbitPushdown (A := A)
        (moduleExtensionByZero (k := k) C S M.obj) ≅
      shiftOrbitMapFunctor (k := k) (A := A)
          (rawFunctor (k := k) C S) ⋙
        orbitPushdown (A := A)
          (moduleExtensionByZeroRawQuotient (k := k) (C := C) S M) := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  let Q := moduleExtensionByZeroRawQuotient (k := k) (C := C) S M
  exact orbitPushdownCommShiftIso (k := k) (A := A)
    (rawFunctor (k := k) C S) Q

set_option backward.isDefEq.respectTransparency false in
/-- The extension/raw change-of-base isomorphism descends through deletion in
the ambient shift-orbit category. -/
noncomputable def orbitPushdownExtensionRestrictionToRawIso
    (S : Set C) (hS : ShiftInvariant (C := C) A S)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI : (rawFunctor (k := k) C S).CommShift A :=
      rawFunctorCommShift (k := k) S hS
    let L := orbitPushdown (A := A)
      (moduleExtensionByZero (k := k) C S M.obj)
    let R := shiftOrbitMapFunctor (k := k) (A := A)
        (rawFunctor (k := k) C S) ⋙
      orbitPushdown (A := A)
        (moduleExtensionByZeroRawQuotient (k := k) (C := C) S M)
    let hL : ModuleVanishesOnDeleted
        (k := k) (ShiftOrbitCategory C A) S L :=
      orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
        (k := k) S hS M
    let e : L ≅ R := orbitPushdownExtensionToRawIso
      (k := k) S hS M
    let hR : ModuleVanishesOnDeleted
        (k := k) (ShiftOrbitCategory C A) S R := fun X hX ↦
      (e.app X).isZero_iff.mp (hL X hX)
    moduleRestrictionToDeletion
        (k := k) (ShiftOrbitCategory C A) S L hL ≅
      moduleRestrictionToDeletion
        (k := k) (ShiftOrbitCategory C A) S R hR := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  let L := orbitPushdown (A := A)
    (moduleExtensionByZero (k := k) C S M.obj)
  let R := shiftOrbitMapFunctor (k := k) (A := A)
      (rawFunctor (k := k) C S) ⋙
    orbitPushdown (A := A)
      (moduleExtensionByZeroRawQuotient (k := k) (C := C) S M)
  let hL : ModuleVanishesOnDeleted
      (k := k) (ShiftOrbitCategory C A) S L :=
    orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
      (k := k) S hS M
  let e : L ≅ R := orbitPushdownExtensionToRawIso
    (k := k) S hS M
  let hR : ModuleVanishesOnDeleted
      (k := k) (ShiftOrbitCategory C A) S R := fun X hX ↦
    (e.app X).isZero_iff.mp (hL X hX)
  exact moduleRestrictionToDeletionIso
    (k := k) (ShiftOrbitCategory C A) S L R hL hR e

set_option backward.isDefEq.respectTransparency false in
/-- The restriction of the raw change-of-base module is the pullback from the
common surviving raw orbit category. -/
noncomputable def orbitDeletionRawRestrictionIso
    (S : Set C) (hS : ShiftInvariant (C := C) A S)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI : (rawFunctor (k := k) C S).CommShift A :=
      rawFunctorCommShift (k := k) S hS
    let Qm := moduleExtensionByZeroRawQuotient (k := k) (C := C) S M
    let L := orbitPushdown (A := A)
      (moduleExtensionByZero (k := k) C S M.obj)
    let R := shiftOrbitMapFunctor (k := k) (A := A)
        (rawFunctor (k := k) C S) ⋙ orbitPushdown (A := A) Qm
    let hL : ModuleVanishesOnDeleted
        (k := k) (ShiftOrbitCategory C A) S L :=
      orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
        (k := k) S hS M
    let e : L ≅ R := orbitPushdownExtensionToRawIso
      (k := k) S hS M
    let hR : ModuleVanishesOnDeleted
        (k := k) (ShiftOrbitCategory C A) S R := fun X hX ↦
      (e.app X).isZero_iff.mp (hL X hX)
    let Q : ObjectProperty
        (ShiftOrbitCategory (RawCategory (k := k) C S) A) :=
      OrbitIsSurvivingRaw (k := k) (C := C) (A := A) S
    moduleRestrictionToDeletion
        (k := k) (ShiftOrbitCategory C A) S R hR ≅
      orbitDeletionToSurvivingRawOrbitFunctor (k := k) S hS ⋙
        Q.ι ⋙ orbitPushdown (A := A) Qm := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  let Qm := moduleExtensionByZeroRawQuotient (k := k) (C := C) S M
  let L := orbitPushdown (A := A)
    (moduleExtensionByZero (k := k) C S M.obj)
  let R := shiftOrbitMapFunctor (k := k) (A := A)
      (rawFunctor (k := k) C S) ⋙ orbitPushdown (A := A) Qm
  let hL : ModuleVanishesOnDeleted
      (k := k) (ShiftOrbitCategory C A) S L :=
    orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
      (k := k) S hS M
  let e : L ≅ R := orbitPushdownExtensionToRawIso
    (k := k) S hS M
  let hR : ModuleVanishesOnDeleted
      (k := k) (ShiftOrbitCategory C A) S R := fun X hX ↦
    (e.app X).isZero_iff.mp (hL X hX)
  let Q : ObjectProperty
      (ShiftOrbitCategory (RawCategory (k := k) C S) A) :=
    OrbitIsSurvivingRaw (k := k) (C := C) (A := A) S
  change moduleRestrictionToDeletion
      (k := k) (ShiftOrbitCategory C A) S R hR ≅
    orbitDeletionToSurvivingRawOrbitFunctor (k := k) S hS ⋙
      Q.ι ⋙ orbitPushdown (A := A) Qm
  exact NatIso.ofComponents (fun X ↦ Iso.refl _) (by
    intro X Y f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    obtain ⟨g, hg⟩ :=
      (rawFunctor (k := k) (ShiftOrbitCategory C A) S).map_surjective f.hom
    change
      ((ideal (k := k) (ShiftOrbitCategory C A) S).quotientLift R
        (module_isKilledBy_of_vanishesOnDeleted
          (k := k) (ShiftOrbitCategory C A) S R hR)).map f.hom = _
    rw [← hg]
    change R.map g =
      (orbitPushdown (A := A) Qm).map
        ((rawOrbitDeletionComparisonFunctor (k := k) S hS).map f.hom)
    rw [← hg]
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The deletion-side raw change-of-base module is the pullback from the same
common surviving raw orbit category. -/
noncomputable def deletionOrbitRawPullbackIso
    (S : Set C) (hS : ShiftInvariant (C := C) A S)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hS a
    let Qm := moduleExtensionByZeroRawQuotient (k := k) (C := C) S M
    let Q : ObjectProperty
        (ShiftOrbitCategory (RawCategory (k := k) C S) A) :=
      OrbitIsSurvivingRaw (k := k) (C := C) (A := A) S
    shiftOrbitMapFunctor (k := k) (A := A)
        (IsSurvivingRaw (k := k) C S).ι ⋙ orbitPushdown (A := A) Qm ≅
      deletionShiftOrbitInclusionFunctor (k := k) S hS ⋙
        Q.ι ⋙ orbitPushdown (A := A) Qm := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- Gabriel push-down commutes with shift-invariant object deletion.  The
module obtained by pushing down after deletion is the pullback, through the
canonical orbit/deletion equivalence, of the restriction of the push-down of
the extension-by-zero module. -/
noncomputable def orbitPushdownDeletionIso
    (S : Set C) (hS : ShiftInvariant (C := C) A S)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    letI := rawHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hS a
    letI := deletionHasShift (k := k) S hS
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hS a
    letI : ∀ a : A,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hS a
    let L := orbitPushdown (A := A)
      (moduleExtensionByZero (k := k) C S M.obj)
    let hL : ModuleVanishesOnDeleted
        (k := k) (ShiftOrbitCategory C A) S L :=
      orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
        (k := k) S hS M
    orbitPushdown (A := A) M.obj ≅
      (deletionOrbitEquivalence (k := k) S hS).functor ⋙
        moduleRestrictionToDeletion
          (k := k) (ShiftOrbitCategory C A) S L hL := by
  letI := rawHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hS a
  letI : (rawFunctor (k := k) C S).CommShift A :=
    rawFunctorCommShift (k := k) S hS
  letI := deletionHasShift (k := k) S hS
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hS a
  letI : ∀ a : A,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hS a
  let Qm := moduleExtensionByZeroRawQuotient (k := k) (C := C) S M
  let Q : ObjectProperty
      (ShiftOrbitCategory (RawCategory (k := k) C S) A) :=
    OrbitIsSurvivingRaw (k := k) (C := C) (A := A) S
  let common := Q.ι ⋙ orbitPushdown (A := A) Qm
  let eDel := deletionShiftOrbitInclusionEquivalence (k := k) S hS
  let eOrb := orbitDeletionToSurvivingRawOrbitEquivalence (k := k) S hS
  let E := deletionOrbitEquivalence (k := k) S hS
  let L := orbitPushdown (A := A)
    (moduleExtensionByZero (k := k) C S M.obj)
  let hL : ModuleVanishesOnDeleted
      (k := k) (ShiftOrbitCategory C A) S L :=
    orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
      (k := k) S hS M
  let R := shiftOrbitMapFunctor (k := k) (A := A)
      (rawFunctor (k := k) C S) ⋙ orbitPushdown (A := A) Qm
  let eExt : L ≅ R := orbitPushdownExtensionToRawIso
    (k := k) S hS M
  let hR : ModuleVanishesOnDeleted
      (k := k) (ShiftOrbitCategory C A) S R := fun X hX ↦
    (eExt.app X).isZero_iff.mp (hL X hX)
  let RestL := moduleRestrictionToDeletion
    (k := k) (ShiftOrbitCategory C A) S L hL
  let RestR := moduleRestrictionToDeletion
    (k := k) (ShiftOrbitCategory C A) S R hR
  let a₁ := orbitPushdownDeletionToRawIso (k := k) S hS M
  let a₂ := deletionOrbitRawPullbackIso (k := k) S hS M
  let a : orbitPushdown (A := A) M.obj ≅ eDel.functor ⋙ common :=
    a₁ ≪≫ a₂
  let b₁ : RestL ≅ RestR :=
    orbitPushdownExtensionRestrictionToRawIso (k := k) S hS M
  let b₂ : RestR ≅ eOrb.functor ⋙ common :=
    orbitDeletionRawRestrictionIso (k := k) S hS M
  let b : RestL ≅ eOrb.functor ⋙ common := b₁ ≪≫ b₂
  let collapse : E.functor ⋙ (eOrb.functor ⋙ common) ≅
      eDel.functor ⋙ common :=
    Functor.associator eDel.functor eOrb.inverse
        (eOrb.functor ⋙ common) ≪≫
      Functor.isoWhiskerLeft eDel.functor
        (Functor.associator eOrb.inverse eOrb.functor common).symm ≪≫
      Functor.isoWhiskerLeft eDel.functor (eOrb.invFunIdAssoc common)
  let pulled : E.functor ⋙ RestL ≅ eDel.functor ⋙ common :=
    Functor.isoWhiskerLeft E.functor b ≪≫ collapse
  exact a ≪≫ pulled.symm

section DeckSkeleton

variable {G : Type v} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

set_option backward.isDefEq.respectTransparency false in
/-- The deck-orbit skeleton of an invariant deletion is canonically
equivalent to deleting the corresponding orbit classes from the ambient
deck-orbit skeleton. -/
noncomputable def deckOrbitDeletionCommEquivalence
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k := k) S hShift
    letI : ∀ a : Additive G,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
    letI : ∀ a : Additive G,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
    letI := deletionHasShift (k := k) S hShift
    letI : ∀ a : Additive G,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hShift a
    letI : ∀ a : Additive G,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hShift a
    letI := deletionMulAction (k := k) S hS
    DeckOrbitSkeleton (DeletionCategory (k := k) C S) G ≌
      DeletionCategory (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
  letI := rawHasShift (k := k) S hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
  letI := deletionHasShift (k := k) S hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hShift a
  letI := deletionMulAction (k := k) S hS
  let DS := CoherentDeckShift.deletionCoherentDeckShift (k := k) D S hS
  haveI : ∀ a : Additive G, (DS.core.F a).Additive :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_additive
      (k := k) D S hS a
  haveI : ∀ a : Additive G, (DS.core.F a).Linear k :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_linear
      (k := k) D S hS a
  exact DS.deckOrbitSkeletonEquivalence.trans
    ((deletionOrbitEquivalence (k := k) S hShift).trans
      (MagnitudeConjecture.ObjectDeletion.CoherentDeckShift.deckOrbitDeletionEquivalence
        (k := k) D S hS).symm)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance deckOrbitDeletionCommEquivalence_functor_additive
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k := k) S hShift
    letI : ∀ a : Additive G,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
    letI : ∀ a : Additive G,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
    letI := deletionHasShift (k := k) S hShift
    letI : ∀ a : Additive G,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hShift a
    letI : ∀ a : Additive G,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hShift a
    letI := deletionMulAction (k := k) S hS
    let E := deckOrbitDeletionCommEquivalence (k := k) D S hS
    E.functor.Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
  letI := rawHasShift (k := k) S hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
  letI := deletionHasShift (k := k) S hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hShift a
  letI := deletionMulAction (k := k) S hS
  change (deckOrbitDeletionCommEquivalence (k := k) D S hS).functor.Additive
  let DS := CoherentDeckShift.deletionCoherentDeckShift (k := k) D S hS
  haveI : ∀ a : Additive G, (DS.core.F a).Additive :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_additive
      (k := k) D S hS a
  haveI : ∀ a : Additive G, (DS.core.F a).Linear k :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_linear
      (k := k) D S hS a
  letI := DS.hasShift
  letI := DS.additiveShift
  letI := DS.linearShift (k := k)
  let eRep := DS.deckOrbitSkeletonEquivalence
  let eOrbit := deletionOrbitEquivalence (k := k) S hShift
  let eDeck :=
    MagnitudeConjecture.ObjectDeletion.CoherentDeckShift.deckOrbitDeletionEquivalence
      (k := k) D S hS
  letI : eRep.functor.Additive :=
    CoherentDeckShift.deckOrbitSkeletonEquivalence_functor_additive DS
  letI : eOrbit.functor.Additive :=
    deletionOrbitEquivalence_functor_additive (k := k) S hShift
  letI : eDeck.functor.Additive :=
    MagnitudeConjecture.ObjectDeletion.CoherentDeckShift.deckOrbitDeletionEquivalence_functor_additive
      (k := k) D S hS
  letI : eDeck.inverse.Additive := inferInstance
  change (eRep.functor ⋙ (eOrbit.functor ⋙ eDeck.inverse)).Additive
  constructor
  intro X Y f g
  change eDeck.inverse.map
      (eOrbit.functor.map (eRep.functor.map (f + g))) = _
  rw [eRep.functor.map_add, eOrbit.functor.map_add,
    eDeck.inverse.map_add]
  rfl

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance deckOrbitDeletionCommEquivalence_functor_linear
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k := k) S hShift
    letI : ∀ a : Additive G,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
    letI : ∀ a : Additive G,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
    letI := deletionHasShift (k := k) S hShift
    letI : ∀ a : Additive G,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hShift a
    letI : ∀ a : Additive G,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hShift a
    letI := deletionMulAction (k := k) S hS
    let E := deckOrbitDeletionCommEquivalence (k := k) D S hS
    E.functor.Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
  letI := rawHasShift (k := k) S hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
  letI := deletionHasShift (k := k) S hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hShift a
  letI := deletionMulAction (k := k) S hS
  change (deckOrbitDeletionCommEquivalence (k := k) D S hS).functor.Linear k
  let DS := CoherentDeckShift.deletionCoherentDeckShift (k := k) D S hS
  haveI : ∀ a : Additive G, (DS.core.F a).Additive :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_additive
      (k := k) D S hS a
  haveI : ∀ a : Additive G, (DS.core.F a).Linear k :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_linear
      (k := k) D S hS a
  letI := DS.hasShift
  letI := DS.additiveShift
  letI := DS.linearShift (k := k)
  let eRep := DS.deckOrbitSkeletonEquivalence
  let eOrbit := deletionOrbitEquivalence (k := k) S hShift
  let eDeck :=
    MagnitudeConjecture.ObjectDeletion.CoherentDeckShift.deckOrbitDeletionEquivalence
      (k := k) D S hS
  letI : eRep.functor.Linear k :=
    CoherentDeckShift.deckOrbitSkeletonEquivalence_functor_linear DS
  letI : eOrbit.functor.Linear k :=
    deletionOrbitEquivalence_functor_linear (k := k) S hShift
  letI : eDeck.functor.Linear k :=
    MagnitudeConjecture.ObjectDeletion.CoherentDeckShift.deckOrbitDeletionEquivalence_functor_linear
      (k := k) D S hS
  letI : eDeck.inverse.Linear k := inferInstance
  change (eRep.functor ⋙ (eOrbit.functor ⋙ eDeck.inverse)).Linear k
  constructor
  intro X Y f r
  change eDeck.inverse.map
      (eOrbit.functor.map (eRep.functor.map (r • f))) = _
  rw [eRep.functor.map_smul, eOrbit.functor.map_smul,
    eDeck.inverse.map_smul]
  rfl

/-- Skeletal push-down of an extension-by-zero module vanishes on every
deleted deck-orbit class. -/
theorem orbitSkeletonPushdown_moduleExtensionByZero_vanishesOnDeleted
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ModuleVanishesOnDeleted
      (k := k) (DeckOrbitSkeleton C G) (deckOrbitDeletedSet (G := G) S)
      (orbitSkeletonPushdown (G := G)
        (moduleExtensionByZero (k := k) C S M.obj)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
  let hL := orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
    (k := k) S hShift M
  intro q hq
  exact hL
    (deckOrbitRepresentative (C := C) (G := G) q) hq

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of skeletal push-down is the pullback of the nonskeletal
restriction through the deck-orbit deletion comparison. -/
noncomputable def orbitSkeletonPushdownRestrictionComparisonIso
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
    let L := orbitPushdown (A := Additive G)
      (moduleExtensionByZero (k := k) C S M.obj)
    let hL : ModuleVanishesOnDeleted
        (k := k) (ShiftOrbitCategory C (Additive G)) S L :=
      orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
        (k := k) S hShift M
    let Lskel := orbitSkeletonPushdown (G := G)
      (moduleExtensionByZero (k := k) C S M.obj)
    let hLskel : ModuleVanishesOnDeleted
        (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S) Lskel :=
      orbitSkeletonPushdown_moduleExtensionByZero_vanishesOnDeleted
        (k := k) D S hS M
    moduleRestrictionToDeletion
        (k := k) (DeckOrbitSkeleton C G)
          (deckOrbitDeletedSet (G := G) S) Lskel hLskel ≅
      (MagnitudeConjecture.ObjectDeletion.CoherentDeckShift.deckOrbitDeletionEquivalence
          (k := k) D S hS).functor ⋙
        moduleRestrictionToDeletion
          (k := k) (ShiftOrbitCategory C (Additive G)) S L hL := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
  let L := orbitPushdown (A := Additive G)
    (moduleExtensionByZero (k := k) C S M.obj)
  let hL : ModuleVanishesOnDeleted
      (k := k) (ShiftOrbitCategory C (Additive G)) S L :=
    orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
      (k := k) S hShift M
  let Lskel := orbitSkeletonPushdown (G := G)
    (moduleExtensionByZero (k := k) C S M.obj)
  let hLskel : ModuleVanishesOnDeleted
      (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S) Lskel :=
    orbitSkeletonPushdown_moduleExtensionByZero_vanishesOnDeleted
      (k := k) D S hS M
  let E := MagnitudeConjecture.ObjectDeletion.CoherentDeckShift.deckOrbitDeletionEquivalence
    (k := k) D S hS
  change moduleRestrictionToDeletion
      (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S) Lskel hLskel ≅
    E.functor ⋙ moduleRestrictionToDeletion
      (k := k) (ShiftOrbitCategory C (Additive G)) S L hL
  exact NatIso.ofComponents (fun X ↦ Iso.refl _) (by
    intro X Y f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    obtain ⟨g, hg⟩ :=
      (rawFunctor (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S)).map_surjective f.hom
    change
      ((ideal (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S)).quotientLift Lskel
          (module_isKilledBy_of_vanishesOnDeleted
            (k := k) (DeckOrbitSkeleton C G)
              (deckOrbitDeletedSet (G := G) S) Lskel hLskel)).map f.hom = _
    rw [← hg]
    change Lskel.map g =
      ((ideal (k := k) (ShiftOrbitCategory C (Additive G)) S).quotientLift L
        (module_isKilledBy_of_vanishesOnDeleted
          (k := k) (ShiftOrbitCategory C (Additive G)) S L hL)).map
            ((MagnitudeConjecture.ObjectDeletion.CoherentDeckShift.rawDeckOrbitDeletionComparisonFunctor
              (k := k) D S).map f.hom)
    rw [← hg]
    rfl)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Skeletal Gabriel push-down commutes with invariant object deletion. -/
noncomputable def orbitSkeletonPushdownDeletionIso
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S)
    (M : LinearModuleCategory.{u, v, v, v}
      (C := DeletionCategory (k := k) C S) k) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k := k) S hShift
    letI : ∀ a : Additive G,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
    letI : ∀ a : Additive G,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
    letI := deletionHasShift (k := k) S hShift
    letI : ∀ a : Additive G,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hShift a
    letI : ∀ a : Additive G,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hShift a
    letI := deletionMulAction (k := k) S hS
    let Lskel := orbitSkeletonPushdown (G := G)
      (moduleExtensionByZero (k := k) C S M.obj)
    let hLskel : ModuleVanishesOnDeleted
        (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S) Lskel :=
      orbitSkeletonPushdown_moduleExtensionByZero_vanishesOnDeleted
        (k := k) D S hS M
    orbitSkeletonPushdown (G := G) M.obj ≅
      (deckOrbitDeletionCommEquivalence (k := k) D S hS).functor ⋙
        moduleRestrictionToDeletion
          (k := k) (DeckOrbitSkeleton C G)
          (deckOrbitDeletedSet (G := G) S) Lskel hLskel := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
  letI := rawHasShift (k := k) S hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
  letI := deletionHasShift (k := k) S hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hShift a
  letI := deletionMulAction (k := k) S hS
  let DS := CoherentDeckShift.deletionCoherentDeckShift (k := k) D S hS
  haveI : ∀ a : Additive G, (DS.core.F a).Additive :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_additive
      (k := k) D S hS a
  haveI : ∀ a : Additive G, (DS.core.F a).Linear k :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_linear
      (k := k) D S hS a
  let eRep := DS.deckOrbitSkeletonEquivalence
  let eOrbit := deletionOrbitEquivalence (k := k) S hShift
  let eDeck :=
    MagnitudeConjecture.ObjectDeletion.CoherentDeckShift.deckOrbitDeletionEquivalence
      (k := k) D S hS
  let E := deckOrbitDeletionCommEquivalence (k := k) D S hS
  let L := orbitPushdown (A := Additive G)
    (moduleExtensionByZero (k := k) C S M.obj)
  let hL : ModuleVanishesOnDeleted
      (k := k) (ShiftOrbitCategory C (Additive G)) S L :=
    orbitPushdown_moduleExtensionByZero_vanishesOnDeleted
      (k := k) S hShift M
  let Lskel := orbitSkeletonPushdown (G := G)
    (moduleExtensionByZero (k := k) C S M.obj)
  let hLskel : ModuleVanishesOnDeleted
      (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S) Lskel :=
    orbitSkeletonPushdown_moduleExtensionByZero_vanishesOnDeleted
      (k := k) D S hS M
  let Rest := moduleRestrictionToDeletion
    (k := k) (ShiftOrbitCategory C (Additive G)) S L hL
  let RestSkel := moduleRestrictionToDeletion
    (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S) Lskel hLskel
  let n := orbitPushdownDeletionIso (k := k) S hShift M
  let a : orbitSkeletonPushdown (G := G) M.obj ≅
      eRep.functor ⋙ (eOrbit.functor ⋙ Rest) :=
    Functor.isoWhiskerLeft eRep.functor n
  let c : RestSkel ≅ eDeck.functor ⋙ Rest :=
    orbitSkeletonPushdownRestrictionComparisonIso (k := k) D S hS M
  let inner : eDeck.inverse ⋙ RestSkel ≅ Rest :=
    Functor.isoWhiskerLeft eDeck.inverse c ≪≫
      (Functor.associator eDeck.inverse eDeck.functor Rest).symm ≪≫
      eDeck.invFunIdAssoc Rest
  let pre := eRep.functor ⋙ eOrbit.functor
  let collapse : E.functor ⋙ RestSkel ≅
      eRep.functor ⋙ (eOrbit.functor ⋙ Rest) :=
    Functor.associator pre eDeck.inverse RestSkel ≪≫
      Functor.isoWhiskerLeft pre inner ≪≫
      Functor.associator eRep.functor eOrbit.functor Rest
  exact a ≪≫ collapse.symm

/-- Skeletal push-down preserves vanishing on an invariant deleted set. -/
theorem orbitSkeletonPushdown_vanishesOnDeleted_of_vanishesOnDeleted
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S)
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k)
    (hM : ModuleVanishesOnDeleted (k := k) C S M.obj) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ModuleVanishesOnDeleted
      (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S)
      (orbitSkeletonPushdown (G := G) M.obj) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let R := linearModuleRestrictionToDeletion (k := k) C S M hM
  let F := linearModuleExtensionByZero (k := k) C S
  let eExt := linearModuleRestrictionExtensionIso (k := k) C S M hM
  let Push := linearModuleOrbitSkeletonPushdown
    (k := k) (C := C) (G := G)
  let J := (IsLinearModule.{u, v, v, v}
    (C := DeckOrbitSkeleton C G) k).ι
  let ePush : orbitSkeletonPushdown (G := G) (F.obj R).obj ≅
      orbitSkeletonPushdown (G := G) M.obj :=
    J.mapIso (Push.mapIso eExt)
  let hExt :=
    orbitSkeletonPushdown_moduleExtensionByZero_vanishesOnDeleted
      (k := k) D S hS R
  intro X hX
  exact ((ePush.app X).isZero_iff).1 (hExt X hX)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- For an ambient module which already vanishes on an invariant deleted
set, skeletal push-down commutes with restricting that module to the deletion
category. -/
noncomputable def orbitSkeletonPushdownRestrictionIso
    (S : Set C) [ObjectProperty.IsClosedUnderIsomorphisms S]
    (hS : ActionInvariant (G := G) S)
    (M : LinearModuleCategory.{u, v, v, v} (C := C) k)
    (hM : ModuleVanishesOnDeleted (k := k) C S M.obj) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
    letI := rawHasShift (k := k) S hShift
    letI : ∀ a : Additive G,
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
    letI : ∀ a : Additive G,
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
    letI := deletionHasShift (k := k) S hShift
    letI : ∀ a : Additive G,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hShift a
    letI : ∀ a : Additive G,
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hShift a
    letI := deletionMulAction (k := k) S hS
    let R := linearModuleRestrictionToDeletion (k := k) C S M hM
    let hP : ModuleVanishesOnDeleted
        (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S)
        (orbitSkeletonPushdown (G := G) M.obj) := by
      exact orbitSkeletonPushdown_vanishesOnDeleted_of_vanishesOnDeleted
        (k := k) D S hS M hM
    orbitSkeletonPushdown (G := G) R.obj ≅
      (deckOrbitDeletionCommEquivalence (k := k) D S hS).functor ⋙
        moduleRestrictionToDeletion
          (k := k) (DeckOrbitSkeleton C G)
          (deckOrbitDeletedSet (G := G) S)
          (orbitSkeletonPushdown (G := G) M.obj) hP := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant D S hS
  letI := rawHasShift (k := k) S hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
  letI := deletionHasShift (k := k) S hShift
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hShift a
  letI : ∀ a : Additive G,
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hShift a
  letI := deletionMulAction (k := k) S hS
  let R := linearModuleRestrictionToDeletion (k := k) C S M hM
  let hP : ModuleVanishesOnDeleted
      (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S)
      (orbitSkeletonPushdown (G := G) M.obj) :=
    orbitSkeletonPushdown_vanishesOnDeleted_of_vanishesOnDeleted
      (k := k) D S hS M hM
  let n := orbitSkeletonPushdownDeletionIso (k := k) D S hS R
  let F := linearModuleExtensionByZero (k := k) C S
  let eExt := linearModuleRestrictionExtensionIso (k := k) C S M hM
  let Push := linearModuleOrbitSkeletonPushdown
    (k := k) (C := C) (G := G)
  let J := (IsLinearModule.{u, v, v, v}
    (C := DeckOrbitSkeleton C G) k).ι
  let ePush : orbitSkeletonPushdown (G := G) (F.obj R).obj ≅
      orbitSkeletonPushdown (G := G) M.obj :=
    J.mapIso (Push.mapIso eExt)
  let hExt :=
    orbitSkeletonPushdown_moduleExtensionByZero_vanishesOnDeleted
      (k := k) D S hS R
  let eRest := moduleRestrictionToDeletionIso
    (k := k) (DeckOrbitSkeleton C G)
    (deckOrbitDeletedSet (G := G) S)
    (orbitSkeletonPushdown (G := G) (F.obj R).obj)
    (orbitSkeletonPushdown (G := G) M.obj)
    hExt hP ePush
  exact n ≪≫ Functor.isoWhiskerLeft
    (deckOrbitDeletionCommEquivalence (k := k) D S hS).functor eRest

end DeckSkeleton

end MagnitudeConjecture.ObjectDeletion
