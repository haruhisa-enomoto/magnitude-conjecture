import MagnitudeConjecture.CategoryTheory.ObjectDeletionOrbit
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStage

/-!
# Orbit categories of finite object-deletion stages

This file specializes the orbit/deletion comparison to the intermediate
subgroup-orbit deletion categories in the covering telescope.  It is the
categorical form of the manuscript assertion that passing a deletion stage
downstairs is the same as deleting its image in the subgroup orbit category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v w z

variable {k : Type z} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type w} [Group G] [MulAction G C]

set_option backward.isDefEq.respectTransparency false in
/-- At every finite deletion stage, taking the subgroup shift-orbit category
commutes with deleting the accumulated subgroup-invariant object set. -/
noncomputable def stageDeletionOrbitEquivalence
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : ObjectProperty.IsClosedUnderIsomorphisms
        (stageDeletedSet N representative x j) :=
      isClosedUnderIsomorphisms_of_skeletal hC _
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
      (D.restrict N) (stageDeletedSet N representative x j)
      (stageDeletedSet_actionInvariant N representative x j)
    letI := deletionHasShift (k := k)
      (stageDeletedSet N representative x j) hShift
    letI : ∀ a : Additive N,
        (shiftFunctor
          (StageCategory (k := k) N representative x j) a).Additive :=
      fun a ↦ deletionShift_additive (k := k)
        (stageDeletedSet N representative x j) hShift a
    ShiftOrbitCategory
        (StageCategory (k := k) N representative x j) (Additive N) ≌
      DeletionCategory (k := k)
        (ShiftOrbitCategory C (Additive N))
        (stageDeletedSet N representative x j : Set C) := by
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (stageDeletedSet N representative x j) :=
    isClosedUnderIsomorphisms_of_skeletal hC _
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
    (D.restrict N) (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)
  exact deletionOrbitEquivalence (k := k)
    (stageDeletedSet N representative x j) hShift

noncomputable instance stageDeletionOrbitEquivalence_functor_additive
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : ObjectProperty.IsClosedUnderIsomorphisms
        (stageDeletedSet N representative x j) :=
      isClosedUnderIsomorphisms_of_skeletal hC _
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
      (D.restrict N) (stageDeletedSet N representative x j)
      (stageDeletedSet_actionInvariant N representative x j)
    letI := deletionHasShift (k := k)
      (stageDeletedSet N representative x j) hShift
    letI : ∀ a : Additive N,
        (shiftFunctor
          (StageCategory (k := k) N representative x j) a).Additive :=
      fun a ↦ deletionShift_additive (k := k)
        (stageDeletedSet N representative x j) hShift a
    (stageDeletionOrbitEquivalence
      (k := k) D hC N representative x j).functor.Additive := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (stageDeletedSet N representative x j) :=
    isClosedUnderIsomorphisms_of_skeletal hC _
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
    (D.restrict N) (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)
  letI := deletionHasShift (k := k)
    (stageDeletedSet N representative x j) hShift
  letI : ∀ a : Additive N,
      (shiftFunctor
        (StageCategory (k := k) N representative x j) a).Additive :=
    fun a ↦ deletionShift_additive (k := k)
      (stageDeletedSet N representative x j) hShift a
  change (deletionOrbitEquivalence (k := k)
    (stageDeletedSet N representative x j) hShift).functor.Additive
  infer_instance

noncomputable instance stageDeletionOrbitEquivalence_functor_linear
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) {m : ℕ} (N : Subgroup G)
    (representative : Fin m → G) (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : ObjectProperty.IsClosedUnderIsomorphisms
        (stageDeletedSet N representative x j) :=
      isClosedUnderIsomorphisms_of_skeletal hC _
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
      (D.restrict N) (stageDeletedSet N representative x j)
      (stageDeletedSet_actionInvariant N representative x j)
    letI := deletionHasShift (k := k)
      (stageDeletedSet N representative x j) hShift
    letI : ∀ a : Additive N,
        (shiftFunctor
          (StageCategory (k := k) N representative x j) a).Additive :=
      fun a ↦ deletionShift_additive (k := k)
        (stageDeletedSet N representative x j) hShift a
    letI : ∀ a : Additive N,
        (shiftFunctor
          (StageCategory (k := k) N representative x j) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k)
        (stageDeletedSet N representative x j) hShift a
    (stageDeletionOrbitEquivalence
      (k := k) D hC N representative x j).functor.Linear k := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (stageDeletedSet N representative x j) :=
    isClosedUnderIsomorphisms_of_skeletal hC _
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
    (D.restrict N) (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)
  letI := deletionHasShift (k := k)
    (stageDeletedSet N representative x j) hShift
  letI : ∀ a : Additive N,
      (shiftFunctor
        (StageCategory (k := k) N representative x j) a).Additive :=
    fun a ↦ deletionShift_additive (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI : ∀ a : Additive N,
      (shiftFunctor
        (StageCategory (k := k) N representative x j) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k)
      (stageDeletedSet N representative x j) hShift a
  change (deletionOrbitEquivalence (k := k)
    (stageDeletedSet N representative x j) hShift).functor.Linear k
  infer_instance

end MagnitudeConjecture.ObjectDeletion
