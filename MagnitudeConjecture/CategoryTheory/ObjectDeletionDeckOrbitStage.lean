import MagnitudeConjecture.CategoryTheory.ObjectDeletionDeckOrbit
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteOrbit
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStages
import MagnitudeConjecture.CategoryTheory.ObjectDeletionOrbitStage

/-!
# Finite deletion stages on the deck-orbit skeleton

The downstairs model at stage `j` deletes from the fixed ambient deck-orbit
skeleton exactly the orbit classes represented by the first `j` subgroup
orbits upstairs.  The successor equation is literal: the next deleted set is
the previous set union the singleton image of the next chosen object.
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
variable (N : Subgroup G)

section FixedShift

variable [HasShift C (Additive N)]
variable [∀ a : Additive N, (shiftFunctor C a).Additive]
variable [∀ a : Additive N, (shiftFunctor C a).Linear k]

/-- The image in the subgroup deck-orbit skeleton of all objects deleted by
stage `j`. -/
def stageDeckDeletedSet {m : ℕ}
    (representative : Fin m → G) (x : C) (j : Fin (m + 1)) :
    Set (DeckOrbitSkeleton C N) :=
  deckOrbitDeletedSet (G := N) (stageDeletedSet N representative x j)

/-- The fixed-skeleton model of the downstairs category at stage `j`. -/
abbrev DownstairsStageCategory {m : ℕ}
    (representative : Fin m → G) (x : C) (j : Fin (m + 1)) :=
  DeletionCategory (k := k) (DeckOrbitSkeleton C N)
    (stageDeckDeletedSet N representative x j)

/-- The orbit class of the next chosen object. -/
def stageDeckObject {m : ℕ}
    (representative : Fin m → G) (x : C) (i : Fin m) :
    DeckOrbitSkeleton C N :=
  (Quotient.mk'' (representative i • x) :
    MulAction.orbitRel.Quotient N C)

/-- The image of the next full subgroup orbit is the singleton containing
the image of its chosen representative. -/
theorem deckOrbitDeletedSet_subgroupOrbit {m : ℕ}
    (representative : Fin m → G) (x : C) (i : Fin m) :
    deckOrbitDeletedSet (G := N)
        (subgroupOrbit N (representative i • x)) =
      {stageDeckObject N representative x i} := by
  exact deckOrbitDeletedSet_orbit (G := N)
    (representative i • x)

/-- Downstairs, the successor stage adjoins exactly the singleton image of
the next chosen object. -/
theorem stageDeckDeletedSet_succ {m : ℕ}
    (representative : Fin m → G) (x : C) (i : Fin m) :
    stageDeckDeletedSet N representative x i.succ =
      stageDeckDeletedSet N representative x i.castSucc ∪
        {stageDeckObject N representative x i} := by
  rw [stageDeckDeletedSet, stageDeletedSet_succ,
    deckOrbitDeletedSet_union,
    deckOrbitDeletedSet_subgroupOrbit]
  rfl

/-- The singleton object deleted from the current downstairs stage. -/
abbrev DownstairsStageAdditionalDeleted {m : ℕ}
    (representative : Fin m → G) (x : C) (i : Fin m) :=
  AdditionalDeleted (k := k) (DeckOrbitSkeleton C N)
    (stageDeckDeletedSet N representative x i.castSucc)
    {stageDeckObject N representative x i}

/-- Deleting the image of `gᵢx` from the current fixed-skeleton model gives
the next fixed-skeleton stage. -/
noncomputable def downstairsStageSuccEquivalence {m : ℕ}
    (representative : Fin m → G) (x : C) (i : Fin m) :
    IteratedDeletionCategory (k := k) (DeckOrbitSkeleton C N)
        (stageDeckDeletedSet N representative x i.castSucc)
        {stageDeckObject N representative x i} ≌
      DownstairsStageCategory (k := k) N representative x i.succ :=
  (iteratedDeletionEquivalence (k := k) (DeckOrbitSkeleton C N)
    (stageDeckDeletedSet N representative x i.castSucc)
    {stageDeckObject N representative x i}).trans
      (deletionEquivalenceOfEq (k := k) (DeckOrbitSkeleton C N)
        (stageDeckDeletedSet_succ N representative x i).symm)

noncomputable instance downstairsStageSuccEquivalence_functor_additive
    {m : ℕ} (representative : Fin m → G) (x : C) (i : Fin m) :
    (downstairsStageSuccEquivalence
      (k := k) N representative x i).functor.Additive := by
  let e₁ := iteratedDeletionEquivalence (k := k) (DeckOrbitSkeleton C N)
    (stageDeckDeletedSet N representative x i.castSucc)
    {stageDeckObject N representative x i}
  let e₂ := deletionEquivalenceOfEq (k := k) (DeckOrbitSkeleton C N)
    (stageDeckDeletedSet_succ N representative x i).symm
  letI : e₁.functor.Additive := inferInstance
  letI : e₂.functor.Additive := inferInstance
  change (e₁.functor ⋙ e₂.functor).Additive
  infer_instance

noncomputable instance downstairsStageSuccEquivalence_functor_linear
    {m : ℕ} (representative : Fin m → G) (x : C) (i : Fin m) :
    (downstairsStageSuccEquivalence
      (k := k) N representative x i).functor.Linear k := by
  let e₁ := iteratedDeletionEquivalence (k := k) (DeckOrbitSkeleton C N)
    (stageDeckDeletedSet N representative x i.castSucc)
    {stageDeckObject N representative x i}
  let e₂ := deletionEquivalenceOfEq (k := k) (DeckOrbitSkeleton C N)
    (stageDeckDeletedSet_succ N representative x i).symm
  letI : e₁.functor.Linear k := inferInstance
  letI : e₂.functor.Linear k := inferInstance
  change (e₁.functor ⋙ e₂.functor).Linear k
  infer_instance

end FixedShift

section StageComparison

variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

set_option backward.isDefEq.respectTransparency false in
/-- The actual deck-orbit skeleton of the upstairs stage is equivalent to the
fixed ambient skeleton with precisely the accumulated orbit classes deleted. -/
noncomputable def stageDeckOrbitEquivalence
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    DeckOrbitSkeleton (StageCategory (k := k) N representative x j) N ≌
      DownstairsStageCategory (k := k) N representative x j := by
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : ObjectProperty.IsClosedUnderIsomorphisms
      (stageDeletedSet N representative x j) :=
    isClosedUnderIsomorphisms_of_skeletal hC _
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
    (D.restrict N) (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)
  letI := rawHasShift (k := k) (stageDeletedSet N representative x j) hShift
  letI : ∀ a : Additive N,
      (shiftFunctor
        (RawCategory (k := k) C (stageDeletedSet N representative x j)) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI : ∀ a : Additive N,
      (shiftFunctor
        (RawCategory (k := k) C (stageDeletedSet N representative x j)) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI := deletionHasShift (k := k)
    (stageDeletedSet N representative x j) hShift
  letI : ∀ a : Additive N,
      (shiftFunctor (StageCategory (k := k) N representative x j) a).Additive :=
    fun a ↦ deletionShift_additive (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI : ∀ a : Additive N,
      (shiftFunctor (StageCategory (k := k) N representative x j) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  haveI : ∀ a : Additive N, (SD.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC N representative x j a
  haveI : ∀ a : Additive N, (SD.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC N representative x j a
  exact (SD.deckOrbitSkeletonEquivalence).trans
    ((stageDeletionOrbitEquivalence (k := k) D hC N representative x j).trans
      (CoherentDeckShift.deckOrbitDeletionEquivalence (k := k)
        (D.restrict N) (stageDeletedSet N representative x j)
        (stageDeletedSet_actionInvariant N representative x j)).symm)

/-- The literal map from an orbit class in a deletion stage to the same
surviving orbit class in the fixed ambient deck skeleton. -/
noncomputable def stageDeckOrbitObjectMap
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    DeckOrbitSkeleton (StageCategory (k := k) N representative x j) N →
      DownstairsStageCategory (k := k) N representative x j := by
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  let S := stageDeletedSet N representative x j
  let hS := stageDeletedSet_actionInvariant N representative x j
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  refine fun q ↦ ⟨(rawFunctor (k := k) (DeckOrbitSkeleton C N)
    (stageDeckDeletedSet N representative x j)).obj
      (deletionOrbitQuotientToAmbient (k := k) C S hS q), ?_⟩
  intro hq
  change deckOrbitRepresentative (C := C) (G := N)
      (deletionOrbitQuotientToAmbient (k := k) C S hS q) ∈ S at hq
  induction q using Quotient.inductionOn' with
  | _ X =>
      change deckOrbitRepresentative (C := C) (G := N)
          (Quotient.mk'' X.obj.as : MulAction.orbitRel.Quotient N C) ∈ S at hq
      obtain ⟨g, hg⟩ := deckOrbitRepresentative_mk_mem_orbit
        (C := C) (G := N) X.obj.as
      rw [← hg] at hq
      exact X.property ((hS g X.obj.as).1 hq)

/-- The canonical orbit-class map at a deletion stage is injective. -/
theorem stageDeckOrbitObjectMap_injective
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    Function.Injective
      (stageDeckOrbitObjectMap
        (k := k) N D hC representative x j) := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  let S := stageDeletedSet N representative x j
  let hS := stageDeletedSet_actionInvariant N representative x j
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  intro q r hqr
  apply deletionOrbitQuotientToAmbient_injective (k := k) C S hS
  have hamb := congrArg (fun Y : DownstairsStageCategory
    (k := k) N representative x j ↦ Y.obj.as) hqr
  change deletionOrbitQuotientToAmbient (k := k) C S hS q =
    deletionOrbitQuotientToAmbient (k := k) C S hS r at hamb
  exact hamb

/-- Every surviving fixed ambient orbit class comes from the corresponding
orbit class in the literal deletion stage. -/
theorem stageDeckOrbitObjectMap_surjective
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    Function.Surjective
      (stageDeckOrbitObjectMap
        (k := k) N D hC representative x j) := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  let S := stageDeletedSet N representative x j
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  intro Y
  let U := deckOrbitRepresentative (C := C) (G := N) Y.obj.as
  have hU : U ∉ S := Y.property
  let X : StageCategory (k := k) N representative x j :=
    ⟨(rawFunctor (k := k) C S).obj U, hU⟩
  refine ⟨(Quotient.mk'' X : MulAction.orbitRel.Quotient N
    (StageCategory (k := k) N representative x j)), ?_⟩
  unfold stageDeckOrbitObjectMap
  apply ObjectProperty.FullSubcategory.ext
  apply CategoryTheory.Quotient.ext
  exact deckOrbitRepresentative_mk (C := C) (G := N) Y.obj.as

/-- Literal object coordinates for the equivalence between an actual
deletion-stage orbit skeleton and its fixed ambient model. -/
noncomputable def stageDeckOrbitObjectEquiv
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    DeckOrbitSkeleton (StageCategory (k := k) N representative x j) N ≃
      DownstairsStageCategory (k := k) N representative x j :=
  Equiv.ofBijective
    (stageDeckOrbitObjectMap (k := k) N D hC representative x j)
    ⟨stageDeckOrbitObjectMap_injective
        (k := k) N D hC representative x j,
      stageDeckOrbitObjectMap_surjective
        (k := k) N D hC representative x j⟩

set_option backward.isDefEq.respectTransparency false in
/-- The existing stage equivalence sends each orbit class to an object
isomorphic to its canonical fixed-ambient orbit-class coordinate. -/
noncomputable def stageDeckOrbitEquivalence_objIso
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    ∀ q : DeckOrbitSkeleton
        (StageCategory (k := k) N representative x j) N,
      (stageDeckOrbitEquivalence
          (k := k) N D hC representative x j).functor.obj q ≅
        stageDeckOrbitObjectMap
          (k := k) N D hC representative x j q := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  let S := stageDeletedSet N representative x j
  let hS := stageDeletedSet_actionInvariant N representative x j
  letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
    isClosedUnderIsomorphisms_of_skeletal hC _
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
    (D.restrict N) S hS
  letI := rawHasShift (k := k) S hShift
  letI : ∀ a : Additive N,
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
  letI : ∀ a : Additive N,
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
  letI := deletionHasShift (k := k) S hShift
  letI : ∀ a : Additive N,
      (shiftFunctor (StageCategory (k := k) N representative x j) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hShift a
  letI : ∀ a : Additive N,
      (shiftFunctor (StageCategory (k := k) N representative x j) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hShift a
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  haveI : ∀ a : Additive N, (SD.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC N representative x j a
  haveI : ∀ a : Additive N, (SD.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC N representative x j a
  let e₁ := SD.deckOrbitSkeletonEquivalence
  let e₂ := stageDeletionOrbitEquivalence
    (k := k) D hC N representative x j
  let eDel := CoherentDeckShift.deckOrbitDeletionEquivalence (k := k)
    (D.restrict N) S hS
  intro q
  let A := e₂.functor.obj (e₁.functor.obj q)
  let Phi := stageDeckOrbitObjectMap
    (k := k) N D hC representative x j q
  have hA : A ≅ eDel.functor.obj Phi := by
    let U : C := (show StageCategory (k := k) N representative x j from
      e₁.functor.obj q).obj.as
    have hOrbit :
        (Quotient.mk'' U : MulAction.orbitRel.Quotient N C) = Phi.obj.as := by
      change deletionOrbitQuotientToAmbient (k := k) C S hS
          (Quotient.mk'' (show StageCategory (k := k) N representative x j from
            e₁.functor.obj q)) =
        deletionOrbitQuotientToAmbient (k := k) C S hS q
      exact congrArg (deletionOrbitQuotientToAmbient (k := k) C S hS)
        (deckOrbitRepresentative_mk
          (C := StageCategory (k := k) N representative x j) (G := N) q)
    let eU := (D.restrict N).objectIsoDeckOrbitRepresentative U
    let eRep := (ShiftOrbitCategory.identityComponentFunctor
      (C := C) (A := Additive N)).mapIso
      (eqToIso (congrArg
        (deckOrbitRepresentative (C := C) (G := N)) hOrbit))
    let eShift := eU ≪≫ eRep
    let eOD := orbitDeletionToSurvivingRawOrbitEquivalence
      (k := k) S hShift
    let eInc := deletionShiftOrbitInclusionEquivalence
      (k := k) S hShift
    let P : DeletionCategory (k := k)
        (ShiftOrbitCategory C (Additive N)) S :=
      ⟨(rawFunctor (k := k)
          (ShiftOrbitCategory C (Additive N)) S).obj U,
        (show StageCategory (k := k) N representative x j from
          e₁.functor.obj q).property⟩
    have hB : eInc.functor.obj (e₁.functor.obj q) =
        eOD.functor.obj P := rfl
    have hAP : A ≅ P := by
      change eOD.inverse.obj (eInc.functor.obj (e₁.functor.obj q)) ≅ P
      exact eOD.inverse.mapIso (eqToIso hB) ≪≫
        (eOD.unitIso.app P).symm
    have hP : P ≅ eDel.functor.obj Phi := by
      dsimp [P, eDel,
        CoherentDeckShift.deckOrbitDeletionEquivalence]
      change (⟨(rawFunctor (k := k)
            (ShiftOrbitCategory C (Additive N)) S).obj U, _⟩ :
          DeletionCategory (k := k)
            (ShiftOrbitCategory C (Additive N)) S) ≅
        ⟨(rawFunctor (k := k)
            (ShiftOrbitCategory C (Additive N)) S).obj
          (deckOrbitRepresentative (C := C) (G := N) Phi.obj.as), _⟩
      exact ObjectProperty.isoMk _
        ((rawFunctor (k := k)
          (ShiftOrbitCategory C (Additive N)) S).mapIso eShift)
    exact hAP ≪≫ hP
  change eDel.inverse.obj A ≅ Phi
  exact eDel.inverse.mapIso hA ≪≫ (eDel.unitIso.app Phi).symm

set_option backward.isDefEq.respectTransparency false in
noncomputable instance stageDeckOrbitEquivalence_functor_additive
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    (stageDeckOrbitEquivalence
      (k := k) N D hC representative x j).functor.Additive := by
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
  letI := rawHasShift (k := k) (stageDeletedSet N representative x j) hShift
  letI : ∀ a : Additive N,
      (shiftFunctor
        (RawCategory (k := k) C (stageDeletedSet N representative x j)) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI : ∀ a : Additive N,
      (shiftFunctor
        (RawCategory (k := k) C (stageDeletedSet N representative x j)) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI := deletionHasShift (k := k)
    (stageDeletedSet N representative x j) hShift
  letI : ∀ a : Additive N,
      (shiftFunctor (StageCategory (k := k) N representative x j) a).Additive :=
    fun a ↦ deletionShift_additive (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI : ∀ a : Additive N,
      (shiftFunctor (StageCategory (k := k) N representative x j) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  haveI : ∀ a : Additive N, (SD.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC N representative x j a
  haveI : ∀ a : Additive N, (SD.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC N representative x j a
  let e₁ := SD.deckOrbitSkeletonEquivalence
  let e₂ := stageDeletionOrbitEquivalence
    (k := k) D hC N representative x j
  let eDel := CoherentDeckShift.deckOrbitDeletionEquivalence (k := k)
    (D.restrict N) (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)
  let e₃ := eDel.symm
  letI : e₁.functor.Additive :=
    CoherentDeckShift.deckOrbitSkeletonEquivalence_functor_additive SD
  letI : e₂.functor.Additive :=
    stageDeletionOrbitEquivalence_functor_additive
      (k := k) D hC N representative x j
  letI : eDel.functor.Additive :=
    CoherentDeckShift.deckOrbitDeletionEquivalence_functor_additive
      (k := k) (D.restrict N) (stageDeletedSet N representative x j)
        (stageDeletedSet_actionInvariant N representative x j)
  letI : e₃.functor.Additive := by
    change eDel.inverse.Additive
    infer_instance
  constructor
  intro X Y f g
  change e₃.functor.map (e₂.functor.map (e₁.functor.map (f + g))) = _
  rw [e₁.functor.map_add, e₂.functor.map_add, e₃.functor.map_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
noncomputable instance stageDeckOrbitEquivalence_functor_linear
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    (stageDeckOrbitEquivalence
      (k := k) N D hC representative x j).functor.Linear k := by
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
  letI := rawHasShift (k := k) (stageDeletedSet N representative x j) hShift
  letI : ∀ a : Additive N,
      (shiftFunctor
        (RawCategory (k := k) C (stageDeletedSet N representative x j)) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI : ∀ a : Additive N,
      (shiftFunctor
        (RawCategory (k := k) C (stageDeletedSet N representative x j)) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI := deletionHasShift (k := k)
    (stageDeletedSet N representative x j) hShift
  letI : ∀ a : Additive N,
      (shiftFunctor (StageCategory (k := k) N representative x j) a).Additive :=
    fun a ↦ deletionShift_additive (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI : ∀ a : Additive N,
      (shiftFunctor (StageCategory (k := k) N representative x j) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k)
      (stageDeletedSet N representative x j) hShift a
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  haveI : ∀ a : Additive N, (SD.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC N representative x j a
  haveI : ∀ a : Additive N, (SD.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC N representative x j a
  let e₁ := SD.deckOrbitSkeletonEquivalence
  let e₂ := stageDeletionOrbitEquivalence
    (k := k) D hC N representative x j
  let eDel := CoherentDeckShift.deckOrbitDeletionEquivalence (k := k)
    (D.restrict N) (stageDeletedSet N representative x j)
    (stageDeletedSet_actionInvariant N representative x j)
  let e₃ := eDel.symm
  letI : e₁.functor.Linear k :=
    CoherentDeckShift.deckOrbitSkeletonEquivalence_functor_linear SD
  letI : e₂.functor.Linear k :=
    stageDeletionOrbitEquivalence_functor_linear
      (k := k) D hC N representative x j
  letI : eDel.functor.Linear k :=
    CoherentDeckShift.deckOrbitDeletionEquivalence_functor_linear
      (k := k) (D.restrict N) (stageDeletedSet N representative x j)
        (stageDeletedSet_actionInvariant N representative x j)
  letI : e₃.functor.Linear k := by
    change eDel.inverse.Linear k
    infer_instance
  constructor
  intro X Y f r
  change e₃.functor.map (e₂.functor.map (e₁.functor.map (r • f))) = _
  rw [e₁.functor.map_smul, e₂.functor.map_smul, e₃.functor.map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A stage comparison functor whose object map is literally the canonical
orbit-class bijection. -/
noncomputable def stageDeckOrbitNormalizedFunctor
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    DeckOrbitSkeleton (StageCategory (k := k) N representative x j) N ⥤
      DownstairsStageCategory (k := k) N representative x j := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  let E := stageDeckOrbitEquivalence
    (k := k) N D hC representative x j
  let ι := stageDeckOrbitEquivalence_objIso
    (k := k) N D hC representative x j
  exact
    { obj := stageDeckOrbitObjectMap
        (k := k) N D hC representative x j
      map := fun {q r} f ↦ (ι q).inv ≫ E.functor.map f ≫ (ι r).hom
      map_id := by
        intro q
        rw [E.functor.map_id, Category.id_comp]
        change (ι q).inv ≫ (ι q).hom = _
        exact (ι q).inv_hom_id
      map_comp := by
        intro q r s f g
        simp [Category.assoc] }

set_option backward.isDefEq.respectTransparency false in
/-- The normalized stage functor is naturally isomorphic to the original
comparison equivalence. -/
noncomputable def stageDeckOrbitEquivalenceFunctorIso
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    (stageDeckOrbitEquivalence
      (k := k) N D hC representative x j).functor ≅
      stageDeckOrbitNormalizedFunctor
        (k := k) N D hC representative x j := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  let ι := stageDeckOrbitEquivalence_objIso
    (k := k) N D hC representative x j
  exact NatIso.ofComponents ι (by
    intro q r f
    dsimp [stageDeckOrbitNormalizedFunctor, ι]
    simp)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance stageDeckOrbitNormalizedFunctor_additive
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    (stageDeckOrbitNormalizedFunctor
      (k := k) N D hC representative x j).Additive := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  let E := stageDeckOrbitEquivalence
    (k := k) N D hC representative x j
  letI : E.functor.Additive :=
    stageDeckOrbitEquivalence_functor_additive
      (k := k) N D hC representative x j
  exact Functor.additive_of_iso
    (stageDeckOrbitEquivalenceFunctorIso
      (k := k) N D hC representative x j)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance stageDeckOrbitNormalizedFunctor_linear
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    (stageDeckOrbitNormalizedFunctor
      (k := k) N D hC representative x j).Linear k := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  let E := stageDeckOrbitEquivalence
    (k := k) N D hC representative x j
  letI : E.functor.Linear k :=
    stageDeckOrbitEquivalence_functor_linear
      (k := k) N D hC representative x j
  exact Functor.linear_of_iso k
    (stageDeckOrbitEquivalenceFunctorIso
      (k := k) N D hC representative x j)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance stageDeckOrbitNormalizedFunctor_isEquivalence
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    (stageDeckOrbitNormalizedFunctor
      (k := k) N D hC representative x j).IsEquivalence := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  let E := stageDeckOrbitEquivalence
    (k := k) N D hC representative x j
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  exact Functor.isEquivalence_of_iso
    (stageDeckOrbitEquivalenceFunctorIso
      (k := k) N D hC representative x j)

set_option backward.isDefEq.respectTransparency false in
/-- The stage equivalence normalized to use the literal orbit-class object
bijection as its forward object map. -/
noncomputable def stageDeckOrbitNormalizedEquivalence
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    DeckOrbitSkeleton (StageCategory (k := k) N representative x j) N ≌
      DownstairsStageCategory (k := k) N representative x j := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  exact (stageDeckOrbitNormalizedFunctor
    (k := k) N D hC representative x j).asEquivalence

/-- The normalized stage equivalence is literally bijective on objects. -/
theorem stageDeckOrbitNormalizedEquivalence_obj_bijective
    (hC : Skeletal C) {m : ℕ} (representative : Fin m → G)
    (x : C) (j : Fin (m + 1)) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x j
    let SD := stageCoherentDeckShift (k := k) D hC N representative x j
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    Function.Bijective
      (stageDeckOrbitNormalizedEquivalence
        (k := k) N D hC representative x j).functor.obj := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := stageMulAction (k := k) N representative x j
  let SD := stageCoherentDeckShift (k := k) D hC N representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  exact ⟨stageDeckOrbitObjectMap_injective
      (k := k) N D hC representative x j,
    stageDeckOrbitObjectMap_surjective
      (k := k) N D hC representative x j⟩

end StageComparison

end MagnitudeConjecture.ObjectDeletion
