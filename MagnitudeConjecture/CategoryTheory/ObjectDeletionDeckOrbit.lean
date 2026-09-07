import MagnitudeConjecture.CategoryTheory.DeckOrbitSkeleton
import MagnitudeConjecture.CategoryTheory.ObjectDeletionOrbit

/-!
# Object deletion on the chosen deck-orbit skeleton

For a deck-invariant set of upstairs objects, this file compares deletion
after replacing the shift-orbit category by its one-representative-per-orbit
skeleton.  On the skeleton the deleted objects are literal orbit classes.
In particular, one full deck orbit becomes one singleton object, which is the
form used by the covering-average argument in the manuscript.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution.CategoricalIdeal

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v w z

variable {k : Type z} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type w} [Group G] [MulAction G C]

omit [Category.{v} C] [Preadditive C] in
/-- The chosen representative of the orbit class of `X` lies in the literal
deck orbit of `X`. -/
theorem deckOrbitRepresentative_mk_mem_orbit (X : C) :
    deckOrbitRepresentative (C := C) (G := G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C) ∈
      MulAction.orbit G X := by
  apply MulAction.orbitRel_apply.mp
  apply Quotient.exact
  exact deckOrbitRepresentative_mk (C := C) (G := G)
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)

section DeletedSet

variable [HasShift C (Additive G)]
variable [∀ a : Additive G, (shiftFunctor C a).Additive]
variable [∀ a : Additive G, (shiftFunctor C a).Linear k]

/-- The deck-orbit classes whose chosen representatives belong to `S`. -/
def deckOrbitDeletedSet (S : Set C) : Set (DeckOrbitSkeleton C G) :=
  fun q ↦ deckOrbitRepresentative (C := C) (G := G) q ∈ S

@[simp]
theorem mem_deckOrbitDeletedSet_iff (S : Set C) (q : DeckOrbitSkeleton C G) :
    q ∈ deckOrbitDeletedSet (G := G) S ↔
      deckOrbitRepresentative (C := C) (G := G) q ∈ S :=
  Iff.rfl

/-- A full literal deck orbit becomes one deleted object in the chosen orbit
skeleton. -/
theorem deckOrbitDeletedSet_orbit (X : C) :
    deckOrbitDeletedSet (G := G) (MulAction.orbit G X) =
      {(Quotient.mk'' X : MulAction.orbitRel.Quotient G C)} := by
  ext q
  constructor
  · intro hq
    change deckOrbitRepresentative (C := C) (G := G) q ∈
      MulAction.orbit G X at hq
    have hrel := MulAction.orbitRel_apply.mpr hq
    have heq :
        (Quotient.mk'' (deckOrbitRepresentative (C := C) (G := G) q) :
          MulAction.orbitRel.Quotient G C) = Quotient.mk'' X :=
      Quotient.sound hrel
    show q = (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
    exact (deckOrbitRepresentative_mk (C := C) (G := G) q).symm.trans heq
  · intro hq
    have heq : q =
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C) := by
      exact hq
    subst q
    exact deckOrbitRepresentative_mk_mem_orbit (G := G) X

@[simp]
theorem deckOrbitDeletedSet_union (S T : Set C) :
    deckOrbitDeletedSet (G := G) (S ∪ T) =
      deckOrbitDeletedSet (G := G) S ∪
        deckOrbitDeletedSet (G := G) T := by
  rfl

end DeletedSet

omit [Category.{v} C] [Preadditive C] in
/-- The chosen representative of the orbit of an object in an invariant set
still belongs to that set. -/
theorem deckOrbitRepresentative_mem_of_mem (S : Set C)
    (hS : ActionInvariant (G := G) S) {X : C} (hX : X ∈ S) :
    deckOrbitRepresentative (C := C) (G := G)
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C) ∈ S := by
  obtain ⟨g, hg⟩ := deckOrbitRepresentative_mk_mem_orbit (G := G) X
  rw [← hg]
  exact (hS g X).2 hX

namespace CoherentDeckShift

variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]
variable (S : Set C)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to chosen orbit representatives reflects membership in the
object-deletion ideal. -/
theorem mem_deckOrbitIdeal_of_representative_mem_ideal
    (hS : ActionInvariant (G := G) S) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ∀ {q r : DeckOrbitSkeleton C G} (f : q ⟶ r),
      (deckOrbitRepresentativeFunctor (C := C) (G := G)).map f ∈
          (ideal (k := k) (ShiftOrbitCategory C (Additive G)) S).hom
            ((deckOrbitRepresentativeFunctor (C := C) (G := G)).obj q)
            ((deckOrbitRepresentativeFunctor (C := C) (G := G)).obj r) →
        f ∈ (ideal (k := k) (DeckOrbitSkeleton C G)
          (deckOrbitDeletedSet (G := G) S)).hom q r := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  intro q r f hf
  let E := InducedCategory.homLinearEquiv (R := k)
    (X := q) (Y := r)
  rw [← E.symm_apply_apply f]
  refine Submodule.span_induction
    (p := fun t _ ↦ E.symm t ∈
      (ideal (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S)).hom q r) ?_ ?_ ?_ ?_ hf
  · intro t ht
    rcases ht with ⟨U, V, s, hs, a, b, rfl⟩
    rcases hs with ⟨rfl, hU⟩
    let qU : DeckOrbitSkeleton C G :=
      (Quotient.mk'' U : MulAction.orbitRel.Quotient G C)
    let e :
        (show ShiftOrbitCategory C (Additive G) from U) ≅
          (deckOrbitRepresentativeFunctor (C := C) (G := G)).obj qU :=
      D.objectIsoDeckOrbitRepresentative U
    let a' : q ⟶ qU := InducedCategory.homMk (a ≫ e.hom)
    let b' : qU ⟶ r := InducedCategory.homMk (e.inv ≫ s ≫ b)
    have hqU : qU ∈ deckOrbitDeletedSet (G := G) S :=
      deckOrbitRepresentative_mem_of_mem S hS hU
    have hcomp := comp_mem_ideal (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S) hqU a' b'
    convert hcomp using 1
    apply InducedCategory.hom_ext
    simp [E, a', b', e]
  ·
    simp
  · intro p t hp ht ihp iht
    simpa using
      ((ideal (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S)).hom _ _).add_mem ihp iht
  · intro c t ht iht
    simpa using
      (ideal (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S)).smul_mem c iht

set_option backward.isDefEq.respectTransparency false in
/-- Chosen representatives followed by the raw ambient deletion quotient. -/
noncomputable def deckOrbitToRawDeletionFunctor :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    DeckOrbitSkeleton C G ⥤
      RawCategory (k := k) (ShiftOrbitCategory C (Additive G)) S := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact deckOrbitRepresentativeFunctor (C := C) (G := G) ⋙
    rawFunctor (k := k) (ShiftOrbitCategory C (Additive G)) S

noncomputable instance deckOrbitToRawDeletionFunctor_additive :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (deckOrbitToRawDeletionFunctor (k := k) D S).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only [deckOrbitToRawDeletionFunctor]
  infer_instance

noncomputable instance deckOrbitToRawDeletionFunctor_linear :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (deckOrbitToRawDeletionFunctor (k := k) D S).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only [deckOrbitToRawDeletionFunctor]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The representative functor followed by ambient deletion kills precisely
the skeleton objects represented by the invariant deleted set. -/
theorem deckOrbitToRawDeletionFunctor_isKilledBy :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (ideal (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S)).IsKilledBy
        (deckOrbitToRawDeletionFunctor (k := k) D S) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  intro X Y f hf
  change f ∈ HomIdeal.generatedHomSubmodule k
    (endomorphismRelations (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S)) X Y at hf
  induction hf using Submodule.span_induction with
  | mem t ht =>
      rcases ht with ⟨U, V, s, hs, a, b, rfl⟩
      rcases hs with ⟨rfl, hU⟩
      rw [Functor.map_comp, Functor.map_comp]
      have hzero := rawFunctor_obj_isZero (k := k)
        (ShiftOrbitCategory C (Additive G)) S hU
      have hszero :
          (deckOrbitToRawDeletionFunctor (k := k) D S).map s = 0 :=
        hzero.eq_of_src _ _
      rw [hszero]
      simp
  | zero =>
      exact (deckOrbitToRawDeletionFunctor (k := k) D S).map_zero X Y
  | add p q hp hq ihp ihq =>
      rw [(deckOrbitToRawDeletionFunctor (k := k) D S).map_add, ihp, ihq,
        add_zero]
  | smul c t ht iht =>
      rw [(deckOrbitToRawDeletionFunctor (k := k) D S).map_smul, iht,
        smul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The raw quotient comparison from deletion on the chosen orbit skeleton to
deletion on the nonskeletal orbit category. -/
noncomputable def rawDeckOrbitDeletionComparisonFunctor :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    RawCategory (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S) ⥤
      RawCategory (k := k) (ShiftOrbitCategory C (Additive G)) S := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact (ideal (k := k) (DeckOrbitSkeleton C G)
    (deckOrbitDeletedSet (G := G) S)).quotientLift
      (deckOrbitToRawDeletionFunctor (k := k) D S)
      (deckOrbitToRawDeletionFunctor_isKilledBy (k := k) D S)

noncomputable instance rawDeckOrbitDeletionComparisonFunctor_additive :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (rawDeckOrbitDeletionComparisonFunctor (k := k) D S).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact HomIdeal.quotientLift_additive
    (ideal (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S))
    (deckOrbitToRawDeletionFunctor (k := k) D S)
    (deckOrbitToRawDeletionFunctor_isKilledBy (k := k) D S)

noncomputable instance rawDeckOrbitDeletionComparisonFunctor_linear :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (rawDeckOrbitDeletionComparisonFunctor (k := k) D S).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact HomIdeal.quotientLift_linear
    (ideal (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S))
    (deckOrbitToRawDeletionFunctor (k := k) D S)
    (deckOrbitToRawDeletionFunctor_isKilledBy (k := k) D S)

set_option backward.isDefEq.respectTransparency false in
/-- The raw skeleton/ambient deletion comparison is full. -/
theorem rawDeckOrbitDeletionComparisonFunctor_full :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (rawDeckOrbitDeletionComparisonFunctor (k := k) D S).Full := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := deckOrbitToRawDeletionFunctor (k := k) D S
  haveI : F.Full := by
    dsimp [F, deckOrbitToRawDeletionFunctor]
    infer_instance
  exact HomIdeal.quotientLift_full
    (ideal (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S)) F
    (deckOrbitToRawDeletionFunctor_isKilledBy (k := k) D S)

set_option backward.isDefEq.respectTransparency false in
/-- The raw skeleton/ambient deletion comparison is faithful. -/
theorem rawDeckOrbitDeletionComparisonFunctor_faithful :
    ActionInvariant (G := G) S →
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (rawDeckOrbitDeletionComparisonFunctor (k := k) D S).Faithful := by
  intro hS
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := deckOrbitToRawDeletionFunctor (k := k) D S
  apply HomIdeal.quotientLift_faithful
    (ideal (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S)) F
    (deckOrbitToRawDeletionFunctor_isKilledBy (k := k) D S)
  intro X Y f hzero
  apply mem_deckOrbitIdeal_of_representative_mem_ideal (k := k) D S hS f
  exact ((ideal (k := k) (ShiftOrbitCategory C (Additive G)) S).map_eq_zero_iff
      ((deckOrbitRepresentativeFunctor (C := C) (G := G)).map f)).1 hzero

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the raw comparison to the surviving objects. -/
noncomputable def deckOrbitDeletionComparisonFunctor :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    DeletionCategory (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S) ⥤
      DeletionCategory (k := k) (ShiftOrbitCategory C (Additive G)) S := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let P := IsSurvivingRaw (k := k) (DeckOrbitSkeleton C G)
    (deckOrbitDeletedSet (G := G) S)
  let Q := IsSurvivingRaw (k := k) (ShiftOrbitCategory C (Additive G)) S
  exact ObjectProperty.lift Q
    (P.ι ⋙ rawDeckOrbitDeletionComparisonFunctor (k := k) D S)
    (fun X ↦ by
      change deckOrbitRepresentative (C := C) (G := G) X.obj.as ∉ S
      exact X.property)

noncomputable instance deckOrbitDeletionComparisonFunctor_additive :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (deckOrbitDeletionComparisonFunctor (k := k) D S).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only [deckOrbitDeletionComparisonFunctor]
  infer_instance

noncomputable instance deckOrbitDeletionComparisonFunctor_linear :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (deckOrbitDeletionComparisonFunctor (k := k) D S).Linear k where
  map_smul := by
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    intro X Y f r
    apply ObjectProperty.hom_ext
    exact (rawDeckOrbitDeletionComparisonFunctor
      (k := k) D S).map_smul r f.hom

set_option backward.isDefEq.respectTransparency false in
theorem deckOrbitDeletionComparisonFunctor_full :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (deckOrbitDeletionComparisonFunctor (k := k) D S).Full := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : (rawDeckOrbitDeletionComparisonFunctor (k := k) D S).Full :=
    rawDeckOrbitDeletionComparisonFunctor_full (k := k) D S
  dsimp only [deckOrbitDeletionComparisonFunctor]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem deckOrbitDeletionComparisonFunctor_faithful :
    ActionInvariant (G := G) S →
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (deckOrbitDeletionComparisonFunctor (k := k) D S).Faithful := by
  intro hS
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : (rawDeckOrbitDeletionComparisonFunctor (k := k) D S).Faithful :=
    rawDeckOrbitDeletionComparisonFunctor_faithful (k := k) D S hS
  dsimp only [deckOrbitDeletionComparisonFunctor]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Every surviving ambient orbit object is isomorphic after deletion to its
chosen surviving orbit representative. -/
theorem deckOrbitDeletionComparisonFunctor_essSurj :
    ActionInvariant (G := G) S →
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (deckOrbitDeletionComparisonFunctor (k := k) D S).EssSurj := by
  intro hS
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  constructor
  intro Y
  let U : C := Y.obj.as
  let q : DeckOrbitSkeleton C G :=
    (Quotient.mk'' U : MulAction.orbitRel.Quotient G C)
  have hq : q ∉ deckOrbitDeletedSet (G := G) S := by
    intro hrep
    obtain ⟨g, hg⟩ := deckOrbitRepresentative_mk_mem_orbit
      (C := C) (G := G) U
    have hrep' : deckOrbitRepresentative (C := C) (G := G)
        (Quotient.mk'' U : MulAction.orbitRel.Quotient G C) ∈ S := by
      simpa [q] using hrep
    rw [← hg] at hrep'
    exact Y.property ((hS g U).1 hrep')
  let X : DeletionCategory (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S) :=
    ⟨(rawFunctor (k := k) (DeckOrbitSkeleton C G)
      (deckOrbitDeletedSet (G := G) S)).obj q, hq⟩
  refine ⟨X, ?_⟩
  let e := (D.objectIsoDeckOrbitRepresentative U).symm
  exact ⟨ObjectProperty.isoMk _
    ((rawFunctor (k := k) (ShiftOrbitCategory C (Additive G)) S).mapIso e)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Deleting an invariant upstairs set on the one-object-per-orbit skeleton
is equivalent to deleting that set in the nonskeletal shift-orbit category. -/
noncomputable def deckOrbitDeletionEquivalence :
    ActionInvariant (G := G) S →
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    DeletionCategory (k := k) (DeckOrbitSkeleton C G)
        (deckOrbitDeletedSet (G := G) S) ≌
      DeletionCategory (k := k) (ShiftOrbitCategory C (Additive G)) S := by
  intro hS
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := deckOrbitDeletionComparisonFunctor (k := k) D S
  letI : F.Full := deckOrbitDeletionComparisonFunctor_full (k := k) D S
  letI : F.Faithful :=
    deckOrbitDeletionComparisonFunctor_faithful (k := k) D S hS
  letI : F.EssSurj :=
    deckOrbitDeletionComparisonFunctor_essSurj (k := k) D S hS
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

noncomputable instance deckOrbitDeletionEquivalence_functor_additive
    (hS : ActionInvariant (G := G) S) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (deckOrbitDeletionEquivalence (k := k) D S hS).functor.Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  change (deckOrbitDeletionComparisonFunctor (k := k) D S).Additive
  infer_instance

noncomputable instance deckOrbitDeletionEquivalence_functor_linear
    (hS : ActionInvariant (G := G) S) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (deckOrbitDeletionEquivalence (k := k) D S hS).functor.Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  change (deckOrbitDeletionComparisonFunctor (k := k) D S).Linear k
  infer_instance

end CoherentDeckShift

end MagnitudeConjecture.ObjectDeletion
