import MagnitudeConjecture.CategoryTheory.DeckOrbitSkeleton
import MagnitudeConjecture.CategoryTheory.ShiftOrbitSubgroupFunctor
import MagnitudeConjecture.Combinatorics.OrbitQuotientAction

/-!
# Functors between strict deck-orbit skeletons

For a subgroup `N ≤ G`, the inclusion of shift-orbit morphisms descends to
the strict orbit skeletons.  On objects the resulting functor is the literal
map from an `N`-orbit to the `G`-orbit containing it.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

private noncomputable abbrev subgroupOrbitObject (N : Subgroup G)
    (q : MulAction.orbitRel.Quotient N C) :
    MulAction.orbitRel.Quotient G C :=
  Quotient.mk'' (deckOrbitRepresentative (C := C) (G := N) q)

@[simp]
private theorem subgroupOrbitObject_mk (N : Subgroup G) (X : C) :
    subgroupOrbitObject (C := C) N
        (Quotient.mk'' X : MulAction.orbitRel.Quotient N C) =
      (Quotient.mk'' X : MulAction.orbitRel.Quotient G C) := by
  apply MulAction.orbitRel.quotient_eq_of_quotient_subgroup_eq'
  exact deckOrbitRepresentative_mk (C := C) (G := N)
    (Quotient.mk'' X : MulAction.orbitRel.Quotient N C)

/-- The morphism on strict orbit skeletons induced by extension from the
subgroup shift-orbit category. -/
noncomputable def deckOrbitSubgroupMap (N : Subgroup G)
    {q r : MulAction.orbitRel.Quotient N C}
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      (show DeckOrbitSkeleton C N from q) ⟶
        (show DeckOrbitSkeleton C N from r)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (show DeckOrbitSkeleton C G from subgroupOrbitObject (C := C) N q) ⟶
      (show DeckOrbitSkeleton C G from subgroupOrbitObject (C := C) N r) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  let X := deckOrbitRepresentative (C := C) (G := N) q
  let Y := deckOrbitRepresentative (C := C) (G := N) r
  exact InducedCategory.homMk
    ((D.objectIsoDeckOrbitRepresentative X).inv ≫
      (D.shiftOrbitSubgroupFunctor N).map f.hom ≫
      (D.objectIsoDeckOrbitRepresentative Y).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Passing from the strict `N`-orbit skeleton to the strict `G`-orbit
skeleton.  Its object map sends an `N`-orbit to the `G`-orbit containing it. -/
noncomputable def deckOrbitSubgroupFunctor (N : Subgroup G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    DeckOrbitSkeleton C N ⥤ DeckOrbitSkeleton C G := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact
    { obj := fun q : MulAction.orbitRel.Quotient N C ↦
        subgroupOrbitObject (C := C) N q
      map := fun {q r : MulAction.orbitRel.Quotient N C} f ↦
        D.deckOrbitSubgroupMap N f
      map_id := by
        intro q
        let X := deckOrbitRepresentative (C := C) (G := N) q
        apply InducedCategory.hom_ext
        change (D.objectIsoDeckOrbitRepresentative X).inv ≫
            D.shiftOrbitSubgroupMap N X X (shiftOrbitId X) ≫
            (D.objectIsoDeckOrbitRepresentative X).hom =
          𝟙 (show ShiftOrbitCategory C (Additive G) from
            deckOrbitRepresentative (C := C) (G := G)
              (Quotient.mk'' X : MulAction.orbitRel.Quotient G C))
        rw [D.shiftOrbitSubgroupMap_id]
        have hright :
            (D.objectIsoDeckOrbitRepresentative X).inv ≫ shiftOrbitId X =
              (D.objectIsoDeckOrbitRepresentative X).inv :=
          shiftOrbitComp_id_right
            (D.objectIsoDeckOrbitRepresentative X).inv
        calc
          (D.objectIsoDeckOrbitRepresentative X).inv ≫ shiftOrbitId X ≫
              (D.objectIsoDeckOrbitRepresentative X).hom =
            ((D.objectIsoDeckOrbitRepresentative X).inv ≫ shiftOrbitId X) ≫
              (D.objectIsoDeckOrbitRepresentative X).hom :=
            (Category.assoc _ _ _).symm
          _ =
            (D.objectIsoDeckOrbitRepresentative X).inv ≫
              (D.objectIsoDeckOrbitRepresentative X).hom :=
            congrArg
              (fun t ↦ t ≫ (D.objectIsoDeckOrbitRepresentative X).hom)
              hright
          _ = _ := (D.objectIsoDeckOrbitRepresentative X).inv_hom_id
      map_comp := by
        intro q r s f g
        let X := deckOrbitRepresentative (C := C) (G := N) q
        let Y := deckOrbitRepresentative (C := C) (G := N) r
        let Z := deckOrbitRepresentative (C := C) (G := N) s
        apply InducedCategory.hom_ext
        change (D.objectIsoDeckOrbitRepresentative X).inv ≫
            D.shiftOrbitSubgroupMap N X Z
              (shiftOrbitCompHom f.hom g.hom) ≫
            (D.objectIsoDeckOrbitRepresentative Z).hom =
          ((D.objectIsoDeckOrbitRepresentative X).inv ≫
              D.shiftOrbitSubgroupMap N X Y f.hom ≫
              (D.objectIsoDeckOrbitRepresentative Y).hom) ≫
            (D.objectIsoDeckOrbitRepresentative Y).inv ≫
            D.shiftOrbitSubgroupMap N Y Z g.hom ≫
            (D.objectIsoDeckOrbitRepresentative Z).hom
        rw [D.shiftOrbitSubgroupMap_comp]
        simp
        simp only [Y]
        exact Category.assoc
          (D.shiftOrbitSubgroupMap N X
            (deckOrbitRepresentative (C := C) (G := N) r) f.hom)
          (D.shiftOrbitSubgroupMap N
            (deckOrbitRepresentative (C := C) (G := N) r) Z g.hom)
          (D.objectIsoDeckOrbitRepresentative Z).hom }

@[simp]
theorem deckOrbitSubgroupFunctor_obj_mk (N : Subgroup G) (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.deckOrbitSubgroupFunctor N).obj
        (show DeckOrbitSkeleton C N from
          (Quotient.mk'' X : MulAction.orbitRel.Quotient N C)) =
      (show DeckOrbitSkeleton C G from
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)) := by
  exact subgroupOrbitObject_mk (C := C) N X

/-- The strict-orbit object functor is the flattening map in the orbit-tower
equivalence. -/
theorem orbitTowerEquiv_mk_eq_deckOrbitSubgroupFunctor_obj
    (N : Subgroup G) [N.Normal]
    (q : MulAction.orbitRel.Quotient N C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    MagnitudeConjecture.CoveringAction.orbitTowerEquiv N
        (Quotient.mk'' q : MulAction.orbitRel.Quotient (G ⧸ N)
          (MulAction.orbitRel.Quotient N C)) =
      (D.deckOrbitSubgroupFunctor N).obj
        (show DeckOrbitSkeleton C N from q) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  induction q using Quotient.inductionOn' with
  | _ X =>
      rw [MagnitudeConjecture.CoveringAction.orbitTowerEquiv_mk,
        D.deckOrbitSubgroupFunctor_obj_mk]

instance deckOrbitSubgroupFunctor_additive (N : Subgroup G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.deckOrbitSubgroupFunctor N).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  constructor
  intro q r f g
  let X := deckOrbitRepresentative (C := C) (G := N) q
  let Y := deckOrbitRepresentative (C := C) (G := N) r
  apply InducedCategory.hom_ext
  change (D.objectIsoDeckOrbitRepresentative X).inv ≫
        D.shiftOrbitSubgroupMap N X Y (f.hom + g.hom) ≫
        (D.objectIsoDeckOrbitRepresentative Y).hom =
      (D.objectIsoDeckOrbitRepresentative X).inv ≫
          D.shiftOrbitSubgroupMap N X Y f.hom ≫
          (D.objectIsoDeckOrbitRepresentative Y).hom +
        (D.objectIsoDeckOrbitRepresentative X).inv ≫
          D.shiftOrbitSubgroupMap N X Y g.hom ≫
          (D.objectIsoDeckOrbitRepresentative Y).hom
  rw [(D.shiftOrbitSubgroupMap N X Y).map_add,
    Preadditive.add_comp, Preadditive.comp_add]

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
