import MagnitudeConjecture.CategoryTheory.OrbitPushdownFunctor
import MagnitudeConjecture.CategoryTheory.ShiftOrbitObjectIso
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Whiskering
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A skeletal base for a coherent deck orbit category

The concrete shift-orbit category retains every upstairs object.  This file
replaces its object type by the quotient of the strict deck action, chooses
one representative of every orbit, and inherits all morphisms from the
shift-orbit category between those representatives.

The representative inclusion is fully faithful by construction.  For a
coherent deck shift it is also essentially surjective, so this induced
category is genuinely equivalent to the nonskeletal shift-orbit category.
Gabriel push-down and its functorial action on linear modules are then
restricted along the representative inclusion.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w uK uM

section Representatives

variable {C : Type u}
variable {G : Type w} [Group G] [MulAction G C]

/-- The chosen representative of a strict deck orbit. -/
noncomputable def deckOrbitRepresentative
    (q : MulAction.orbitRel.Quotient G C) : C :=
  Quotient.out q

@[simp]
theorem deckOrbitRepresentative_mk
    (q : MulAction.orbitRel.Quotient G C) :
    Quotient.mk'' (deckOrbitRepresentative (C := C) (G := G) q) = q :=
  Quotient.out_eq' q

end Representatives

section OrbitSkeleton

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {G : Type w} [Group G] [MulAction G C]
variable [HasShift C (Additive G)]
variable [∀ a : Additive G, (shiftFunctor C a).Additive]
variable [∀ a : Additive G, (shiftFunctor C a).Linear k]

/-- One object per strict deck orbit, with morphisms inherited from the
shift-orbit category between the chosen representatives. -/
@[nolint unusedArguments]
noncomputable abbrev DeckOrbitSkeleton
    (C : Type u) [Category.{v} C] [Preadditive C]
    (G : Type w) [Group G] [MulAction G C]
    [HasShift C (Additive G)]
    [∀ a : Additive G, (shiftFunctor C a).Additive] : Type u :=
  InducedCategory (ShiftOrbitCategory C (Additive G))
    (fun q : MulAction.orbitRel.Quotient G C ↦
      (deckOrbitRepresentative (C := C) (G := G) q :
        ShiftOrbitCategory C (Additive G)))

/-- Inclusion of the chosen orbit representatives into the nonskeletal
shift-orbit category. -/
noncomputable abbrev deckOrbitRepresentativeFunctor :
    DeckOrbitSkeleton C G ⥤
      ShiftOrbitCategory C (Additive G) :=
  inducedFunctor (D := ShiftOrbitCategory C (Additive G))
    (fun q : MulAction.orbitRel.Quotient G C ↦
      (deckOrbitRepresentative (C := C) (G := G) q :
        ShiftOrbitCategory C (Additive G)))

instance deckOrbitRepresentativeFunctor_additive :
    (deckOrbitRepresentativeFunctor (C := C) (G := G)).Additive :=
  inferInstance

instance deckOrbitRepresentativeFunctor_linear :
    (deckOrbitRepresentativeFunctor (C := C) (G := G)).Linear k :=
  inferInstance

variable (M : C ⥤ ModuleCat.{uM} k) [M.Additive] [M.Linear k]

/-- Gabriel push-down restricted to one chosen representative of each strict
deck orbit. -/
noncomputable abbrev orbitSkeletonPushdown :
    DeckOrbitSkeleton C G ⥤ ModuleCat.{max w uM} k :=
  deckOrbitRepresentativeFunctor (C := C) (G := G) ⋙
    orbitPushdown (A := Additive G) M

instance orbitSkeletonPushdown_additive :
    (orbitSkeletonPushdown (G := G) M).Additive := inferInstance

instance orbitSkeletonPushdown_linear :
    (orbitSkeletonPushdown (G := G) M).Linear k := inferInstance

/-- Skeletal Gabriel push-down as a functor on linear modules. -/
noncomputable def linearModuleOrbitSkeletonPushdown :
    LinearModuleCategory.{u, v, uK, uM} (C := C) k ⥤
      LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k where
  obj M := ⟨orbitSkeletonPushdown (G := G) M.obj,
    inferInstance, inferInstance⟩
  map {M N} α := ObjectProperty.homMk
    (Functor.whiskerLeft
      (deckOrbitRepresentativeFunctor (C := C) (G := G))
      (orbitPushdownNatTrans (A := Additive G) α.hom))
  map_id M := by
    apply ObjectProperty.hom_ext
    change Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        (orbitPushdownNatTrans (A := Additive G) (𝟙 M.obj)) =
      𝟙 (orbitSkeletonPushdown (G := G) M.obj)
    rw [orbitPushdownNatTrans_id]
    exact Functor.whiskerLeft_id _
  map_comp {M N P} α β := by
    apply ObjectProperty.hom_ext
    change Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        (orbitPushdownNatTrans (A := Additive G) (α.hom ≫ β.hom)) =
      Functor.whiskerLeft
          (deckOrbitRepresentativeFunctor (C := C) (G := G))
          (orbitPushdownNatTrans (A := Additive G) α.hom) ≫
        Functor.whiskerLeft
          (deckOrbitRepresentativeFunctor (C := C) (G := G))
          (orbitPushdownNatTrans (A := Additive G) β.hom)
    rw [orbitPushdownNatTrans_comp, Functor.whiskerLeft_comp]

instance linearModuleOrbitSkeletonPushdown_additive :
    (linearModuleOrbitSkeletonPushdown
      (k := k) (C := C) (G := G)).Additive where
  map_add := by
    intro M N α β
    apply ObjectProperty.hom_ext
    change Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        (orbitPushdownNatTrans (A := Additive G) (α.hom + β.hom)) =
      Functor.whiskerLeft
          (deckOrbitRepresentativeFunctor (C := C) (G := G))
          (orbitPushdownNatTrans (A := Additive G) α.hom) +
        Functor.whiskerLeft
          (deckOrbitRepresentativeFunctor (C := C) (G := G))
          (orbitPushdownNatTrans (A := Additive G) β.hom)
    rw [orbitPushdownNatTrans_add]
    rfl

instance linearModuleOrbitSkeletonPushdown_linear :
    (linearModuleOrbitSkeletonPushdown
      (k := k) (C := C) (G := G)).Linear k where
  map_smul α r := by
    apply ObjectProperty.hom_ext
    change Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        (orbitPushdownNatTrans (A := Additive G) (r • α.hom)) =
      r • Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor (C := C) (G := G))
        (orbitPushdownNatTrans (A := Additive G) α.hom)
    rw [orbitPushdownNatTrans_smul]
    rfl

end OrbitSkeleton

namespace CoherentDeckShift

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]

/-- Every upstairs object is isomorphic in the orbit category to the chosen
representative of its strict deck orbit. -/
noncomputable def objectIsoDeckOrbitRepresentative (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    (show ShiftOrbitCategory C (Additive G) from X) ≅
      (show ShiftOrbitCategory C (Additive G) from
        deckOrbitRepresentative (C := C) (G := G)
          (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)) := by
  letI := D.hasShift
  letI := D.additiveShift
  let R := deckOrbitRepresentative (C := C) (G := G)
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
  have hq :
      (Quotient.mk'' R : MulAction.orbitRel.Quotient G C) =
        Quotient.mk'' X :=
    deckOrbitRepresentative_mk (C := C) (G := G)
      (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
  have horbit : R ∈ MulAction.orbit G X :=
    MulAction.orbitRel_apply.mp (Quotient.exact hq)
  let g : G := horbit.choose
  have hg : g • X = R := horbit.choose_spec
  change g • X = deckOrbitRepresentative
    (Quotient.mk'' X : MulAction.orbitRel.Quotient G C) at hg
  unfold deckOrbitRepresentative at hg
  exact ShiftOrbitCategory.objectShiftIso X (Additive.ofMul g⁻¹) ≪≫
    ShiftOrbitCategory.identityComponentFunctor.mapIso
      (D.objIso g⁻¹ X) ≪≫
    ShiftOrbitCategory.identityComponentFunctor.mapIso
      (eqToIso (by rw [inv_inv]; exact hg))

/-- The morphism between chosen orbit representatives induced by an upstairs
morphism. -/
noncomputable def orbitSkeletonMap {X Y : C} (f : X ⟶ Y) :
    letI := D.hasShift
    letI := D.additiveShift
    (show DeckOrbitSkeleton C G from
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)) ⟶
      (show DeckOrbitSkeleton C G from
        (Quotient.mk'' Y : MulAction.orbitRel.Quotient G C)) := by
  letI := D.hasShift
  letI := D.additiveShift
  exact InducedCategory.homMk
    ((D.objectIsoDeckOrbitRepresentative X).inv ≫
      (ShiftOrbitCategory.identityComponentFunctor
        (C := C) (A := Additive G)).map f ≫
      (D.objectIsoDeckOrbitRepresentative Y).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The strict-orbit object map and representative-conjugated morphism map
form the canonical functor from the upstairs category to the chosen orbit
skeleton. -/
noncomputable def orbitSkeletonFunctor :
    letI := D.hasShift
    letI := D.additiveShift
    C ⥤ DeckOrbitSkeleton C G := by
  letI := D.hasShift
  letI := D.additiveShift
  exact
    { obj := fun X ↦
        (Quotient.mk'' X : MulAction.orbitRel.Quotient G C)
      map := fun f ↦ D.orbitSkeletonMap f
      map_id := by
        intro X
        apply InducedCategory.hom_ext
        change (D.objectIsoDeckOrbitRepresentative X).inv ≫
            (ShiftOrbitCategory.identityComponentFunctor
              (C := C) (A := Additive G)).map (𝟙 X) ≫
            (D.objectIsoDeckOrbitRepresentative X).hom = 𝟙 _
        calc
          _ = (D.objectIsoDeckOrbitRepresentative X).inv ≫
              (𝟙 (show ShiftOrbitCategory C (Additive G) from X)) ≫
              (D.objectIsoDeckOrbitRepresentative X).hom := congrArg
                (fun q ↦ (D.objectIsoDeckOrbitRepresentative X).inv ≫ q ≫
                  (D.objectIsoDeckOrbitRepresentative X).hom)
                ((ShiftOrbitCategory.identityComponentFunctor
                  (C := C) (A := Additive G)).map_id X)
          _ = _ := by simp
      map_comp := by
        intro X Y Z f g
        apply InducedCategory.hom_ext
        simp only [orbitSkeletonMap, InducedCategory.comp_hom,
          InducedCategory.homMk_hom, Functor.map_comp, Category.assoc,
          Iso.hom_inv_id_assoc] }

@[simp]
theorem orbitSkeletonFunctor_obj (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    (D.orbitSkeletonFunctor).obj X =
      (Quotient.mk'' X : MulAction.orbitRel.Quotient G C) := by
  rfl

@[simp]
theorem orbitSkeletonFunctor_map {X Y : C} (f : X ⟶ Y) :
    letI := D.hasShift
    letI := D.additiveShift
    (D.orbitSkeletonFunctor).map f = D.orbitSkeletonMap f := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem orbitSkeletonMap_add {X Y : C} (f g : X ⟶ Y) :
    letI := D.hasShift
    letI := D.additiveShift
    D.orbitSkeletonMap (f + g) =
      D.orbitSkeletonMap f + D.orbitSkeletonMap g := by
  letI := D.hasShift
  letI := D.additiveShift
  apply InducedCategory.hom_ext
  simp only [orbitSkeletonMap, InducedCategory.homMk_hom,
    Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  rfl

instance orbitSkeletonFunctor_additive :
    letI := D.hasShift
    letI := D.additiveShift
    D.orbitSkeletonFunctor.Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  constructor
  intro X Y f g
  change D.orbitSkeletonMap (f + g) =
    D.orbitSkeletonMap f + D.orbitSkeletonMap g
  exact D.orbitSkeletonMap_add f g

@[simp]
theorem deckOrbitRepresentativeFunctor_map_orbitSkeletonMap
    {X Y : C} (f : X ⟶ Y) :
    letI := D.hasShift
    letI := D.additiveShift
    (deckOrbitRepresentativeFunctor (C := C) (G := G)).map
        (D.orbitSkeletonMap f) =
      (D.objectIsoDeckOrbitRepresentative X).inv ≫
        (ShiftOrbitCategory.identityComponentFunctor
          (C := C) (A := Additive G)).map f ≫
        (D.objectIsoDeckOrbitRepresentative Y).hom := by
  rfl

/-- The representative inclusion is essentially surjective, hence it really
is an orbit skeleton rather than merely a full subcategory. -/
instance deckOrbitRepresentativeFunctor_essSurj :
    letI := D.hasShift
    letI := D.additiveShift
    (deckOrbitRepresentativeFunctor
      (C := C) (G := G)).EssSurj := by
  letI := D.hasShift
  letI := D.additiveShift
  constructor
  intro X
  refine ⟨(Quotient.mk'' (show C from X) :
    MulAction.orbitRel.Quotient G C), ?_⟩
  exact ⟨(D.objectIsoDeckOrbitRepresentative (show C from X)).symm⟩

/-- The one-representative-per-orbit category is equivalent to the full
nonskeletal shift-orbit category. -/
noncomputable def deckOrbitSkeletonEquivalence :
    letI := D.hasShift
    letI := D.additiveShift
    DeckOrbitSkeleton C G ≌ ShiftOrbitCategory C (Additive G) := by
  letI := D.hasShift
  letI := D.additiveShift
  let F := deckOrbitRepresentativeFunctor (C := C) (G := G)
  letI : F.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := D.deckOrbitRepresentativeFunctor_essSurj }
  exact F.asEquivalence

noncomputable instance deckOrbitSkeletonEquivalence_functor_additive :
    letI := D.hasShift
    letI := D.additiveShift
    (D.deckOrbitSkeletonEquivalence).functor.Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  change (deckOrbitRepresentativeFunctor (C := C) (G := G)).Additive
  infer_instance

noncomputable instance deckOrbitSkeletonEquivalence_functor_linear
    {k : Type uK} [CommRing k] [CategoryTheory.Linear k C]
    [∀ a : Additive G, (D.core.F a).Linear k] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.deckOrbitSkeletonEquivalence).functor.Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  change (deckOrbitRepresentativeFunctor (C := C) (G := G)).Linear k
  infer_instance

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
