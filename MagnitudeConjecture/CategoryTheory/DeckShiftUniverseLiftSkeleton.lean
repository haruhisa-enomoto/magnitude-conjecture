import MagnitudeConjecture.CategoryTheory.DeckOrbitSkeleton
import MagnitudeConjecture.CategoryTheory.DeckShiftUniverseLiftOrbit

/-!
# Reindexing skeletal deck-orbit categories across a universe lift

The shift-orbit equivalence induced by `ULift` is identity on upstairs
objects.  Here it is descended to the one-object-per-strict-orbit skeleton.
The resulting object map is the literal equivalence between the two orbit
quotients, which is the extra precision needed for finite category algebras.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w w' uK

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]

/-- Universe lifting the acting group does not change the set of strict
object orbits. -/
noncomputable def uliftOrbitQuotientEquiv :
    MulAction.orbitRel.Quotient (ULift.{w'} G) C ≃
      MulAction.orbitRel.Quotient G C :=
  Quotient.congr (Equiv.refl C) fun X Y ↦ by
    simp only [MulAction.orbitRel_apply]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g.down, hg⟩
    · rintro ⟨g, hg⟩
      exact ⟨ULift.up g, hg⟩

omit [Category C] [Preadditive C] in
@[simp]
theorem uliftOrbitQuotientEquiv_mk (X : C) :
    (uliftOrbitQuotientEquiv (C := C) (G := G) :
      MulAction.orbitRel.Quotient (ULift.{w'} G) C ≃
        MulAction.orbitRel.Quotient G C)
        (Quotient.mk'' X) = Quotient.mk'' X :=
  rfl

namespace CoherentDeckShift

variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable {k : Type uK} [CommRing k] [CategoryTheory.Linear k C]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The chosen lifted-orbit representative and the chosen original-orbit
representative of the corresponding quotient class are isomorphic in the
original shift-orbit category. -/
noncomputable def uliftRepresentativeIso
    (q : MulAction.orbitRel.Quotient (ULift.{w'} G) C) :
    letI := D.hasShift
    letI := D.additiveShift
    (show ShiftOrbitCategory C (Additive G) from
      deckOrbitRepresentative (C := C) (G := ULift.{w'} G) q) ≅
    (show ShiftOrbitCategory C (Additive G) from
      deckOrbitRepresentative (C := C) (G := G)
        (uliftOrbitQuotientEquiv (C := C) (G := G) q)) := by
  letI := D.hasShift
  letI := D.additiveShift
  let R := deckOrbitRepresentative (C := C) (G := ULift.{w'} G) q
  have hq :
      (Quotient.mk'' R : MulAction.orbitRel.Quotient G C) =
        uliftOrbitQuotientEquiv (C := C) (G := G) q := by
    rw [← uliftOrbitQuotientEquiv_mk (C := C) (G := G) R]
    exact congrArg
      (uliftOrbitQuotientEquiv (C := C) (G := G))
      (deckOrbitRepresentative_mk
        (C := C) (G := ULift.{w'} G) q)
  exact D.objectIsoDeckOrbitRepresentative R ≪≫
    ShiftOrbitCategory.identityComponentFunctor.mapIso
      (eqToIso (congrArg
        (deckOrbitRepresentative (C := C) (G := G)) hq))

/-- Reindex a morphism between lifted orbit representatives and conjugate it
to the independently chosen representatives of the corresponding original
orbits. -/
noncomputable def uliftDeckOrbitSkeletonMap
    {q r : MulAction.orbitRel.Quotient (ULift.{w'} G) C}
    (f : letI := D.ulift.{u, v, w, w'}.hasShift
      letI := D.ulift.{u, v, w, w'}.additiveShift
      (show DeckOrbitSkeleton C (ULift.{w'} G) from q) ⟶
        (show DeckOrbitSkeleton C (ULift.{w'} G) from r)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    (show DeckOrbitSkeleton C G from
        uliftOrbitQuotientEquiv (C := C) (G := G) q) ⟶
      (show DeckOrbitSkeleton C G from
        uliftOrbitQuotientEquiv (C := C) (G := G) r) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  exact InducedCategory.homMk
    ((D.uliftRepresentativeIso q).inv ≫
      (D.uliftShiftOrbitFunctor (k := k)).map f.hom ≫
      (D.uliftRepresentativeIso r).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The strict orbit-quotient equivalence and representative-conjugated Hom
maps form the canonical functor between the two orbit skeletons. -/
noncomputable def uliftDeckOrbitSkeletonFunctor :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    DeckOrbitSkeleton C (ULift.{w'} G) ⥤ DeckOrbitSkeleton C G := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  exact
    { obj := uliftOrbitQuotientEquiv (C := C) (G := G)
      map := fun f ↦ D.uliftDeckOrbitSkeletonMap (k := k) f
      map_id := by
        intro q
        apply InducedCategory.hom_ext
        simp only [uliftDeckOrbitSkeletonMap,
          InducedCategory.homMk_hom, InducedCategory.id_hom]
        change (D.uliftRepresentativeIso q).inv ≫
            D.uliftShiftOrbitLinearEquiv (k := k) _ _ (shiftOrbitId _) ≫
            (D.uliftRepresentativeIso q).hom = shiftOrbitId _
        rw [D.uliftShiftOrbitLinearEquiv_id]
        change (D.uliftRepresentativeIso q).inv ≫ 𝟙 _ ≫
            (D.uliftRepresentativeIso q).hom = 𝟙 _
        simp
      map_comp := by
        intro q r s f g
        apply InducedCategory.hom_ext
        simp only [uliftDeckOrbitSkeletonMap,
          InducedCategory.homMk_hom, InducedCategory.comp_hom]
        rw [Functor.map_comp]
        simp only [Category.assoc, Iso.hom_inv_id_assoc] }

omit [∀ a : Additive G, (D.core.F a).Linear k] in
@[simp]
theorem uliftDeckOrbitSkeletonFunctor_obj
    (q : MulAction.orbitRel.Quotient (ULift.{w'} G) C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    (D.uliftDeckOrbitSkeletonFunctor (k := k)).obj q =
      uliftOrbitQuotientEquiv (C := C) (G := G) q :=
  rfl

set_option backward.isDefEq.respectTransparency false in
instance uliftDeckOrbitSkeletonFunctor_additive :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    (D.uliftDeckOrbitSkeletonFunctor (k := k)).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  constructor
  intro q r f g
  apply InducedCategory.hom_ext
  let iq := D.uliftRepresentativeIso q
  let ir := D.uliftRepresentativeIso r
  let F := D.uliftShiftOrbitFunctor (k := k)
  change iq.inv ≫ F.map (f.hom + g.hom) ≫ ir.hom =
    iq.inv ≫ F.map f.hom ≫ ir.hom +
      iq.inv ≫ F.map g.hom ≫ ir.hom
  rw [F.map_add]
  simp only [Preadditive.comp_add, Preadditive.add_comp]

set_option backward.isDefEq.respectTransparency false in
instance uliftDeckOrbitSkeletonFunctor_linear :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    (D.uliftDeckOrbitSkeletonFunctor (k := k)).Linear k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  constructor
  intro q r f c
  apply InducedCategory.hom_ext
  let iq := D.uliftRepresentativeIso q
  let ir := D.uliftRepresentativeIso r
  let F := D.uliftShiftOrbitFunctor (k := k)
  change iq.inv ≫ F.map (c • f.hom) ≫ ir.hom =
    c • (iq.inv ≫ F.map f.hom ≫ ir.hom)
  rw [F.map_smul]
  simp only [Linear.comp_smul, Linear.smul_comp]

instance uliftDeckOrbitSkeletonFunctor_full :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    (D.uliftDeckOrbitSkeletonFunctor (k := k)).Full := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  constructor
  intro q r f
  let F := D.uliftShiftOrbitFunctor (k := k)
  refine ⟨InducedCategory.homMk
    (F.preimage
      ((D.uliftRepresentativeIso q).hom ≫ f.hom ≫
        (D.uliftRepresentativeIso r).inv)), ?_⟩
  apply InducedCategory.hom_ext
  change (D.uliftRepresentativeIso q).inv ≫
      F.map (F.preimage
        ((D.uliftRepresentativeIso q).hom ≫ f.hom ≫
          (D.uliftRepresentativeIso r).inv)) ≫
      (D.uliftRepresentativeIso r).hom = f.hom
  rw [F.map_preimage]
  let iq := D.uliftRepresentativeIso q
  let ir := D.uliftRepresentativeIso r
  change iq.inv ≫ (iq.hom ≫ f.hom ≫ ir.inv) ≫ ir.hom = f.hom
  simp

instance uliftDeckOrbitSkeletonFunctor_faithful :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    (D.uliftDeckOrbitSkeletonFunctor (k := k)).Faithful := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  constructor
  intro q r f g h
  apply InducedCategory.hom_ext
  let F := D.uliftShiftOrbitFunctor (k := k)
  have hhom := congrArg InducedCategory.Hom.hom h
  simp only [uliftDeckOrbitSkeletonFunctor,
    uliftDeckOrbitSkeletonMap, InducedCategory.homMk_hom] at hhom
  let iq := D.uliftRepresentativeIso q
  let ir := D.uliftRepresentativeIso r
  change iq.inv ≫
      F.map f.hom ≫ ir.hom =
    iq.inv ≫
      F.map g.hom ≫ ir.hom at hhom
  have hleft :
      iq.inv ≫ (F.map f.hom ≫ ir.hom) =
        iq.inv ≫ (F.map g.hom ≫ ir.hom) := by
    simpa only [Category.assoc] using hhom
  have hright : F.map f.hom ≫ ir.hom = F.map g.hom ≫ ir.hom :=
    (cancel_epi iq.inv).mp hleft
  exact F.map_injective ((cancel_mono ir.hom).mp hright)

omit [∀ a : Additive G, (D.core.F a).Linear k] in
/-- The skeletal reindexing functor is literally bijective on objects. -/
theorem uliftDeckOrbitSkeletonFunctor_obj_bijective :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    Function.Bijective
      (D.uliftDeckOrbitSkeletonFunctor (k := k)).obj := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  change Function.Bijective
    (uliftOrbitQuotientEquiv (C := C) (G := G))
  exact (uliftOrbitQuotientEquiv (C := C) (G := G)).bijective

/-- Universe lifting the deck group does not change the one-object-per-orbit
linear category. -/
noncomputable def uliftDeckOrbitSkeletonEquivalence :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := D.ulift.{u, v, w, w'}.hasShift
    letI := D.ulift.{u, v, w, w'}.additiveShift
    letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
    DeckOrbitSkeleton C (ULift.{w'} G) ≌ DeckOrbitSkeleton C G := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := D.ulift.{u, v, w, w'}.hasShift
  letI := D.ulift.{u, v, w, w'}.additiveShift
  letI := D.ulift.{u, v, w, w'}.linearShift (k := k)
  let F := D.uliftDeckOrbitSkeletonFunctor (k := k)
  let e := uliftOrbitQuotientEquiv (C := C) (G := G)
  letI : F.IsEquivalence :=
    { full := inferInstance
      faithful := inferInstance
      essSurj := ⟨fun q ↦
        ⟨e.symm q, ⟨eqToIso (e.apply_symm_apply q)⟩⟩⟩ }
  exact F.asEquivalence

end CoherentDeckShift

end MagnitudeConjecture.CoveringHom
