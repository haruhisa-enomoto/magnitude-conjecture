import MagnitudeConjecture.CategoryTheory.ShiftOrbitNormalTranslate
import MagnitudeConjecture.CategoryTheory.DeckOrbitSkeleton
import MagnitudeConjecture.Combinatorics.OrbitQuotientAction

/-!
# Ambient translations on a normal deck-orbit skeleton

For a normal subgroup `N ◁ G`, every ambient element `g : G` inverse-translates
the strict `N`-orbit of an object.  This file upgrades that object operation to
an additive endofunctor of the chosen deck-orbit skeleton.  On morphisms it uses
the normal translation of the nonskeletal `N`-shift-orbit category, conjugated
by the canonical isomorphisms to the chosen orbit representatives.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

private theorem conjugateMap_add
    {B : Type u} [Category.{v} B] [Preadditive B]
    (F : B ⥤ B) [F.Additive]
    {X Y X' Y' : B} (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y')
    (f h : X ⟶ Y) :
    eX.inv ≫ F.map (f + h) ≫ eY.hom =
      (eX.inv ≫ F.map f ≫ eY.hom) +
        (eX.inv ≫ F.map h ≫ eY.hom) := by
  rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]

private noncomputable abbrev normalTranslateOrbitObject
    (N : Subgroup G) (g : G)
    (q : MulAction.orbitRel.Quotient N C) :
    MulAction.orbitRel.Quotient N C :=
  Quotient.mk'' (g⁻¹ • deckOrbitRepresentative (C := C) (G := N) q)

/-- The fixed ambient shift of a chosen `N`-orbit representative is
isomorphic in the `N`-orbit category to the representative of the inverse
translated strict orbit. -/
noncomputable def shiftOrbitNormalTranslateRepresentativeIso
    (N : Subgroup G) [N.Normal] (g : G)
    (q : MulAction.orbitRel.Quotient N C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.shiftOrbitNormalTranslateFunctor N g).obj
        (deckOrbitRepresentative (C := C) (G := N) q) ≅
      deckOrbitRepresentative (C := C) (G := N)
        (normalTranslateOrbitObject (C := C) N g q) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  let X := deckOrbitRepresentative (C := C) (G := N) q
  exact ShiftOrbitCategory.identityComponentFunctor.mapIso
      (D.objIso g X) ≪≫
    (D.restrict N).objectIsoDeckOrbitRepresentative (g⁻¹ • X)

noncomputable def deckOrbitNormalTranslateMap
    (N : Subgroup G) [N.Normal] (g : G)
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
    (show DeckOrbitSkeleton C N from
        normalTranslateOrbitObject (C := C) N g q) ⟶
      (show DeckOrbitSkeleton C N from
        normalTranslateOrbitObject (C := C) N g r) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact InducedCategory.homMk
    ((D.shiftOrbitNormalTranslateRepresentativeIso N g q).inv ≫
      (D.shiftOrbitNormalTranslateFunctor N g).map f.hom ≫
      (D.shiftOrbitNormalTranslateRepresentativeIso N g r).hom)

set_option backward.isDefEq.respectTransparency false in
noncomputable def deckOrbitNormalTranslateFunctor
    (N : Subgroup G) [N.Normal] (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    DeckOrbitSkeleton C N ⥤ DeckOrbitSkeleton C N := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  exact
    { obj := normalTranslateOrbitObject (C := C) N g
      map := fun {q r} f ↦ D.deckOrbitNormalTranslateMap N g f
      map_id := by
        intro q
        apply InducedCategory.hom_ext
        change (D.shiftOrbitNormalTranslateRepresentativeIso N g q).inv ≫
            (D.shiftOrbitNormalTranslateFunctor N g).map (𝟙 _) ≫
            (D.shiftOrbitNormalTranslateRepresentativeIso N g q).hom = 𝟙 _
        rw [(D.shiftOrbitNormalTranslateFunctor N g).map_id]
        simp
      map_comp := by
        intro q r s f h
        apply InducedCategory.hom_ext
        simp only [deckOrbitNormalTranslateMap, InducedCategory.comp_hom,
          InducedCategory.homMk_hom, Functor.map_comp, Category.assoc,
          Iso.hom_inv_id_assoc] }

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem deckOrbitNormalTranslateMap_add
    (N : Subgroup G) [N.Normal] (g : G)
    {q r : MulAction.orbitRel.Quotient N C}
    (f h : letI := D.hasShift
      letI := D.additiveShift
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      (show DeckOrbitSkeleton C N from q) ⟶
        (show DeckOrbitSkeleton C N from r)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    D.deckOrbitNormalTranslateMap N g (f + h) =
      D.deckOrbitNormalTranslateMap N g f +
        D.deckOrbitNormalTranslateMap N g h := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  apply InducedCategory.hom_ext
  let F := D.shiftOrbitNormalTranslateFunctor N g
  let Xq : ShiftOrbitCategory C (Additive N) :=
    deckOrbitRepresentative (C := C) (G := N) q
  let Xr : ShiftOrbitCategory C (Additive N) :=
    deckOrbitRepresentative (C := C) (G := N) r
  let Yq : ShiftOrbitCategory C (Additive N) :=
    deckOrbitRepresentative (C := C) (G := N)
      (normalTranslateOrbitObject (C := C) N g q)
  let Yr : ShiftOrbitCategory C (Additive N) :=
    deckOrbitRepresentative (C := C) (G := N)
      (normalTranslateOrbitObject (C := C) N g r)
  let eQ : F.obj Xq ≅ Yq :=
    D.shiftOrbitNormalTranslateRepresentativeIso N g q
  let eR : F.obj Xr ≅ Yr :=
    D.shiftOrbitNormalTranslateRepresentativeIso N g r
  change eQ.inv ≫ F.map (f.hom + h.hom) ≫ eR.hom =
    (eQ.inv ≫ F.map f.hom ≫ eR.hom) +
      (eQ.inv ≫ F.map h.hom ≫ eR.hom)
  exact conjugateMap_add F eQ eR f.hom h.hom

set_option backward.isDefEq.respectTransparency false in
instance deckOrbitNormalTranslateFunctor_additive
    (N : Subgroup G) [N.Normal] (g : G) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    (D.deckOrbitNormalTranslateFunctor N g).Additive := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  constructor
  intro q r f h
  change D.deckOrbitNormalTranslateMap N g (f + h) =
    D.deckOrbitNormalTranslateMap N g f +
      D.deckOrbitNormalTranslateMap N g h
  exact D.deckOrbitNormalTranslateMap_add N g f h

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
