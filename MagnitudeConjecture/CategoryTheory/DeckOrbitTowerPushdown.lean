import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence
import MagnitudeConjecture.CategoryTheory.OrbitPushdownChangeBase
import MagnitudeConjecture.CategoryTheory.OrbitPushdownResidualFubiniModuleNaturality

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]
variable (M : C ⥤ ModuleCat.{uM} k) [M.Additive] [M.Linear k]

section

variable (N : Subgroup G) [N.Normal]

/-- Iterated strict skeletal push-down is direct strict skeletal push-down
after precomposition with strict tower flattening. -/
noncomputable def deckOrbitTowerPushdownIso :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    orbitSkeletonPushdown (G := G ⧸ N)
        (orbitSkeletonPushdown (G := N) M) ≅
      D.deckOrbitTowerFlattenFunctor (k := k) N ⋙
        orbitSkeletonPushdown (G := G) M := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  letI : (deckOrbitRepresentativeFunctor
      (C := C) (G := N)).CommShift (Additive (G ⧸ N)) :=
    D.deckOrbitRepresentativeResidualCommShift N
  let iQ := deckOrbitRepresentativeFunctor
    (C := DeckOrbitSkeleton C N) (G := G ⧸ N)
  let iN := deckOrbitRepresentativeFunctor (C := C) (G := N)
  let iG := deckOrbitRepresentativeFunctor (C := C) (G := G)
  let mapIN := shiftOrbitMapFunctor (k := k)
    (A := Additive (G ⧸ N)) iN
  let pushN := orbitPushdown (A := Additive N) M
  let pushQ := orbitPushdown (A := Additive (G ⧸ N)) pushN
  let pushG := orbitPushdown (A := Additive G) M
  let flatten := D.shiftOrbitResidualFlattenFunctor (k := k) N
  let deckFlatten := D.deckOrbitResidualFlattenFunctor (k := k) N
  let changeBase := orbitPushdownCommShiftIso
    (k := k) (A := Additive (G ⧸ N)) iN pushN
  let fubini := D.orbitPushdownResidualFubiniIso M N
  let representative :=
    D.deckOrbitResidualFlattenRepresentativeNatIso (k := k) N
  exact
    Functor.isoWhiskerLeft iQ changeBase ≪≫
      (Functor.associator iQ mapIN pushQ).symm ≪≫
      Functor.isoWhiskerLeft (iQ ⋙ mapIN) fubini ≪≫
      (Functor.associator (iQ ⋙ mapIN) flatten pushG).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator iQ mapIN flatten) pushG ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft iQ representative).symm pushG ≪≫
      Functor.isoWhiskerRight
        (Functor.associator iQ deckFlatten iG).symm pushG ≪≫
      Functor.associator (iQ ⋙ deckFlatten) iG pushG

set_option backward.isDefEq.respectTransparency false in
theorem deckOrbitTowerPushdownIso_module_naturality
    {L : C ⥤ ModuleCat.{uM} k} [L.Additive] [L.Linear k]
    (α : M ⟶ L) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    Functor.whiskerLeft
        (deckOrbitRepresentativeFunctor
          (C := DeckOrbitSkeleton C N) (G := G ⧸ N))
        (orbitPushdownNatTrans (A := Additive (G ⧸ N))
          (Functor.whiskerLeft
            (deckOrbitRepresentativeFunctor (C := C) (G := N))
            (orbitPushdownNatTrans (A := Additive N) α))) ≫
      (D.deckOrbitTowerPushdownIso L N).hom =
    (D.deckOrbitTowerPushdownIso M N).hom ≫
      Functor.whiskerLeft (D.deckOrbitTowerFlattenFunctor (k := k) N)
        (Functor.whiskerLeft
          (deckOrbitRepresentativeFunctor (C := C) (G := G))
          (orbitPushdownNatTrans (A := Additive G) α)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  letI : (deckOrbitRepresentativeFunctor
      (C := C) (G := N)).CommShift (Additive (G ⧸ N)) :=
    D.deckOrbitRepresentativeResidualCommShift N
  let iQ := deckOrbitRepresentativeFunctor
    (C := DeckOrbitSkeleton C N) (G := G ⧸ N)
  let iN := deckOrbitRepresentativeFunctor (C := C) (G := N)
  let iG := deckOrbitRepresentativeFunctor (C := C) (G := G)
  let mapIN := shiftOrbitMapFunctor (k := k)
    (A := Additive (G ⧸ N)) iN
  let flatten := D.shiftOrbitResidualFlattenFunctor (k := k) N
  let representative :=
    D.deckOrbitResidualFlattenRepresentativeNatIso (k := k) N
  apply NatTrans.ext
  funext q
  have hChange :
      (orbitPushdownNatTrans (A := Additive (G ⧸ N))
          (Functor.whiskerLeft iN
            (orbitPushdownNatTrans (A := Additive N) α))).app
            (iQ.obj q) ≫
        (orbitPushdownCommShiftIso (k := k) (A := Additive (G ⧸ N))
          iN (orbitPushdown (A := Additive N) L)).hom.app (iQ.obj q) =
      (orbitPushdownCommShiftIso (k := k) (A := Additive (G ⧸ N))
          iN (orbitPushdown (A := Additive N) M)).hom.app (iQ.obj q) ≫
        (orbitPushdownNatTrans (A := Additive (G ⧸ N))
          (orbitPushdownNatTrans (A := Additive N) α)).app
            (mapIN.obj (iQ.obj q)) := by
    apply ModuleCat.hom_ext
    change
      (orbitPushdownCommShiftLinearEquiv iN
          (orbitPushdown (A := Additive N) L) (iQ.obj q)).toLinearMap.comp
          (orbitPushdownNatTransAppLinear (A := Additive (G ⧸ N))
            (Functor.whiskerLeft iN
              (orbitPushdownNatTrans (A := Additive N) α)) (iQ.obj q)) =
        (orbitPushdownNatTransAppLinear (A := Additive (G ⧸ N))
          (orbitPushdownNatTrans (A := Additive N) α)
            (iN.obj (iQ.obj q))).comp
          (orbitPushdownCommShiftLinearEquiv iN
            (orbitPushdown (A := Additive N) M) (iQ.obj q)).toLinearMap
    exact orbitPushdownCommShiftLinearEquiv_module_naturality
      iN (orbitPushdownNatTrans (A := Additive N) α) (iQ.obj q)
  have hFubini :
      (orbitPushdownNatTrans (A := Additive (G ⧸ N))
          (orbitPushdownNatTrans (A := Additive N) α)).app
            (mapIN.obj (iQ.obj q)) ≫
        (D.orbitPushdownResidualFubiniIso L N).hom.app
          ((iQ ⋙ mapIN).obj q) =
      (D.orbitPushdownResidualFubiniIso M N).hom.app
          ((iQ ⋙ mapIN).obj q) ≫
        (orbitPushdownNatTrans (A := Additive G) α).app
          (flatten.obj (mapIN.obj (iQ.obj q))) := by
    apply ModuleCat.hom_ext
    change
      (D.orbitPushdownResidualFubiniLinearEquiv
          (M := L) N (show C from mapIN.obj (iQ.obj q))).toLinearMap.comp
        (orbitPushdownNatTransAppLinear (A := Additive (G ⧸ N))
          (orbitPushdownNatTrans (A := Additive N) α)
          (show ShiftOrbitCategory C (Additive N) from
            mapIN.obj (iQ.obj q))) =
      (orbitPushdownNatTransAppLinear (A := Additive G) α
          (show C from mapIN.obj (iQ.obj q))).comp
        (D.orbitPushdownResidualFubiniLinearEquiv
          (M := M) N (show C from mapIN.obj (iQ.obj q))).toLinearMap
    exact D.orbitPushdownResidualFubiniLinearEquiv_module_naturality
      α N (show C from mapIN.obj (iQ.obj q))
  have hTail :
      (orbitPushdownNatTrans (A := Additive G) α).app
          (flatten.obj (mapIN.obj (iQ.obj q))) ≫
        (orbitPushdown (A := Additive G) L).map
          (𝟙 (((iQ ⋙ mapIN) ⋙ flatten).obj q)) ≫
        (orbitPushdown (A := Additive G) L).map
          ((Functor.isoWhiskerLeft iQ representative).inv.app q) ≫
        (orbitPushdown (A := Additive G) L).map
          (𝟙 ((iQ ⋙ D.deckOrbitResidualFlattenFunctor (k := k) N ⋙ iG).obj q)) =
      (orbitPushdown (A := Additive G) M).map
          (𝟙 (((iQ ⋙ mapIN) ⋙ flatten).obj q)) ≫
      (orbitPushdown (A := Additive G) M).map
          ((Functor.isoWhiskerLeft iQ representative).inv.app q) ≫
        (orbitPushdown (A := Additive G) M).map
          (𝟙 ((iQ ⋙ D.deckOrbitResidualFlattenFunctor (k := k) N ⋙ iG).obj q)) ≫
        (orbitPushdownNatTrans (A := Additive G) α).app
          (iG.obj ((D.deckOrbitTowerFlattenFunctor (k := k) N).obj q)) := by
    change
      (orbitPushdownNatTrans (A := Additive G) α).app
          (((iQ ⋙ mapIN) ⋙ flatten).obj q) ≫
        (orbitPushdown (A := Additive G) L).map
          (𝟙 (((iQ ⋙ mapIN) ⋙ flatten).obj q)) ≫
        (orbitPushdown (A := Additive G) L).map
          ((Functor.isoWhiskerLeft iQ representative).inv.app q) ≫
        (orbitPushdown (A := Additive G) L).map
          (𝟙 ((iQ ⋙ D.deckOrbitResidualFlattenFunctor (k := k) N ⋙ iG).obj q)) =
      (orbitPushdown (A := Additive G) M).map
          (𝟙 (((iQ ⋙ mapIN) ⋙ flatten).obj q)) ≫
        (orbitPushdown (A := Additive G) M).map
          ((Functor.isoWhiskerLeft iQ representative).inv.app q) ≫
        (orbitPushdown (A := Additive G) M).map
          (𝟙 ((iQ ⋙ D.deckOrbitResidualFlattenFunctor (k := k) N ⋙ iG).obj q)) ≫
        (orbitPushdownNatTrans (A := Additive G) α).app
          ((iQ ⋙ D.deckOrbitResidualFlattenFunctor (k := k) N ⋙ iG).obj q)
    simpa only [Functor.map_comp, Category.assoc] using
      ((orbitPushdownNatTrans (A := Additive G) α).naturality
        ((𝟙 (((iQ ⋙ mapIN) ⋙ flatten).obj q)) ≫
          (Functor.isoWhiskerLeft iQ representative).inv.app q ≫
          (𝟙 ((iQ ⋙ D.deckOrbitResidualFlattenFunctor (k := k) N ⋙ iG).obj q)))).symm
  dsimp only [iQ, iN, iG, mapIN, flatten, representative] at hChange hFubini hTail
  dsimp only [deckOrbitTowerPushdownIso]
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp]
  rw [← Category.assoc, hChange, Category.assoc]
  rw [← Category.assoc
    ((orbitPushdownNatTrans (A := Additive (G ⧸ N))
      (orbitPushdownNatTrans (A := Additive N) α)).app
        (mapIN.obj (iQ.obj q)))
    ((D.orbitPushdownResidualFubiniIso L N).hom.app
      ((iQ ⋙ mapIN).obj q)) _]
  rw [hFubini]
  rw [Category.assoc]
  rw [hTail]
  simp only [Category.assoc]

/-- Iterated strict skeletal push-down of linear modules agrees naturally
with direct strict skeletal push-down transported across tower flattening. -/
noncomputable def linearModuleOrbitSkeletonPushdownTowerIso :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := N) ⋙
      linearModuleOrbitSkeletonPushdown
        (k := k) (C := DeckOrbitSkeleton C N) (G := G ⧸ N) ≅
    linearModuleOrbitSkeletonPushdown
        (k := k) (C := C) (G := G) ⋙
      (D.deckOrbitTowerLinearModuleEquivalence (R := k) N).functor := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI : MulAction (G ⧸ N) (DeckOrbitSkeleton C N) :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  refine NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ (D.deckOrbitTowerPushdownIso M.obj N)) ?_
  intro M L α
  apply ObjectProperty.hom_ext
  exact D.deckOrbitTowerPushdownIso_module_naturality M.obj N α.hom

end

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
