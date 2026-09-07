import MagnitudeConjecture.CategoryTheory.OrbitPushdownResidualFubini
import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerFlatten

/-!
# Equivalence for strict orbit towers

For a normal subgroup `N ◁ G`, flattening the residual strict orbit
skeleton followed by the `N`-orbit skeleton gives the direct strict
`G`-orbit skeleton.  The flattening functor is full, faithful, and
essentially surjective, hence an equivalence.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

set_option maxHeartbeats 800000 in
/-- Residual strict flattening followed by the ambient representative
inclusion agrees naturally with nonskeletal residual flattening after mapping
the subgroup representative inclusion through the residual orbit category. -/
noncomputable def deckOrbitResidualFlattenRepresentativeNatIso
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    letI := D.deckOrbitRepresentativeResidualCommShift N
    letI := D.shiftOrbitSubgroupResidualCommShift N
    (D.deckOrbitResidualFlattenFunctor (k := k) N) ⋙
        deckOrbitRepresentativeFunctor (C := C) (G := G) ≅
      shiftOrbitMapFunctor (k := k) (A := Additive (G ⧸ N))
          (deckOrbitRepresentativeFunctor (C := C) (G := N)) ⋙
        D.shiftOrbitResidualFlattenFunctor (k := k) N := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  let repComm := D.deckOrbitRepresentativeResidualCommShift N
  letI : (deckOrbitRepresentativeFunctor
      (C := C) (G := N)).CommShift (Additive (G ⧸ N)) := repComm
  letI := trivialHasShift
    (DeckOrbitSkeleton C G) (Additive (G ⧸ N))
  letI := trivialHasShift
    (ShiftOrbitCategory C (Additive G)) (Additive (G ⧸ N))
  let subgroupComm := D.shiftOrbitSubgroupResidualCommShift N
  letI : (D.shiftOrbitSubgroupFunctor N).CommShift
      (Additive (G ⧸ N)) := subgroupComm
  let deckComm := D.deckOrbitSubgroupResidualCommShift N
  letI : (D.deckOrbitSubgroupFunctor N).CommShift
      (Additive (G ⧸ N)) := deckComm
  letI : (deckOrbitRepresentativeFunctor
      (C := C) (G := G)).CommShift (Additive (G ⧸ N)) :=
    trivialFunctorCommShift _
  have compat : NatTrans.CommShift
      (D.deckOrbitSubgroupRepresentativeNatIso N).symm.hom
      (Additive (G ⧸ N)) := by
    exact Functor.CommShift.ofComp_compatibility
      (D.deckOrbitSubgroupRepresentativeNatIso N).symm
      (Additive (G ⧸ N))
  letI : NatTrans.CommShift
      (D.deckOrbitSubgroupRepresentativeNatIso N).symm.hom
      (Additive (G ⧸ N)) := compat
  refine NatIso.ofComponents
    (fun X ↦ (D.deckOrbitSubgroupRepresentativeNatIso N).symm.app
      (show DeckOrbitSkeleton C N from X)) ?_
  intro X Y f
  dsimp only [Functor.comp_obj, Functor.comp_map]
  change deckOrbitRepresentativeFunctor.map
      (trivialShiftOrbitFoldMapLinear
        (k := k) (A := Additive (G ⧸ N)) _ _
        (shiftOrbitDescendMapLinear (k := k)
          (A := Additive (G ⧸ N))
          (D.deckOrbitSubgroupFunctor N) f)) ≫
        ((D.deckOrbitSubgroupRepresentativeNatIso N).symm.app Y).hom =
    ((D.deckOrbitSubgroupRepresentativeNatIso N).symm.app X).hom ≫
      trivialShiftOrbitFoldMapLinear
        (k := k) (A := Additive (G ⧸ N)) _ _
        (shiftOrbitDescendMapLinear (k := k)
          (A := Additive (G ⧸ N))
          (D.shiftOrbitSubgroupFunctor N)
          (shiftOrbitDescendMapLinear (k := k)
            (A := Additive (G ⧸ N))
            deckOrbitRepresentativeFunctor f))
  classical
  let iN := deckOrbitRepresentativeFunctor (C := C) (G := N)
  let iG := deckOrbitRepresentativeFunctor (C := C) (G := G)
  let FN := D.deckOrbitSubgroupFunctor N
  let F := D.shiftOrbitSubgroupFunctor N
  let E := D.deckOrbitSubgroupRepresentativeNatIso N
  let left : (X ⟶ Y) →ₗ[k]
      (iG.obj (FN.obj X) ⟶ F.obj (iN.obj Y)) :=
    (CategoryTheory.Linear.rightComp k _ (E.inv.app Y)).comp
      ((iG.mapLinearMap k).comp
        ((D.deckOrbitResidualFlattenFunctor (k := k) N).mapLinearMap k))
  let right : (X ⟶ Y) →ₗ[k]
      (iG.obj (FN.obj X) ⟶ F.obj (iN.obj Y)) :=
    (CategoryTheory.Linear.leftComp k _ (E.inv.app X)).comp
      (((D.shiftOrbitResidualFlattenFunctor (k := k) N).mapLinearMap k).comp
        ((shiftOrbitMapFunctor (k := k)
          (A := Additive (G ⧸ N)) iN).mapLinearMap k))
  change left f = right f
  apply LinearMap.congr_fun (f := left) (g := right)
  apply DirectSum.linearMap_ext
  intro a
  apply LinearMap.ext
  intro fa
  change deckOrbitRepresentativeFunctor.map
      (trivialShiftOrbitFoldMapLinear
        (k := k) (A := Additive (G ⧸ N)) _ _
        (shiftOrbitDescendMapLinear (k := k)
          (A := Additive (G ⧸ N))
          (D.deckOrbitSubgroupFunctor N)
          (DirectSum.of
            (fun c : Additive (G ⧸ N) ↦
              ShiftHom (show DeckOrbitSkeleton C N from X)
                (show DeckOrbitSkeleton C N from Y) c) a fa))) ≫
        ((D.deckOrbitSubgroupRepresentativeNatIso N).symm.app Y).hom =
    ((D.deckOrbitSubgroupRepresentativeNatIso N).symm.app X).hom ≫
      trivialShiftOrbitFoldMapLinear
        (k := k) (A := Additive (G ⧸ N)) _ _
        (shiftOrbitDescendMapLinear (k := k)
          (A := Additive (G ⧸ N))
          (D.shiftOrbitSubgroupFunctor N)
          (shiftOrbitDescendMapLinear (k := k)
            (A := Additive (G ⧸ N))
            deckOrbitRepresentativeFunctor
            (DirectSum.of
              (fun c : Additive (G ⧸ N) ↦
                ShiftHom (show DeckOrbitSkeleton C N from X)
                  (show DeckOrbitSkeleton C N from Y) c) a fa)))
  rw [← shiftOrbitOf_eq_directSumOf
      (show DeckOrbitSkeleton C N from X)
      (show DeckOrbitSkeleton C N from Y) a fa]
  rw [shiftOrbitDescendMapLinear_of
      (F := D.deckOrbitSubgroupFunctor N)]
  rw [shiftOrbitDescendMapLinear_of
      (F := deckOrbitRepresentativeFunctor (C := C) (G := N))]
  have hright :
      trivialShiftOrbitFoldMapLinear
          (k := k) (A := Additive (G ⧸ N))
          ((deckOrbitRepresentativeFunctor (C := C) (G := N) ⋙
            D.shiftOrbitSubgroupFunctor N).obj X)
          ((deckOrbitRepresentativeFunctor (C := C) (G := N) ⋙
            D.shiftOrbitSubgroupFunctor N).obj Y)
          (shiftOrbitDescendMapLinear (k := k)
            (A := Additive (G ⧸ N))
            (D.shiftOrbitSubgroupFunctor N)
            (shiftOrbitOf
              ((deckOrbitRepresentativeFunctor
                (C := C) (G := N)).obj
                  (show DeckOrbitSkeleton C N from X))
              ((deckOrbitRepresentativeFunctor
                (C := C) (G := N)).obj
                  (show DeckOrbitSkeleton C N from Y)) a
              (shiftOrbitDescendHomogeneousMap
                (deckOrbitRepresentativeFunctor
                  (C := C) (G := N)) a fa))) =
        shiftOrbitDescendHomogeneousMap
          (D.shiftOrbitSubgroupFunctor N) a
            (shiftOrbitDescendHomogeneousMap
              (deckOrbitRepresentativeFunctor
                (C := C) (G := N)) a fa) := by
    let iN' := deckOrbitRepresentativeFunctor (C := C) (G := N)
    let F' := D.shiftOrbitSubgroupFunctor N
    let inner := shiftOrbitDescendHomogeneousMap iN' a fa
    let outer := shiftOrbitDescendHomogeneousMap F' a inner
    have hmap :
        shiftOrbitDescendMapLinear (k := k)
            (A := Additive (G ⧸ N)) F'
            (shiftOrbitOf (iN'.obj X) (iN'.obj Y) a inner) =
          shiftOrbitOf (F'.obj (iN'.obj X))
            (F'.obj (iN'.obj Y)) a outer := by
      exact shiftOrbitDescendMapLinear_of
        (k := k) (A := Additive (G ⧸ N)) F' a inner
    calc
      _ = trivialShiftOrbitFoldMapLinear
          (k := k) (A := Additive (G ⧸ N))
          (F'.obj (iN'.obj X)) (F'.obj (iN'.obj Y))
          (shiftOrbitOf (F'.obj (iN'.obj X))
            (F'.obj (iN'.obj Y)) a outer) := by
        exact congrArg
          (trivialShiftOrbitFoldMapLinear
            (k := k) (A := Additive (G ⧸ N))
            (F'.obj (iN'.obj X)) (F'.obj (iN'.obj Y))) hmap
      _ = outer := by
        rw [trivialShiftOrbitFoldMapLinear_of]
        rfl
      _ = _ := rfl
  have hleft :
      trivialShiftOrbitFoldMapLinear
          (k := k) (A := Additive (G ⧸ N))
          ((D.deckOrbitSubgroupFunctor N).obj X)
          ((D.deckOrbitSubgroupFunctor N).obj Y)
          (shiftOrbitOf
            ((D.deckOrbitSubgroupFunctor N).obj X)
            ((D.deckOrbitSubgroupFunctor N).obj Y) a
            (shiftOrbitDescendHomogeneousMap
              (D.deckOrbitSubgroupFunctor N) a fa)) =
        shiftOrbitDescendHomogeneousMap
          (D.deckOrbitSubgroupFunctor N) a fa := by
    rw [trivialShiftOrbitFoldMapLinear_of]
    rfl
  calc
    _ = deckOrbitRepresentativeFunctor.map
          (shiftOrbitDescendHomogeneousMap
            (D.deckOrbitSubgroupFunctor N) a fa) ≫
        ((D.deckOrbitSubgroupRepresentativeNatIso N).symm.app Y).hom := by
      exact congrArg
        (fun z ↦ deckOrbitRepresentativeFunctor.map z ≫
          ((D.deckOrbitSubgroupRepresentativeNatIso N).symm.app Y).hom)
        hleft
    _ = ((D.deckOrbitSubgroupRepresentativeNatIso N).symm.app X).hom ≫
        shiftOrbitDescendHomogeneousMap
          (D.shiftOrbitSubgroupFunctor N) a
            (shiftOrbitDescendHomogeneousMap
              deckOrbitRepresentativeFunctor a fa) := by
      dsimp [deckComm, repComm, subgroupComm,
        deckOrbitSubgroupResidualCommShift]
      have hc := NatTrans.shift_app_comm
        (D.deckOrbitSubgroupRepresentativeNatIso N).symm.hom a
        (show DeckOrbitSkeleton C N from Y)
      simp only [Functor.commShiftIso_comp_hom_app] at hc
      rw [trivialFunctorCommShift_hom_app] at hc
      dsimp [trivialShiftMkCore, ShiftMkCore.shiftFunctor_eq] at hc
      simp only [Category.comp_id] at hc
      simp only [shiftOrbitDescendHomogeneousMap,
        InducedCategory.comp_hom, Category.assoc]
      change _ ≫ (_ ≫
        (D.deckOrbitSubgroupRepresentativeNatIso N).inv.app Y) = _
      erw [hc]
      let tail :=
        (D.shiftOrbitSubgroupFunctor N).map
            ((Functor.commShiftIso deckOrbitRepresentativeFunctor a).hom.app Y) ≫
          (Functor.commShiftIso
            (D.shiftOrbitSubgroupFunctor N) a).hom.app
              (deckOrbitRepresentativeFunctor.obj Y)
      have hn :=
        (D.deckOrbitSubgroupRepresentativeNatIso N).symm.hom.naturality_assoc
          fa tail
      erw [hn]
      have htail : tail =
          (D.shiftOrbitSubgroupFunctor N).map
              ((Functor.commShiftIso
                deckOrbitRepresentativeFunctor a).hom.app Y) ≫
            (Functor.commShiftIso
              (D.shiftOrbitSubgroupFunctor N) a).hom.app
                (deckOrbitRepresentativeFunctor.obj Y) := rfl
      rw [htail]
      simp only [Functor.comp_map]
      erw [← Functor.map_comp_assoc]
      rfl
    _ = _ := by
      exact (congrArg
        (fun z ↦
          ((D.deckOrbitSubgroupRepresentativeNatIso N).symm.app X).hom ≫ z)
        hright).symm

/-- Strict residual flattening is full. -/
instance deckOrbitResidualFlattenFunctor_full
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    (D.deckOrbitResidualFlattenFunctor (k := k) N).Full := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  exact Functor.Full.of_comp_faithful_iso
    (deckOrbitResidualFlattenRepresentativeNatIso (k := k) D N)

/-- Strict residual flattening is faithful. -/
instance deckOrbitResidualFlattenFunctor_faithful
    (N : Subgroup G) [N.Normal] :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    letI := D.deckOrbitResidualHasShift N
    letI := D.deckOrbitResidualAdditiveShift N
    letI := D.deckOrbitResidualLinearShift (k := k) N
    (D.deckOrbitResidualFlattenFunctor (k := k) N).Faithful := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  letI := D.deckOrbitResidualHasShift N
  letI := D.deckOrbitResidualAdditiveShift N
  letI := D.deckOrbitResidualLinearShift (k := k) N
  exact Functor.Faithful.of_comp_iso
    (deckOrbitResidualFlattenRepresentativeNatIso (k := k) D N)

/-- The strict orbit-tower flattening functor is full. -/
instance deckOrbitTowerFlattenFunctor_full
    (N : Subgroup G) [N.Normal] :
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
    (D.deckOrbitTowerFlattenFunctor (k := k) N).Full := by
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
  change (deckOrbitRepresentativeFunctor ⋙
    D.deckOrbitResidualFlattenFunctor (k := k) N).Full
  infer_instance

/-- The strict orbit-tower flattening functor is faithful. -/
instance deckOrbitTowerFlattenFunctor_faithful
    (N : Subgroup G) [N.Normal] :
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
    (D.deckOrbitTowerFlattenFunctor (k := k) N).Faithful := by
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
  change (deckOrbitRepresentativeFunctor ⋙
    D.deckOrbitResidualFlattenFunctor (k := k) N).Faithful
  infer_instance

/-- The strict orbit-tower flattening functor is essentially surjective. -/
instance deckOrbitTowerFlattenFunctor_essSurj
    (N : Subgroup G) [N.Normal] :
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
    (D.deckOrbitTowerFlattenFunctor (k := k) N).EssSurj := by
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
  constructor
  intro q
  let p := (MagnitudeConjecture.CoveringAction.orbitTowerEquiv N).symm
    (show MulAction.orbitRel.Quotient G C from q)
  refine ⟨(show DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N)
    from p), ?_⟩
  refine ⟨eqToIso ?_⟩
  rw [D.deckOrbitTowerFlattenFunctor_obj (k := k) N p]
  exact (MagnitudeConjecture.CoveringAction.orbitTowerEquiv N).apply_symm_apply _

/-- The two-stage strict orbit skeleton for `N` and `G / N` is equivalent to
the direct strict `G`-orbit skeleton. -/
noncomputable def deckOrbitTowerEquivalence
    (N : Subgroup G) [N.Normal] :
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
    DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N) ≌
      DeckOrbitSkeleton C G := by
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
  let F := D.deckOrbitTowerFlattenFunctor (k := k) N
  letI : F.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact F.asEquivalence
end MagnitudeConjecture.CoveringHom.CoherentDeckShift
