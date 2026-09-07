import MagnitudeConjecture.CategoryTheory.ShiftOrbitSubgroupResidualCommShift
import MagnitudeConjecture.LinearAlgebra.DirectSumFubini
import Mathlib.GroupTheory.Coset.Basic

/-!
# Linear Fubini equivalences for residual orbit flattening

For a normal subgroup `N ◁ G`, multiplication identifies `(G / N) × N`
with `G` after choosing the canonical quotient representatives.  This file
lifts that bijection to the homogeneous shifted Hom spaces and their
finite-support direct sums.  It also records the corresponding formula for
the actual residual flattening functor on a doubly homogeneous generator.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom
open MagnitudeConjecture.CoveringHom.CoherentDeckShift
open MagnitudeConjecture.DirectSumFubini

universe w

variable {G : Type w} [Group G]

noncomputable def normalQuotientSubgroupEquiv
    (N : Subgroup G) [N.Normal] : (G ⧸ N) × N ≃ G where
  toFun p := normalQuotientRepresentative N p.1 * (p.2 : G)
  invFun g :=
    ((g : G ⧸ N),
      ⟨(normalQuotientRepresentative N (g : G ⧸ N))⁻¹ * g,
        (QuotientGroup.eq_one_iff _).mp (by
          simp [normalQuotientRepresentative_mk])⟩)
  left_inv p := by
    apply Prod.ext
    · simp [normalQuotientRepresentative_mk]
    · apply Subtype.ext
      simp
  right_inv g := by
    simp

@[simp]
theorem normalQuotientSubgroupEquiv_apply
    (N : Subgroup G) [N.Normal] (q : G ⧸ N) (n : N) :
    normalQuotientSubgroupEquiv N (q, n) =
      normalQuotientRepresentative N q * (n : G) :=
  rfl

noncomputable def normalAdditiveQuotientSubgroupEquiv
    (N : Subgroup G) [N.Normal] :
    Additive (G ⧸ N) × Additive N ≃ Additive G :=
  (Equiv.prodCongr Additive.toMul Additive.toMul).trans
    ((normalQuotientSubgroupEquiv N).trans Additive.ofMul)

@[simp]
theorem normalAdditiveQuotientSubgroupEquiv_apply
    (N : Subgroup G) [N.Normal]
    (q : Additive (G ⧸ N)) (n : Additive N) :
    normalAdditiveQuotientSubgroupEquiv N (q, n) =
      Additive.ofMul
        (normalQuotientRepresentative N q.toMul * (n.toMul : G)) :=
  rfl

noncomputable def normalAdditiveQuotientSubgroupSigmaEquiv
    (N : Subgroup G) [N.Normal] :
    (Σ _q : Additive (G ⧸ N), Additive N) ≃ Additive G :=
  (Equiv.sigmaEquivProd (Additive (G ⧸ N)) (Additive N)).trans
    (normalAdditiveQuotientSubgroupEquiv N)

@[simp]
theorem normalAdditiveQuotientSubgroupSigmaEquiv_apply
    (N : Subgroup G) [N.Normal]
    (p : Σ _q : Additive (G ⧸ N), Additive N) :
    normalAdditiveQuotientSubgroupSigmaEquiv N p =
      normalAdditiveQuotientSubgroupEquiv N (p.1, p.2) :=
  rfl

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v uK

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

noncomputable def residualHomogeneousLinearEquiv
    (N : Subgroup G) [N.Normal]
    (q : Additive (G ⧸ N)) (n : Additive N) (X Y : C) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    ShiftHom X
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj Y) n ≃ₗ[k]
      ShiftHom X Y
        (normalAdditiveQuotientSubgroupSigmaEquiv N ⟨q, n⟩) := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  let a := Additive.ofMul (normalQuotientRepresentative N q.toMul)
  let b := Additive.ofMul (n.toMul : G)
  change
    (X ⟶ ((shiftFunctor C a ⋙ shiftFunctor C b).obj Y)) ≃ₗ[k]
      (X ⟶ (shiftFunctor C (a + b)).obj Y)
  let e := shiftFunctorAdd C a b
  exact
    { toFun := fun f ↦ f ≫ e.inv.app Y
      invFun := fun f ↦ f ≫ e.hom.app Y
      left_inv := by
        intro f
        change (f ≫ e.inv.app Y) ≫ e.hom.app Y = f
        rw [Category.assoc, e.inv_hom_id_app, Category.comp_id]
      right_inv := by
        intro f
        change (f ≫ e.hom.app Y) ≫ e.inv.app Y = f
        rw [Category.assoc, e.hom_inv_id_app, Category.comp_id]
      map_add' := by
        intro f g
        rw [Preadditive.add_comp]
      map_smul' := by
        intro r f
        rw [CategoryTheory.Linear.smul_comp, RingHom.id_apply] }

theorem shiftOrbitResidualFlattenFunctor_map_of_of
    (N : Subgroup G) [N.Normal]
    (q : Additive (G ⧸ N)) (n : Additive N) (X Y : C)
    (f : letI := D.hasShift
      letI := (D.restrict N).hasShift
      ShiftHom X
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj Y) n) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    (D.shiftOrbitResidualFlattenFunctor (k := k) N).map
        (shiftOrbitOf
          (show ShiftOrbitCategory C (Additive N) from X)
          (show ShiftOrbitCategory C (Additive N) from Y) q
          (shiftOrbitOf X
            ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N q.toMul))).obj Y) n f)) =
      shiftOrbitOf X Y (normalAdditiveQuotientSubgroupEquiv N (q, n))
        (D.residualHomogeneousLinearEquiv (k := k) N q n X Y f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  letI := trivialHasShift
    (ShiftOrbitCategory C (Additive G)) (Additive (G ⧸ N))
  letI := D.shiftOrbitSubgroupResidualCommShift N
  change (shiftOrbitDescendedFunctor (k := k)
      (A := Additive (G ⧸ N)) (D.shiftOrbitSubgroupFunctor N)).map _ = _
  rw [shiftOrbitDescendedFunctor_map_of]
  unfold shiftOrbitDescendHomogeneousMap
  rw [D.shiftOrbitSubgroupFunctor_map_eq]
  change D.shiftOrbitSubgroupMap N X
      ((shiftFunctor C (Additive.ofMul
        (normalQuotientRepresentative N q.toMul))).obj Y)
        (shiftOrbitOf X
          ((shiftFunctor C (Additive.ofMul
            (normalQuotientRepresentative N q.toMul))).obj Y) n f) ≫
      (ShiftOrbitCategory.objectShiftIso Y (Additive.ofMul
        (normalQuotientRepresentative N q.toMul))).inv = _
  rw [D.shiftOrbitSubgroupMap_of]
  change shiftOrbitCompHom
      (shiftOrbitOf X
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj Y)
        (Additive.ofMul (n.toMul : G)) f)
      (shiftOrbitFromShift Y (Additive.ofMul
        (normalQuotientRepresentative N q.toMul))) = _
  rw [shiftOrbitFromShift, shiftOrbitCompHom_of_of]
  simp [shiftHomComp, shiftHomComp',
    shiftFunctorAdd'_eq_shiftFunctorAdd]
  congr 1

noncomputable def residualFlattenUncurryLinearEquiv
    (N : Subgroup G) [N.Normal] (X Y : C) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    (DirectSum (Additive (G ⧸ N)) fun q ↦
      DirectSum (Additive N) fun n ↦
        ShiftHom X ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj Y) n) ≃ₗ[k]
      DirectSum (Σ _q : Additive (G ⧸ N), Additive N) fun p ↦
        ShiftHom X ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N p.1.toMul))).obj Y) p.2 := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  classical
  exact (DirectSum.sigmaLcurryEquiv k).symm

noncomputable def residualFlattenFiberwiseLinearEquiv
    (N : Subgroup G) [N.Normal] (X Y : C) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    (DirectSum (Σ _q : Additive (G ⧸ N), Additive N) fun p ↦
        ShiftHom X ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N p.1.toMul))).obj Y) p.2) ≃ₗ[k]
      DirectSum (Σ _q : Additive (G ⧸ N), Additive N) fun p ↦
        ShiftHom X Y (normalAdditiveQuotientSubgroupSigmaEquiv N p) := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  exact mapRangeLinearEquiv fun p ↦
    D.residualHomogeneousLinearEquiv (k := k) N p.1 p.2 X Y

noncomputable def residualFlattenDegreeLinearEquiv
    (N : Subgroup G) [N.Normal] (X Y : C) :
    letI := D.hasShift
    (DirectSum (Σ _q : Additive (G ⧸ N), Additive N) fun p ↦
      ShiftHom X Y (normalAdditiveQuotientSubgroupSigmaEquiv N p)) ≃ₗ[k]
      DirectSum (Additive G) fun g ↦ ShiftHom X Y g := by
  letI := D.hasShift
  classical
  let degreeEquiv := normalAdditiveQuotientSubgroupSigmaEquiv N
  exact (DirectSum.lequivCongrLeft k degreeEquiv).trans
    (mapRangeLinearEquiv fun g ↦
      LinearEquiv.cast (degreeEquiv.apply_symm_apply g))

noncomputable def residualFlattenDirectSumLinearEquiv
    (N : Subgroup G) [N.Normal] (X Y : C) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    (DirectSum (Additive (G ⧸ N)) fun q ↦
      DirectSum (Additive N) fun n ↦
        ShiftHom X ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj Y) n) ≃ₗ[k]
      DirectSum (Additive G) fun g ↦ ShiftHom X Y g := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  exact (D.residualFlattenUncurryLinearEquiv (k := k) N X Y).trans
    ((D.residualFlattenFiberwiseLinearEquiv (k := k) N X Y).trans
      (D.residualFlattenDegreeLinearEquiv (k := k) N X Y))

omit [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k] in
set_option backward.isDefEq.respectTransparency false in
theorem residualFlattenDirectSumLinearEquiv_of_of
    (N : Subgroup G) [N.Normal]
    (q : Additive (G ⧸ N)) (n : Additive N) (X Y : C)
    (f : letI := D.hasShift
      letI := (D.restrict N).hasShift
      ShiftHom X
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj Y) n) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    letI : DecidableEq G := Classical.decEq _
    letI : DecidablePred (fun g : G ↦ g ∈ N) := Classical.decPred _
    D.residualFlattenDirectSumLinearEquiv (k := k) N X Y
        (DirectSum.of
          (fun q ↦ DirectSum (Additive N) fun n ↦
            ShiftHom X ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N q.toMul))).obj Y) n)
          q
          (DirectSum.of
            (fun n ↦ ShiftHom X
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj Y) n)
            n f)) =
      DirectSum.of (fun g : Additive G ↦ ShiftHom X Y g)
        (normalAdditiveQuotientSubgroupSigmaEquiv N ⟨q, n⟩)
        (D.residualHomogeneousLinearEquiv (k := k) N q n X Y f) := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  letI : DecidableEq G := Classical.decEq _
  letI : DecidablePred (fun g : G ↦ g ∈ N) := Classical.decPred _
  unfold residualFlattenDirectSumLinearEquiv
    residualFlattenUncurryLinearEquiv
    residualFlattenFiberwiseLinearEquiv
    residualFlattenDegreeLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [sigmaLcurryEquiv_symm_of_of,
    mapRangeLinearEquiv_of,
    reindexCastLinearEquiv_of]

noncomputable def shiftOrbitResidualFlattenHomLinearEquiv
    (N : Subgroup G) [N.Normal] (X Y : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    ((show ShiftOrbitCategory
        (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from
          (show ShiftOrbitCategory C (Additive N) from X)) ⟶
        (show ShiftOrbitCategory
          (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from
            (show ShiftOrbitCategory C (Additive N) from Y)) :
      Type _) ≃ₗ[k]
      ((show ShiftOrbitCategory C (Additive G) from X) ⟶
        (show ShiftOrbitCategory C (Additive G) from Y) : Type _) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  change
    (DirectSum (Additive (G ⧸ N)) fun q ↦
      DirectSum (Additive N) fun n ↦
        ShiftHom X ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj Y) n) ≃ₗ[k]
      DirectSum (Additive G) fun g ↦ ShiftHom X Y g
  exact D.residualFlattenDirectSumLinearEquiv (k := k) N X Y

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The Fubini equivalence on residual-orbit Hom spaces is the linear map of
the actual residual flattening functor. -/
theorem shiftOrbitResidualFlattenHomLinearEquiv_toLinearMap
    (N : Subgroup G) [N.Normal] (X Y : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    (D.shiftOrbitResidualFlattenHomLinearEquiv
      (k := k) N X Y).toLinearMap =
      (D.shiftOrbitResidualFlattenFunctor (k := k) N).mapLinearMap
        (X := (show ShiftOrbitCategory
          (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from X))
        (Y := (show ShiftOrbitCategory
          (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from Y)) k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  classical
  let Source := DirectSum (Additive (G ⧸ N)) fun q ↦
    DirectSum (Additive N) fun n ↦
      ShiftHom X ((shiftFunctor C (Additive.ofMul
        (normalQuotientRepresentative N q.toMul))).obj Y) n
  let Target := DirectSum (Additive G) fun g ↦ ShiftHom X Y g
  let eL : Source →ₗ[k] Target :=
    (D.residualFlattenDirectSumLinearEquiv (k := k) N X Y).toLinearMap
  let mapL : Source →ₗ[k] Target :=
    (D.shiftOrbitResidualFlattenFunctor (k := k) N).mapLinearMap
      (X := (show ShiftOrbitCategory
        (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from X))
      (Y := (show ShiftOrbitCategory
        (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from Y)) k
  change eL = mapL
  apply LinearMap.ext
  intro f
  refine DirectSum.induction_on f ?_ ?_ ?_
  · exact eL.map_zero.trans mapL.map_zero.symm
  · intro q fq
    refine DirectSum.induction_on fq ?_ ?_ ?_
    · rw [map_zero]
      exact eL.map_zero.trans mapL.map_zero.symm
    · intro n fn
      trans DirectSum.of (fun g : Additive G ↦ ShiftHom X Y g)
        (normalAdditiveQuotientSubgroupSigmaEquiv N ⟨q, n⟩)
        (D.residualHomogeneousLinearEquiv (k := k) N q n X Y fn)
      · dsimp only [eL, Source, Target]
        exact D.residualFlattenDirectSumLinearEquiv_of_of
          (k := k) N q n X Y fn
      · let explicitGen : Source :=
          DirectSum.of
            (fun q ↦ DirectSum (Additive N) fun n ↦
              ShiftHom X ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj Y) n)
            q
            (DirectSum.of
              (fun n ↦ ShiftHom X
                ((shiftFunctor C (Additive.ofMul
                  (normalQuotientRepresentative N q.toMul))).obj Y) n)
              n fn)
        let outerGen : Source :=
          shiftOrbitOf
            (show ShiftOrbitCategory C (Additive N) from X)
            (show ShiftOrbitCategory C (Additive N) from Y) q
            (shiftOrbitOf X
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj Y) n fn)
        have hgen : explicitGen = outerGen := by
          dsimp only [explicitGen, outerGen, Source]
          rw [shiftOrbitOf_eq_directSumOf, shiftOrbitOf_eq_directSumOf]
          have hfamily :
              (fun c : Additive (G ⧸ N) ↦ ShiftHom
                (show ShiftOrbitCategory C (Additive N) from X)
                (show ShiftOrbitCategory C (Additive N) from Y) c) =
                (fun q ↦ DirectSum (Additive N) fun n ↦
                  ShiftHom X ((shiftFunctor C (Additive.ofMul
                    (normalQuotientRepresentative N q.toMul))).obj Y) n) := by
            rfl
          cases hfamily
          rfl
        change _ = mapL explicitGen
        rw [hgen]
        dsimp only [mapL, outerGen]
        change _ = (D.shiftOrbitResidualFlattenFunctor (k := k) N).map
          (shiftOrbitOf
            (show ShiftOrbitCategory C (Additive N) from X)
            (show ShiftOrbitCategory C (Additive N) from Y) q
            (shiftOrbitOf X
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj Y) n fn))
        rw [D.shiftOrbitResidualFlattenFunctor_map_of_of]
        rfl
    · intro a b ha hb
      rw [map_add, eL.map_add, mapL.map_add, ha, hb]
  · intro a b ha hb
    rw [eL.map_add, mapL.map_add, ha, hb]

/-- Residual orbit flattening is bijective on every Hom space. -/
theorem shiftOrbitResidualFlattenFunctor_map_bijective
    (N : Subgroup G) [N.Normal] (X Y : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    Function.Bijective
      ((D.shiftOrbitResidualFlattenFunctor (k := k) N).map :
        ((show ShiftOrbitCategory
          (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from X) ⟶
        (show ShiftOrbitCategory
          (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from Y)) →
        ((show ShiftOrbitCategory C (Additive G) from X) ⟶
          (show ShiftOrbitCategory C (Additive G) from Y))) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  let e := D.shiftOrbitResidualFlattenHomLinearEquiv (k := k) N X Y
  have he := D.shiftOrbitResidualFlattenHomLinearEquiv_toLinearMap
    (k := k) N X Y
  constructor
  · intro f g hfg
    apply e.injective
    change e.toLinearMap f = e.toLinearMap g
    rw [he]
    exact hfg
  · intro h
    obtain ⟨f, hf⟩ := e.surjective h
    refine ⟨f, ?_⟩
    change (D.shiftOrbitResidualFlattenFunctor
      (k := k) N).mapLinearMap k f = h
    rw [← he]
    exact hf

/-- Residual orbit flattening is full. -/
instance shiftOrbitResidualFlattenFunctor_full
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
    (D.shiftOrbitResidualFlattenFunctor (k := k) N).Full := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  exact { map_surjective := fun {X Y} ↦
    (D.shiftOrbitResidualFlattenFunctor_map_bijective
      (k := k) N (show C from X) (show C from Y)).surjective }

/-- Residual orbit flattening is faithful. -/
instance shiftOrbitResidualFlattenFunctor_faithful
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
    (D.shiftOrbitResidualFlattenFunctor (k := k) N).Faithful := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  exact { map_injective := fun {X Y} ↦
    (D.shiftOrbitResidualFlattenFunctor_map_bijective
      (k := k) N (show C from X) (show C from Y)).injective }

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
