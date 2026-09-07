import MagnitudeConjecture.CategoryTheory.ShiftOrbitResidualFlattenLinearEquiv
import MagnitudeConjecture.CategoryTheory.OrbitPushdown

/-!
# Natural Fubini isomorphism for residual orbit push-down

For a normal subgroup `N ◁ G`, the iterated `N`- and `G / N`-indexed
push-down value is linearly equivalent to the direct `G`-indexed push-down
value.  The equivalence uses the canonical quotient representative and the
coherent addition isomorphism for deck shifts.  Its compatibility with
homogeneous orbit arrows extends linearly to a natural isomorphism of module
functors.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open MagnitudeConjecture.CoveringHom
open MagnitudeConjecture.DirectSumFubini

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [CommRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable {G : Type w} [Group G] [MulAction G C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]
variable (M : C ⥤ ModuleCat.{uM} k) [M.Additive] [M.Linear k]

/-- Include the `n`-summand of subgroup push-down into the corresponding
ambient-group summand. -/
noncomputable def subgroupOrbitPushdownValueInclusionSummand
    (N : Subgroup G) (X : C) (n : Additive N) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    M.obj ((shiftFunctor C n).obj X) →ₗ[k]
      orbitPushdownValue (A := Additive G) M X := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  change M.obj ((shiftFunctor C
      (Additive.ofMul (n.toMul : G))).obj X) →ₗ[k] _
  exact orbitPushdownLof M X (Additive.ofMul (n.toMul : G))

/-- Extension by zero includes subgroup-indexed push-down values into the
ambient-group push-down. -/
noncomputable def subgroupOrbitPushdownValueInclusion
    (N : Subgroup G) (X : C) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    orbitPushdownValue (A := Additive N) M X →ₗ[k]
      orbitPushdownValue (A := Additive G) M X := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  classical
  exact DirectSum.toModule k (Additive N) _ fun n ↦
    D.subgroupOrbitPushdownValueInclusionSummand M N X n

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k]
  [M.Additive] [M.Linear k] in
@[simp]
theorem subgroupOrbitPushdownValueInclusion_lof
    (N : Subgroup G) (X : C) (n : Additive N)
    (x : letI := D.hasShift
      letI := (D.restrict N).hasShift
      M.obj ((shiftFunctor C n).obj X)) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    D.subgroupOrbitPushdownValueInclusion M N X
        (orbitPushdownLof M X n x) =
      orbitPushdownLof M X (Additive.ofMul (n.toMul : G)) x := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  classical
  unfold subgroupOrbitPushdownValueInclusion
  change (DirectSum.toModule k (Additive N) _
      (fun a ↦ D.subgroupOrbitPushdownValueInclusionSummand M N X a))
        (orbitPushdownLof M X n x) =
      D.subgroupOrbitPushdownValueInclusionSummand M N X n x
  rw [orbitPushdownLof_eq_directSumOf M X n x]
  rw [← DirectSum.lof_eq_of k (Additive N)
    (fun a : Additive N ↦ M.obj ((shiftFunctor C a).obj X)) n x]
  exact DirectSum.toModule_lof (R := k)
    (M := fun a : Additive N ↦ M.obj ((shiftFunctor C a).obj X))
    (N := orbitPushdownValue (A := Additive G) M X)
    (φ := fun a ↦
      D.subgroupOrbitPushdownValueInclusionSummand M N X a) n x

set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero on push-down values is natural for every subgroup
orbit morphism. -/
theorem subgroupOrbitPushdownValueInclusion_naturality
    (N : Subgroup G) (X Y : C)
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      ShiftOrbitHom (Additive N) X Y) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    (D.subgroupOrbitPushdownValueInclusion M N Y).comp
        (orbitPushdownMapLinear M f) =
      (orbitPushdownMapLinear M
        (D.shiftOrbitSubgroupMap N X Y f)).comp
          (D.subgroupOrbitPushdownValueInclusion M N X) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  classical
  refine DirectSum.induction_on f ?_ ?_ ?_
  · ext z
    simp
  · intro a fa
    have hfa :
        DirectSum.of (fun c : Additive N ↦ ShiftHom X Y c) a fa =
          shiftOrbitOf X Y a fa :=
      (shiftOrbitOf_eq_directSumOf X Y a fa).symm
    rw [hfa]
    rw [orbitPushdownMapLinear_of, D.shiftOrbitSubgroupMap_of,
      orbitPushdownMapLinear_of]
    apply DirectSum.linearMap_ext
    intro b
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    change D.subgroupOrbitPushdownValueInclusion M N Y
        (orbitPushdownHomogeneousMap M a fa
          ((DirectSum.lof k (Additive N)
            (fun i ↦ M.obj ((shiftFunctor C i).obj X)) b) x)) = _
    rw [DirectSum.lof_eq_of,
      ← orbitPushdownLof_eq_directSumOf M X b x]
    rw [orbitPushdownHomogeneousMap_lof,
      subgroupOrbitPushdownValueInclusion_lof,
      subgroupOrbitPushdownValueInclusion_lof,
      orbitPushdownHomogeneousMap_lof]
    rfl
  · intro f g hf hg
    rw [map_add, map_add, map_add]
    apply LinearMap.ext
    intro x
    simpa using congrArg₂ (.+.)
      (LinearMap.congr_fun hf x) (LinearMap.congr_fun hg x)

noncomputable def residualPushdownHomogeneousLinearEquiv
    (N : Subgroup G) [N.Normal]
    (q : Additive (G ⧸ N)) (n : Additive N) (X : C) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    M.obj ((shiftFunctor C n).obj
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj X)) ≃ₗ[k]
      M.obj ((shiftFunctor C
        (normalAdditiveQuotientSubgroupEquiv N (q, n))).obj X) := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  let a := Additive.ofMul (normalQuotientRepresentative N q.toMul)
  let b := Additive.ofMul (n.toMul : G)
  change M.obj ((shiftFunctor C b).obj ((shiftFunctor C a).obj X)) ≃ₗ[k]
    M.obj ((shiftFunctor C (a + b)).obj X)
  exact (M.mapIso ((shiftFunctorAdd C a b).symm.app X)).toLinearEquiv

noncomputable def residualOrbitPushdownValueLinearEquiv
    (N : Subgroup G) [N.Normal] (X : C) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    (DirectSum (Additive (G ⧸ N)) fun q ↦
      DirectSum (Additive N) fun n ↦
        M.obj ((shiftFunctor C n).obj
          ((shiftFunctor C (Additive.ofMul
            (normalQuotientRepresentative N q.toMul))).obj X))) ≃ₗ[k]
      DirectSum (Additive G) fun g ↦
        M.obj ((shiftFunctor C g).obj X) := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  classical
  let degreeEquiv := normalAdditiveQuotientSubgroupSigmaEquiv N
  let flatten :
      (DirectSum (Additive (G ⧸ N)) fun q ↦
        DirectSum (Additive N) fun n ↦
          M.obj ((shiftFunctor C n).obj
            ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N q.toMul))).obj X))) ≃ₗ[k]
        DirectSum (Σ _q : Additive (G ⧸ N), Additive N) fun p ↦
          M.obj ((shiftFunctor C p.2).obj
            ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N p.1.toMul))).obj X)) :=
    (DirectSum.sigmaLcurryEquiv k).symm
  let mapFibers :
      (DirectSum (Σ _q : Additive (G ⧸ N), Additive N) fun p ↦
        M.obj ((shiftFunctor C p.2).obj
          ((shiftFunctor C (Additive.ofMul
            (normalQuotientRepresentative N p.1.toMul))).obj X))) ≃ₗ[k]
        DirectSum (Σ _q : Additive (G ⧸ N), Additive N) fun p ↦
          M.obj ((shiftFunctor C (degreeEquiv p)).obj X) :=
    mapRangeLinearEquiv fun p ↦
      D.residualPushdownHomogeneousLinearEquiv (M := M) N p.1 p.2 X
  let reindex :
      (DirectSum (Σ _q : Additive (G ⧸ N), Additive N) fun p ↦
        M.obj ((shiftFunctor C (degreeEquiv p)).obj X)) ≃ₗ[k]
        DirectSum (Additive G) fun g ↦
          M.obj ((shiftFunctor C
            (degreeEquiv (degreeEquiv.symm g))).obj X) :=
    DirectSum.lequivCongrLeft k degreeEquiv
  let castFibers :
      (DirectSum (Additive G) fun g ↦
        M.obj ((shiftFunctor C
          (degreeEquiv (degreeEquiv.symm g))).obj X)) ≃ₗ[k]
        DirectSum (Additive G) fun g ↦
          M.obj ((shiftFunctor C g).obj X) :=
    mapRangeLinearEquiv fun g ↦
      LinearEquiv.cast (R := k)
        (M := fun g : Additive G ↦ M.obj ((shiftFunctor C g).obj X))
        (degreeEquiv.apply_symm_apply g)
  exact ((flatten.trans mapFibers).trans reindex).trans castFibers

omit [Preadditive C] [CategoryTheory.Linear k C]
  [∀ a : Additive G, (D.core.F a).Additive]
  [∀ a : Additive G, (D.core.F a).Linear k]
  [M.Additive] [M.Linear k] in
set_option backward.isDefEq.respectTransparency false in
theorem residualOrbitPushdownValueLinearEquiv_of_of
    (N : Subgroup G) [N.Normal]
    (q : Additive (G ⧸ N)) (n : Additive N) (X : C)
    (x : letI := D.hasShift
      letI := (D.restrict N).hasShift
      M.obj ((shiftFunctor C n).obj
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj X))) :
    letI := D.hasShift
    letI := (D.restrict N).hasShift
    letI : DecidableEq G := Classical.decEq _
    letI : DecidablePred (fun g : G ↦ g ∈ N) := Classical.decPred _
    D.residualOrbitPushdownValueLinearEquiv (M := M) N X
        (DirectSum.of
          (fun q ↦ DirectSum (Additive N) fun n ↦
            M.obj ((shiftFunctor C n).obj
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj X)))
          q
          (DirectSum.of
            (fun n ↦ M.obj ((shiftFunctor C n).obj
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj X)))
            n x)) =
      DirectSum.of
        (fun g : Additive G ↦ M.obj ((shiftFunctor C g).obj X))
        (normalAdditiveQuotientSubgroupSigmaEquiv N ⟨q, n⟩)
        (D.residualPushdownHomogeneousLinearEquiv
          (M := M) N q n X x) := by
  letI := D.hasShift
  letI := (D.restrict N).hasShift
  letI : DecidableEq G := Classical.decEq _
  letI : DecidablePred (fun g : G ↦ g ∈ N) := Classical.decPred _
  unfold residualOrbitPushdownValueLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [sigmaLcurryEquiv_symm_of_of,
    mapRangeLinearEquiv_of,
    reindexCastLinearEquiv_of]
  rfl

noncomputable def orbitPushdownResidualFubiniLinearEquiv
    (N : Subgroup G) [N.Normal] (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    orbitPushdownValue (A := Additive (G ⧸ N))
        (orbitPushdown (A := Additive N) M) (show ShiftOrbitCategory C (Additive N) from X) ≃ₗ[k]
      orbitPushdownValue (A := Additive G) M X := by
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
        M.obj ((shiftFunctor C n).obj
          ((shiftFunctor C (Additive.ofMul
            (normalQuotientRepresentative N q.toMul))).obj X))) ≃ₗ[k]
      DirectSum (Additive G) fun g ↦
        M.obj ((shiftFunctor C g).obj X)
  exact D.residualOrbitPushdownValueLinearEquiv (M := M) N X

noncomputable def orbitPushdownResidualFubiniIsoApp
    (N : Subgroup G) [N.Normal] (X : C) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    (orbitPushdown (A := Additive (G ⧸ N))
        (orbitPushdown (A := Additive N) M)).obj
      (show ShiftOrbitCategory
        (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from
          (show ShiftOrbitCategory C (Additive N) from X)) ≅
    ((D.shiftOrbitResidualFlattenFunctor (k := k) N) ⋙
        orbitPushdown (A := Additive G) M).obj
      (show ShiftOrbitCategory
        (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from
          (show ShiftOrbitCategory C (Additive N) from X)) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  change ModuleCat.of k
      (orbitPushdownValue (A := Additive (G ⧸ N))
        (orbitPushdown (A := Additive N) M)
          (show ShiftOrbitCategory C (Additive N) from X)) ≅
    ModuleCat.of k (orbitPushdownValue (A := Additive G) M X)
  exact (D.orbitPushdownResidualFubiniLinearEquiv (M := M) N X).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- On one quotient-degree summand, the residual Fubini equivalence is
extension by zero followed by the canonical path from the chosen quotient
translate. -/
theorem orbitPushdownResidualFubini_factor
    (N : Subgroup G) [N.Normal]
    (q : Additive (G ⧸ N)) (X : C)
    (z : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      orbitPushdownValue (A := Additive N) M
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj X)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    D.orbitPushdownResidualFubiniLinearEquiv (M := M) N X
        (orbitPushdownLof (orbitPushdown (A := Additive N) M)
          (show ShiftOrbitCategory C (Additive N) from X) q z) =
      orbitPushdownMapLinear M
          (shiftOrbitFromShift X (Additive.ofMul
            (normalQuotientRepresentative N q.toMul)))
        (D.subgroupOrbitPushdownValueInclusion M N
          ((shiftFunctor C (Additive.ofMul
            (normalQuotientRepresentative N q.toMul))).obj X) z) := by
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
  refine DirectSum.induction_on z ?_ ?_ ?_
  · simp
  · intro m xm
    have hz :
        DirectSum.of
            (fun m : Additive N ↦ M.obj ((shiftFunctor C m).obj
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj X)))
            m xm =
          orbitPushdownLof M
            ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N q.toMul))).obj X) m xm :=
      (orbitPushdownLof_eq_directSumOf M _ m xm).symm
    rw [hz]
    let explicitInput := DirectSum.of
      (fun r : Additive (G ⧸ N) ↦
        DirectSum (Additive N) fun m ↦
          M.obj ((shiftFunctor C m).obj
            ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N r.toMul))).obj X))) q
      (DirectSum.of
        (fun m : Additive N ↦ M.obj ((shiftFunctor C m).obj
          ((shiftFunctor C (Additive.ofMul
            (normalQuotientRepresentative N q.toMul))).obj X))) m xm)
    have hinput : explicitInput =
        orbitPushdownLof (orbitPushdown (A := Additive N) M)
          (show ShiftOrbitCategory C (Additive N) from X) q
          (orbitPushdownLof M
            ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N q.toMul))).obj X) m xm) := by
      dsimp only [explicitInput]
      rw [orbitPushdownLof_eq_directSumOf,
        orbitPushdownLof_eq_directSumOf]
      have hfamily :
          (fun r : Additive (G ⧸ N) ↦
            orbitPushdownValue (A := Additive N) M
              (show ShiftOrbitCategory C (Additive N) from
                (shiftFunctor C (Additive.ofMul
                  (normalQuotientRepresentative N r.toMul))).obj X)) =
            (fun r : Additive (G ⧸ N) ↦
              DirectSum (Additive N) fun m ↦
                M.obj ((shiftFunctor C m).obj
                  ((shiftFunctor C (Additive.ofMul
                    (normalQuotientRepresentative N r.toMul))).obj X))) := by
        rfl
      cases hfamily
      rfl
    rw [← hinput]
    change D.residualOrbitPushdownValueLinearEquiv
        (M := M) N X explicitInput = _
    rw [D.residualOrbitPushdownValueLinearEquiv_of_of]
    rw [subgroupOrbitPushdownValueInclusion_lof]
    rw [shiftOrbitFromShift, orbitPushdownMapLinear_of,
      orbitPushdownHomogeneousMap_lof]
    apply DFinsupp.single_eq_of_sigma_eq
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      unfold orbitPushdownComponent orbitPushdownComponent'
        residualPushdownHomogeneousLinearEquiv
      dsimp only [LinearEquiv.coe_coe, Functor.mapIso_hom]
      simp [orbitPushdownArrow', shiftFunctorAdd'_eq_shiftFunctorAdd]
      rfl
  · intro z₁ z₂ hz₁ hz₂
    simpa only [map_add] using congrArg₂ (.+.) hz₁ hz₂

set_option backward.isDefEq.respectTransparency false in
/-- Flattening transports the canonical two-stage component path to the
corresponding one-stage path in the ambient orbit category. -/
theorem shiftOrbitResidualFlatten_path
    (N : Subgroup G) [N.Normal]
    (q r : Additive (G ⧸ N)) (n : Additive N) (X Y : C)
    (fn : letI := D.hasShift
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
    shiftOrbitCompHom (D.shiftOrbitSubgroupMap N _ _
          (orbitPushdownArrow'
            (C := ShiftOrbitCategory C (Additive N))
            (A := Additive (G ⧸ N))
            (rfl : q + r = q + r)
            (shiftOrbitOf X
              ((shiftFunctor C (Additive.ofMul
                (normalQuotientRepresentative N q.toMul))).obj Y) n fn)))
        (shiftOrbitFromShift Y
          (Additive.ofMul
            (normalQuotientRepresentative N (q + r).toMul))) =
      shiftOrbitCompHom
        (shiftOrbitFromShift X
          (Additive.ofMul
            (normalQuotientRepresentative N r.toMul)))
        (shiftOrbitOf X Y
          (normalAdditiveQuotientSubgroupEquiv N (q, n))
          (D.residualHomogeneousLinearEquiv
            (k := k) N q n X Y fn)) := by
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
  let F := D.shiftOrbitSubgroupFunctor N
  let flatten := D.shiftOrbitResidualFlattenFunctor (k := k) N
  let innerGen := shiftOrbitOf X
    ((shiftFunctor C (Additive.ofMul
      (normalQuotientRepresentative N q.toMul))).obj Y) n fn
  let outerGen := shiftOrbitOf
    (show ShiftOrbitCategory C (Additive N) from X)
    (show ShiftOrbitCategory C (Additive N) from Y) q innerGen
  let houter := orbitPushdownArrow'
    (C := ShiftOrbitCategory C (Additive N))
    (A := Additive (G ⧸ N))
    (rfl : q + r = q + r) innerGen
  have hpath := orbitPushdownArrow_comp_fromShift
    (C := ShiftOrbitCategory C (Additive N)) q r innerGen
  have hpath' :
      (ShiftOrbitCategory.identityComponentFunctor
            (C := ShiftOrbitCategory C (Additive N))
            (A := Additive (G ⧸ N))).map houter ≫
          shiftOrbitFromShift
            (show ShiftOrbitCategory C (Additive N) from Y) (q + r) =
        shiftOrbitFromShift
            (show ShiftOrbitCategory C (Additive N) from X) r ≫
          outerGen := by
    exact hpath
  have hmapped := congrArg (fun h ↦ flatten.map h) hpath'
  rw [flatten.map_comp, flatten.map_comp] at hmapped
  rw [show flatten = shiftOrbitDescendedFunctor
      (k := k) (A := Additive (G ⧸ N)) F by rfl,
    shiftOrbitDescendedFunctor_map_identityComponent,
    shiftOrbitDescendedFunctor_map_fromShift,
    shiftOrbitDescendedFunctor_map_fromShift] at hmapped
  change shiftOrbitCompHom
      (D.shiftOrbitSubgroupMap N _ _ houter)
        ((D.shiftOrbitSubgroupResidualCommShiftIso N (q + r)).hom.app Y) =
    shiftOrbitCompHom
      ((D.shiftOrbitSubgroupResidualCommShiftIso N r).hom.app X)
        (flatten.map outerGen) at hmapped
  dsimp only [shiftOrbitSubgroupResidualCommShiftIso] at hmapped
  change shiftOrbitCompHom
      (D.shiftOrbitSubgroupMap N _ _ houter)
        (shiftOrbitFromShift Y (Additive.ofMul
          (normalQuotientRepresentative N (q + r).toMul))) =
    shiftOrbitCompHom
      (shiftOrbitFromShift X (Additive.ofMul
        (normalQuotientRepresentative N r.toMul)))
      (flatten.map outerGen) at hmapped
  dsimp only [flatten, outerGen, innerGen] at hmapped
  rw [D.shiftOrbitResidualFlattenFunctor_map_of_of] at hmapped
  dsimp only [flatten, outerGen, innerGen, houter]
  exact hmapped

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem orbitPushdownResidualFubini_naturality_of_of_apply
    (N : Subgroup G) [N.Normal]
    (q r : Additive (G ⧸ N)) (n : Additive N) (X Y : C)
    (fn : letI := D.hasShift
      letI := (D.restrict N).hasShift
      ShiftHom X
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj Y) n)
    (z : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      letI := D.shiftOrbitResidualHasShift N
      letI := D.shiftOrbitResidualAdditiveShift N
      letI := D.shiftOrbitResidualLinearShift (k := k) N
      (orbitPushdown (A := Additive N) M).obj
        ((shiftFunctor (ShiftOrbitCategory C (Additive N)) r).obj
          (show ShiftOrbitCategory C (Additive N) from X))) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    let innerGen := shiftOrbitOf X
      ((shiftFunctor C (Additive.ofMul
        (normalQuotientRepresentative N q.toMul))).obj Y) n fn
    D.orbitPushdownResidualFubiniLinearEquiv (M := M) N Y
        (orbitPushdownHomogeneousMap
          (orbitPushdown (A := Additive N) M) q innerGen
            (orbitPushdownLof (orbitPushdown (A := Additive N) M)
              (show ShiftOrbitCategory C (Additive N) from X) r z)) =
      orbitPushdownMapLinear M
        (shiftOrbitOf X Y
          (normalAdditiveQuotientSubgroupEquiv N (q, n))
          (D.residualHomogeneousLinearEquiv
            (k := k) N q n X Y fn))
        (D.orbitPushdownResidualFubiniLinearEquiv (M := M) N X
          (orbitPushdownLof (orbitPushdown (A := Additive N) M)
            (show ShiftOrbitCategory C (Additive N) from X) r z)) := by
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
  dsimp only
  rw [orbitPushdownHomogeneousMap_lof,
    D.orbitPushdownResidualFubini_factor,
    D.orbitPushdownResidualFubini_factor]
  let innerGen := shiftOrbitOf X
    ((shiftFunctor C (Additive.ofMul
      (normalQuotientRepresentative N q.toMul))).obj Y) n fn
  let houter := orbitPushdownArrow'
    (C := ShiftOrbitCategory C (Additive N))
    (A := Additive (G ⧸ N))
    (rfl : q + r = q + r) innerGen
  let includeX := D.subgroupOrbitPushdownValueInclusion M N
    ((shiftFunctor C (Additive.ofMul
      (normalQuotientRepresentative N r.toMul))).obj X)
  have hincl := LinearMap.congr_fun
    (D.subgroupOrbitPushdownValueInclusion_naturality
      M N _ _ houter) z
  simp only [LinearMap.comp_apply] at hincl
  change D.subgroupOrbitPushdownValueInclusion M N
      ((shiftFunctor C (Additive.ofMul
        (normalQuotientRepresentative N (q + r).toMul))).obj Y)
        (orbitPushdownMapLinear M houter z) =
    orbitPushdownMapLinear M
      (D.shiftOrbitSubgroupMap N
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N r.toMul))).obj X)
        ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N (q + r).toMul))).obj Y)
        houter) (includeX z) at hincl
  change orbitPushdownMapLinear M
      (shiftOrbitFromShift Y (Additive.ofMul
        (normalQuotientRepresentative N (q + r).toMul)))
      (D.subgroupOrbitPushdownValueInclusion M N _
        (orbitPushdownMapLinear M houter z)) =
    orbitPushdownMapLinear M
      (shiftOrbitOf X Y
        (normalAdditiveQuotientSubgroupEquiv N (q, n))
        (D.residualHomogeneousLinearEquiv
          (k := k) N q n X Y fn))
      (orbitPushdownMapLinear M
        (shiftOrbitFromShift X (Additive.ofMul
          (normalQuotientRepresentative N r.toMul)))
        (includeX z))
  rw [hincl]
  let subgroupPath := D.shiftOrbitSubgroupMap N _ _ houter
  let quotientPathY := shiftOrbitFromShift Y (Additive.ofMul
    (normalQuotientRepresentative N (q + r).toMul))
  let quotientPathX := shiftOrbitFromShift X (Additive.ofMul
    (normalQuotientRepresentative N r.toMul))
  let targetGen := shiftOrbitOf X Y
    (normalAdditiveQuotientSubgroupEquiv N (q, n))
    (D.residualHomogeneousLinearEquiv (k := k) N q n X Y fn)
  calc
    orbitPushdownMapLinear M quotientPathY
        (orbitPushdownMapLinear M subgroupPath (includeX z)) =
      orbitPushdownMapLinear M
        (shiftOrbitCompHom subgroupPath quotientPathY) (includeX z) := by
          rw [orbitPushdownMapLinear_comp]
          rfl
    _ = orbitPushdownMapLinear M
        (shiftOrbitCompHom quotientPathX targetGen) (includeX z) := by
          rw [D.shiftOrbitResidualFlatten_path (k := k) N q r n X Y fn]
          rfl
    _ = orbitPushdownMapLinear M targetGen
        (orbitPushdownMapLinear M quotientPathX (includeX z)) := by
          rw [orbitPushdownMapLinear_comp]
          rfl

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem orbitPushdownResidualFubini_naturality_of_of
    (N : Subgroup G) [N.Normal]
    (q : Additive (G ⧸ N)) (n : Additive N) (X Y : C)
    (fn : letI := D.hasShift
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
    let innerGen := shiftOrbitOf X
      ((shiftFunctor C (Additive.ofMul
        (normalQuotientRepresentative N q.toMul))).obj Y) n fn
    (D.orbitPushdownResidualFubiniLinearEquiv
      (M := M) N Y).toLinearMap.comp
        (orbitPushdownHomogeneousMap
          (orbitPushdown (A := Additive N) M) q innerGen) =
      (orbitPushdownMapLinear M
        (shiftOrbitOf X Y
          (normalAdditiveQuotientSubgroupEquiv N (q, n))
          (D.residualHomogeneousLinearEquiv
            (k := k) N q n X Y fn))).comp
        (D.orbitPushdownResidualFubiniLinearEquiv
          (M := M) N X).toLinearMap := by
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
  dsimp only
  apply DirectSum.linearMap_ext
  intro r
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [DirectSum.lof_eq_of,
    ← orbitPushdownLof_eq_directSumOf
      (orbitPushdown (A := Additive N) M)
        (show ShiftOrbitCategory C (Additive N) from X) r z]
  exact D.orbitPushdownResidualFubini_naturality_of_of_apply
    M N q r n X Y fn z

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem orbitPushdownResidualFubini_naturalityLinearMap
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
    let Source := DirectSum (Additive (G ⧸ N)) fun q ↦
      DirectSum (Additive N) fun n ↦
        ShiftHom X ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj Y) n
    let IteratedX := orbitPushdownValue (A := Additive (G ⧸ N))
      (orbitPushdown (A := Additive N) M)
        (show ShiftOrbitCategory C (Additive N) from X)
    let DirectY := orbitPushdownValue (A := Additive G) M Y
    let left : Source →ₗ[k] (IteratedX →ₗ[k] DirectY) :=
      { toFun := fun f ↦
          (D.orbitPushdownResidualFubiniLinearEquiv
            (M := M) N Y).toLinearMap.comp
              (orbitPushdownMapLinear
                (orbitPushdown (A := Additive N) M) f)
        map_add' := by
          intro f g
          apply LinearMap.ext
          intro z
          simp
        map_smul' := by
          intro r f
          apply LinearMap.ext
          intro z
          simp }
    let flattenL : Source →ₗ[k] ShiftOrbitHom (Additive G) X Y :=
      (D.shiftOrbitResidualFlattenFunctor (k := k) N).mapLinearMap k
    let right : Source →ₗ[k] (IteratedX →ₗ[k] DirectY) :=
      { toFun := fun f ↦
          (orbitPushdownMapLinear M (flattenL f)).comp
            (D.orbitPushdownResidualFubiniLinearEquiv
              (M := M) N X).toLinearMap
        map_add' := by
          intro f g
          apply LinearMap.ext
          intro z
          simp [flattenL]
        map_smul' := by
          intro r f
          apply LinearMap.ext
          intro z
          simp [flattenL] }
    left = right := by
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
  dsimp only
  apply DirectSum.linearMap_ext
  intro q
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro fn
  simp only [LinearMap.comp_apply]
  let innerGen := shiftOrbitOf X
    ((shiftFunctor C (Additive.ofMul
      (normalQuotientRepresentative N q.toMul))).obj Y) n fn
  let outerGen := shiftOrbitOf
    (show ShiftOrbitCategory C (Additive N) from X)
    (show ShiftOrbitCategory C (Additive N) from Y) q innerGen
  let explicitGen := DirectSum.of
    (fun r : Additive (G ⧸ N) ↦
      DirectSum (Additive N) fun m ↦
        ShiftHom X ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N r.toMul))).obj Y) m) q
    (DirectSum.of
      (fun m : Additive N ↦
        ShiftHom X ((shiftFunctor C (Additive.ofMul
          (normalQuotientRepresentative N q.toMul))).obj Y) m) n fn)
  have hgen : explicitGen = outerGen := by
    dsimp only [explicitGen, outerGen, innerGen]
    rw [shiftOrbitOf_eq_directSumOf, shiftOrbitOf_eq_directSumOf]
    have hfamily :
        (fun c : Additive (G ⧸ N) ↦ ShiftHom
          (show ShiftOrbitCategory C (Additive N) from X)
          (show ShiftOrbitCategory C (Additive N) from Y) c) =
          (fun r ↦ DirectSum (Additive N) fun m ↦
            ShiftHom X ((shiftFunctor C (Additive.ofMul
              (normalQuotientRepresentative N r.toMul))).obj Y) m) := by
      rfl
    cases hfamily
    rfl
  change
    (D.orbitPushdownResidualFubiniLinearEquiv
      (M := M) N Y).toLinearMap.comp
        (orbitPushdownMapLinear
          (orbitPushdown (A := Additive N) M) explicitGen) =
      (orbitPushdownMapLinear M
        ((D.shiftOrbitResidualFlattenFunctor (k := k) N).map
          explicitGen)).comp
        (D.orbitPushdownResidualFubiniLinearEquiv
          (M := M) N X).toLinearMap
  rw [hgen, D.shiftOrbitResidualFlattenFunctor_map_of_of]
  rw [orbitPushdownMapLinear_of
    (M := orbitPushdown (A := Additive N) M)]
  exact D.orbitPushdownResidualFubini_naturality_of_of
    M N q n X Y fn

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The objectwise residual Fubini equivalences are natural for every
finite-support morphism in the iterated orbit category. -/
theorem orbitPushdownResidualFubini_naturality
    (N : Subgroup G) [N.Normal] {X Y : C}
    (f : letI := D.hasShift
      letI := D.additiveShift
      letI := D.linearShift (k := k)
      letI := (D.restrict N).hasShift
      letI := (D.restrict N).additiveShift
      letI := (D.restrict N).linearShift (k := k)
      letI := D.shiftOrbitResidualHasShift N
      letI := D.shiftOrbitResidualAdditiveShift N
      letI := D.shiftOrbitResidualLinearShift (k := k) N
      (show ShiftOrbitCategory
          (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from X) ⟶
        (show ShiftOrbitCategory
          (ShiftOrbitCategory C (Additive N)) (Additive (G ⧸ N)) from Y)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := D.shiftOrbitResidualHasShift N
    letI := D.shiftOrbitResidualAdditiveShift N
    letI := D.shiftOrbitResidualLinearShift (k := k) N
    (orbitPushdown (A := Additive (G ⧸ N))
        (orbitPushdown (A := Additive N) M)).map f ≫
        (D.orbitPushdownResidualFubiniIsoApp (M := M) N Y).hom =
      (D.orbitPushdownResidualFubiniIsoApp (M := M) N X).hom ≫
        ((D.shiftOrbitResidualFlattenFunctor (k := k) N) ⋙
          orbitPushdown (A := Additive G) M).map f := by
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
  apply ModuleCat.hom_ext
  change
    (D.orbitPushdownResidualFubiniLinearEquiv
      (M := M) N Y).toLinearMap.comp
        (orbitPushdownMapLinear
          (orbitPushdown (A := Additive N) M) f) =
      (orbitPushdownMapLinear M
        ((D.shiftOrbitResidualFlattenFunctor (k := k) N).map f)).comp
        (D.orbitPushdownResidualFubiniLinearEquiv
          (M := M) N X).toLinearMap
  exact LinearMap.congr_fun
    (D.orbitPushdownResidualFubini_naturalityLinearMap M N X Y) f

/-- Iterated push-down along `N` and `G / N` is naturally isomorphic to
direct push-down along `G`, after residual orbit flattening. -/
noncomputable def orbitPushdownResidualFubiniIso
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
    orbitPushdown (A := Additive (G ⧸ N))
        (orbitPushdown (A := Additive N) M) ≅
      (D.shiftOrbitResidualFlattenFunctor (k := k) N) ⋙
        orbitPushdown (A := Additive G) M := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := D.shiftOrbitResidualHasShift N
  letI := D.shiftOrbitResidualAdditiveShift N
  letI := D.shiftOrbitResidualLinearShift (k := k) N
  exact NatIso.ofComponents
    (fun X ↦ D.orbitPushdownResidualFubiniIsoApp
      (M := M) N (show C from X))
    (fun f ↦ D.orbitPushdownResidualFubini_naturality
      M N f)

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
