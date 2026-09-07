import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence
import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerFiniteSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownExactLocalDensity
import MagnitudeConjecture.CategoryTheory.FiniteModuleLocalDensityEquivalence
import MagnitudeConjecture.CategoryTheory.ObjectDeletionDeckOrbitStage
import MagnitudeConjecture.CategoryTheory.ObjectDeletionOrbitPushdown
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStagePushedSupport

/-!
# Module transport from singleton deletion to the successor stage

Deleting the distinguished representative and then the remaining objects of
its subgroup orbit is canonically the next accumulated deletion stage.  The
base equivalence is literally bijective on objects, so precomposition gives
an equivalence of finite-dimensional module categories and preserves
intrinsic local density.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]

/-- The additional objects removed at one stage are exactly the orbit of the
distinguished next object for the retained subgroup action. -/
theorem stageAdditionalDeleted_eq_orbit
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i =
      MulAction.orbit (N : Subgroup G)
        (stageNextObject (k := k) R x i) := by
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let S := stageDeletedSet (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  ext z
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply ObjectProperty.FullSubcategory.ext
    apply CategoryTheory.Quotient.ext
    change (n : G) • y.obj.as = z.obj.as
    exact hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := congrArg
      (fun z : StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc ↦ z.obj.as) hn
    change (n : G) • y.obj.as = z.obj.as at h
    exact h

/-- The full subgroup orbit removed at a successor step is invariant under
the literal subgroup action on the current deletion stage. -/
theorem stageAdditionalDeleted_actionInvariant
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    ActionInvariant (G := (N : Subgroup G))
      (StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i) := by
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  rw [stageAdditionalDeleted_eq_orbit (k := k) N R x i]
  intro n z
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨n⁻¹ * g, ?_⟩
    simpa only [mul_smul, inv_smul_smul] using
      congrArg (fun q ↦ n⁻¹ • q) hg
  · rintro ⟨g, rfl⟩
    exact ⟨n * g, by simp only [mul_smul]⟩

/-- The next orbit class, as the canonical surviving object of the fixed
downstairs model of the current stage. -/
noncomputable def stageDownstairsNextObject
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    DownstairsStageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc := by
  dsimp
  letI := (D.restrict (N : Subgroup G)).hasShift
  letI := (D.restrict (N : Subgroup G)).additiveShift
  letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  let y := stageNextObject (k := k) R x i
  let q : DeckOrbitSkeleton
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) (N : Subgroup G) :=
    (Quotient.mk'' y : MulAction.orbitRel.Quotient
      (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc))
  exact (stageDeckOrbitNormalizedEquivalence
    (k := k) (N : Subgroup G) D hC R.representative x i.castSucc).functor.obj q

/-- The fixed-ambient coordinate of the next current-stage orbit is the
literal orbit class represented by `gᵢx`. -/
theorem stageDownstairsNextObject_obj_as
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    (stageDownstairsNextObject (k := k) D hC N R x i).obj.as =
      stageDeckObject (N : Subgroup G) R.representative x i := by
  dsimp
  letI := (D.restrict (N : Subgroup G)).hasShift
  letI := (D.restrict (N : Subgroup G)).additiveShift
  letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  rfl

/-- Deleting the canonical next downstairs object is literally the
additional-deleted set in the fixed-stage successor construction. -/
theorem stageDownstairsNextObject_singleton_eq_additional
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    ({stageDownstairsNextObject (k := k) D hC N R x i} : Set
      (DownstairsStageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)) =
      DownstairsStageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i := by
  dsimp
  letI := (D.restrict (N : Subgroup G)).hasShift
  letI := (D.restrict (N : Subgroup G)).additiveShift
  letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  ext Y
  constructor
  · intro hY
    have hEq : Y = stageDownstairsNextObject (k := k) D hC N R x i := by
      simpa only [Set.mem_singleton_iff] using hY
    subst Y
    change (stageDownstairsNextObject (k := k) D hC N R x i).obj.as ∈
      ({stageDeckObject (N : Subgroup G) R.representative x i} : Set _)
    rw [stageDownstairsNextObject_obj_as (k := k) D hC N R x i]
    exact Set.mem_singleton _
  · intro hY
    change Y.obj.as ∈
      ({stageDeckObject (N : Subgroup G) R.representative x i} : Set _) at hY
    have hObj : Y.obj.as =
        stageDeckObject (N : Subgroup G) R.representative x i := by
      simpa only [Set.mem_singleton_iff] using hY
    have hNext :
        (stageDownstairsNextObject (k := k) D hC N R x i).obj.as =
          stageDeckObject (N : Subgroup G) R.representative x i :=
      stageDownstairsNextObject_obj_as (k := k) D hC N R x i
    have hEq : Y = stageDownstairsNextObject (k := k) D hC N R x i := by
      apply ObjectProperty.FullSubcategory.ext
      apply CategoryTheory.Quotient.ext
      exact hObj.trans hNext.symm
    exact Set.mem_singleton_iff.mpr hEq

set_option backward.isDefEq.respectTransparency false in
/-- Singleton deletion from the actual current-stage orbit skeleton is
equivalent to the fixed ambient downstairs successor stage. -/
noncomputable def stageOrbitSingletonToDownstairsSuccEquivalence
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
      (Quotient.mk'' (stageNextObject (k := k) R x i) :
        MulAction.orbitRel.Quotient (N : Subgroup G) C₀)
    DeletionCategory (k := k)
        (DeckOrbitSkeleton C₀ (N : Subgroup G)) ({q} : Set _) ≌
      DownstairsStageCategory (k := k) (N : Subgroup G)
        R.representative x i.succ := by
  dsimp
  letI := (D.restrict (N : Subgroup G)).hasShift
  letI := (D.restrict (N : Subgroup G)).additiveShift
  letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
    (Quotient.mk'' (stageNextObject (k := k) R x i) :
      MulAction.orbitRel.Quotient (N : Subgroup G) C₀)
  let e := stageDeckOrbitNormalizedEquivalence
    (k := k) (N : Subgroup G) D hC R.representative x i.castSucc
  letI : e.functor.Additive := by
    change (stageDeckOrbitNormalizedFunctor
      (k := k) (N : Subgroup G) D hC R.representative x i.castSucc).Additive
    infer_instance
  letI : e.functor.Linear k := by
    change (stageDeckOrbitNormalizedFunctor
      (k := k) (N : Subgroup G) D hC R.representative x i.castSucc).Linear k
    infer_instance
  let hobj : Function.Bijective e.functor.obj :=
    stageDeckOrbitNormalizedEquivalence_obj_bijective
      (k := k) (N : Subgroup G) D hC R.representative x i.castSucc
  let e₁ := singletonDeletionEquivalence (k := k) (C :=
      DeckOrbitSkeleton C₀ (N : Subgroup G)) e hobj q
  have hset : ({e.functor.obj q} : Set
      (DownstairsStageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)) =
      DownstairsStageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i := by
    exact stageDownstairsNextObject_singleton_eq_additional
      (k := k) D hC N R x i
  let e₂ := deletionEquivalenceOfEq (k := k)
    (DownstairsStageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc) hset
  exact e₁.trans (e₂.trans
    (downstairsStageSuccEquivalence (k := k) (N : Subgroup G)
      R.representative x i))

set_option backward.isDefEq.respectTransparency false in
private theorem stageOrbitSingletonToDownstairsSuccEquivalence_instances
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let E := stageOrbitSingletonToDownstairsSuccEquivalence
      (k := k) D hC N R x i
    E.functor.Additive ∧ E.functor.Linear k := by
  dsimp
  letI := (D.restrict (N : Subgroup G)).hasShift
  letI := (D.restrict (N : Subgroup G)).additiveShift
  letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
    (Quotient.mk'' (stageNextObject (k := k) R x i) :
      MulAction.orbitRel.Quotient (N : Subgroup G) C₀)
  let e := stageDeckOrbitNormalizedEquivalence
    (k := k) (N : Subgroup G) D hC R.representative x i.castSucc
  letI : e.functor.Additive := by
    change (stageDeckOrbitNormalizedFunctor
      (k := k) (N : Subgroup G) D hC R.representative x i.castSucc).Additive
    infer_instance
  letI : e.functor.Linear k := by
    change (stageDeckOrbitNormalizedFunctor
      (k := k) (N : Subgroup G) D hC R.representative x i.castSucc).Linear k
    infer_instance
  let hobj : Function.Bijective e.functor.obj :=
    stageDeckOrbitNormalizedEquivalence_obj_bijective
      (k := k) (N : Subgroup G) D hC R.representative x i.castSucc
  let e₁ := singletonDeletionEquivalence (k := k) (C :=
    DeckOrbitSkeleton C₀ (N : Subgroup G)) e hobj q
  letI : e₁.functor.Additive := inferInstance
  letI : e₁.functor.Linear k := inferInstance
  have hset : ({e.functor.obj q} : Set
      (DownstairsStageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)) =
      DownstairsStageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i := by
    exact stageDownstairsNextObject_singleton_eq_additional
      (k := k) D hC N R x i
  let e₂ := deletionEquivalenceOfEq (k := k)
    (DownstairsStageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc) hset
  letI : e₂.functor.Additive := inferInstance
  letI : e₂.functor.Linear k := inferInstance
  let e₃ := downstairsStageSuccEquivalence (k := k) (N : Subgroup G)
    R.representative x i
  letI : e₃.functor.Additive := inferInstance
  letI : e₃.functor.Linear k := inferInstance
  constructor
  · change (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor)).Additive
    infer_instance
  · change (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor)).Linear k
    infer_instance

noncomputable instance
    stageOrbitSingletonToDownstairsSuccEquivalence_functor_additive
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    (stageOrbitSingletonToDownstairsSuccEquivalence
      (k := k) D hC N R x i).functor.Additive := by
  exact (stageOrbitSingletonToDownstairsSuccEquivalence_instances
    (k := k) D hC N R x i).1

noncomputable instance
    stageOrbitSingletonToDownstairsSuccEquivalence_functor_linear
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    (stageOrbitSingletonToDownstairsSuccEquivalence
      (k := k) D hC N R x i).functor.Linear k := by
  exact (stageOrbitSingletonToDownstairsSuccEquivalence_instances
    (k := k) D hC N R x i).2

set_option backward.isDefEq.respectTransparency false in
/-- Singleton deletion from the actual current orbit skeleton is equivalent
to the actual orbit skeleton of the successor stage. -/
noncomputable def stageOrbitSingletonToSuccEquivalence
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dcurrent := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dcurrent.hasShift
    letI := Dcurrent.additiveShift
    letI := Dcurrent.linearShift (k := k)
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
      (Quotient.mk'' (stageNextObject (k := k) R x i) :
        MulAction.orbitRel.Quotient (N : Subgroup G) C₀)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.succ
    let Dnext := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.succ
    letI := Dnext.hasShift
    letI := Dnext.additiveShift
    letI := Dnext.linearShift (k := k)
    DeletionCategory (k := k)
        (DeckOrbitSkeleton C₀ (N : Subgroup G)) ({q} : Set _) ≌
      DeckOrbitSkeleton
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.succ) (N : Subgroup G) := by
  dsimp
  letI := (D.restrict (N : Subgroup G)).hasShift
  letI := (D.restrict (N : Subgroup G)).additiveShift
  letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let Dcurrent := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI := Dcurrent.hasShift
  letI := Dcurrent.additiveShift
  letI := Dcurrent.linearShift (k := k)
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.succ
  let Dnext := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.succ
  letI := Dnext.hasShift
  letI := Dnext.additiveShift
  letI := Dnext.linearShift (k := k)
  exact (stageOrbitSingletonToDownstairsSuccEquivalence
    (k := k) D hC N R x i).trans
      (stageDeckOrbitNormalizedEquivalence
        (k := k) (N : Subgroup G) D hC R.representative x i.succ).symm

set_option backward.isDefEq.respectTransparency false in
private theorem stageOrbitSingletonToSuccEquivalence_instances
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dcurrent := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dcurrent.hasShift
    letI := Dcurrent.additiveShift
    letI := Dcurrent.linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.succ
    let Dnext := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.succ
    letI := Dnext.hasShift
    letI := Dnext.additiveShift
    letI := Dnext.linearShift (k := k)
    let E := stageOrbitSingletonToSuccEquivalence
      (k := k) D hC N R x i
    E.functor.Additive ∧ E.functor.Linear k := by
  dsimp
  letI := (D.restrict (N : Subgroup G)).hasShift
  letI := (D.restrict (N : Subgroup G)).additiveShift
  letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let Dcurrent := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI := Dcurrent.hasShift
  letI := Dcurrent.additiveShift
  letI := Dcurrent.linearShift (k := k)
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.succ
  let Dnext := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.succ
  letI := Dnext.hasShift
  letI := Dnext.additiveShift
  letI := Dnext.linearShift (k := k)
  let e₁ := stageOrbitSingletonToDownstairsSuccEquivalence
    (k := k) D hC N R x i
  letI : e₁.functor.Additive := inferInstance
  letI : e₁.functor.Linear k := inferInstance
  let e₂ := stageDeckOrbitNormalizedEquivalence
    (k := k) (N : Subgroup G) D hC R.representative x i.succ
  letI : e₂.functor.Additive := by
    change (stageDeckOrbitNormalizedFunctor
      (k := k) (N : Subgroup G) D hC R.representative x i.succ).Additive
    infer_instance
  letI : e₂.functor.Linear k := by
    change (stageDeckOrbitNormalizedFunctor
      (k := k) (N : Subgroup G) D hC R.representative x i.succ).Linear k
    infer_instance
  letI : e₂.inverse.Additive := inferInstance
  letI : e₂.inverse.Linear k := inferInstance
  constructor
  · change (e₁.functor ⋙ e₂.inverse).Additive
    infer_instance
  · change (e₁.functor ⋙ e₂.inverse).Linear k
    infer_instance

noncomputable instance stageOrbitSingletonToSuccEquivalence_functor_additive
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dcurrent := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dcurrent.hasShift
    letI := Dcurrent.additiveShift
    letI := Dcurrent.linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.succ
    let Dnext := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.succ
    letI := Dnext.hasShift
    letI := Dnext.additiveShift
    letI := Dnext.linearShift (k := k)
    (stageOrbitSingletonToSuccEquivalence
      (k := k) D hC N R x i).functor.Additive := by
  exact (stageOrbitSingletonToSuccEquivalence_instances
    (k := k) D hC N R x i).1

noncomputable instance stageOrbitSingletonToSuccEquivalence_functor_linear
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    letI := (D.restrict (N : Subgroup G)).hasShift
    letI := (D.restrict (N : Subgroup G)).additiveShift
    letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dcurrent := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dcurrent.hasShift
    letI := Dcurrent.additiveShift
    letI := Dcurrent.linearShift (k := k)
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.succ
    let Dnext := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.succ
    letI := Dnext.hasShift
    letI := Dnext.additiveShift
    letI := Dnext.linearShift (k := k)
    (stageOrbitSingletonToSuccEquivalence
      (k := k) D hC N R x i).functor.Linear k := by
  exact (stageOrbitSingletonToSuccEquivalence_instances
    (k := k) D hC N R x i).2

/-- The current stage after direct deletion of the next full subgroup orbit. -/
abbrev StageFullOrbitCategory
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :=
  DeletionCategory (k := k)
    (StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc)
    (StageAdditionalDeleted (k := k) (N : Subgroup G)
      R.representative x i)

/-- Direct full-orbit deletion is the canonical successor stage. -/
noncomputable def stageFullOrbitEquivalence
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    StageFullOrbitCategory (k := k) N R x i ≌
      StageCategory (k := k) (N : Subgroup G)
        R.representative x i.succ :=
  stageSuccEquivalence (k := k) (N : Subgroup G)
    R.representative x i

noncomputable instance stageFullOrbitEquivalence_functor_additive
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    (stageFullOrbitEquivalence (k := k) N R x i).functor.Additive :=
  by
    change (stageSuccEquivalence (k := k) (N : Subgroup G)
      R.representative x i).functor.Additive
    infer_instance

noncomputable instance stageFullOrbitEquivalence_functor_linear
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    (stageFullOrbitEquivalence (k := k) N R x i).functor.Linear k :=
  by
    change (stageSuccEquivalence (k := k) (N : Subgroup G)
      R.representative x i).functor.Linear k
    infer_instance

/-- The direct full-orbit successor comparison is literally bijective on
objects. -/
theorem stageFullOrbitEquivalence_functor_obj_bijective
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    Function.Bijective
      (stageFullOrbitEquivalence (k := k) N R x i).functor.obj :=
  stageSuccEquivalence_functor_obj_bijective
    (k := k) (C := C) (N : Subgroup G) R.representative x i

/-- The literal object equivalence underlying direct full-orbit deletion. -/
noncomputable def stageFullOrbitObjectEquiv
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    StageFullOrbitCategory (k := k) N R x i ≃
      StageCategory (k := k) (N : Subgroup G)
        R.representative x i.succ :=
  Equiv.ofBijective
    (stageFullOrbitEquivalence (k := k) N R x i).functor.obj
    (stageFullOrbitEquivalence_functor_obj_bijective
      (k := k) N R x i)

/-- Finite-dimensional modules on the successor stage are equivalent to
modules on the direct full-orbit deletion. -/
noncomputable def stageFullOrbitFiniteDimensionalModuleEquivalence
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := StageCategory (k := k) (N : Subgroup G)
          R.representative x i.succ) k ≌
      FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := StageFullOrbitCategory (k := k) N R x i) k := by
  let e := stageFullOrbitEquivalence (k := k) N R x i
  letI : e.functor.Additive := inferInstance
  letI : e.functor.Linear k := inferInstance
  exact finiteDimensionalModuleCongrEquivalence (k := k) e
    (stageFullOrbitObjectEquiv (k := k) N R x i) (fun _ ↦ rfl)

noncomputable instance stageFullOrbitFiniteDimensionalModuleEquivalence_functor_additive
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    (stageFullOrbitFiniteDimensionalModuleEquivalence
      (k := k) N R x i).functor.Additive := by
  unfold stageFullOrbitFiniteDimensionalModuleEquivalence
  infer_instance

noncomputable instance stageFullOrbitFiniteDimensionalModuleEquivalence_inverse_additive
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    (stageFullOrbitFiniteDimensionalModuleEquivalence
      (k := k) N R x i).inverse.Additive := by
  infer_instance

/-- Transport from direct full-orbit deletion to the literal successor stage
preserves intrinsic local density. -/
theorem stageFullOrbit_localDensity_inverse
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := StageFullOrbitCategory (k := k) N R x i) k)
    (hM : Indecomposable M) :
    let E := stageFullOrbitFiniteDimensionalModuleEquivalence
      (k := k) N R x i
    finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C
          (stageDeletedSet (N : Subgroup G)
            R.representative x i.succ) hrep)
        (E.inverse.obj M)
        ((MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
          E.inverse M).2 hM) =
      finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k)
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)
          (StageAdditionalDeleted (k := k) (N : Subgroup G)
            R.representative x i)
          (isLocallyRepresentationFinite_deletion (k := k) C
            (stageDeletedSet (N : Subgroup G)
              R.representative x i.castSucc) hrep))
        M hM := by
  let E := stageFullOrbitFiniteDimensionalModuleEquivalence
    (k := k) N R x i
  let hSucc := isLocallyRepresentationFinite_deletion (k := k) C
    (stageDeletedSet (N : Subgroup G) R.representative x i.succ) hrep
  let hStage := isLocallyRepresentationFinite_deletion (k := k) C
    (stageDeletedSet (N : Subgroup G) R.representative x i.castSucc) hrep
  let hFull := isLocallyRepresentationFinite_deletion (k := k)
    (StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc)
    (StageAdditionalDeleted (k := k) (N : Subgroup G)
      R.representative x i) hStage
  letI : E.inverse.Additive := inferInstance
  letI : E.symm.functor.Additive := by
    change E.inverse.Additive
    infer_instance
  exact finiteModuleLocalDensity_map_equivalence
    hSucc hFull E.symm M hM

/-- Direct push-down after deleting the next full subgroup orbit preserves
the intrinsic local density of every surviving indecomposable module. -/
theorem stageFullOrbitRestriction_pushdownLocalDensity
    [IsAlgClosed k]
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) k)
    (hM : Indecomposable M)
    (hvanish : ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      (StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i) M.obj.obj) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    letI := stageIsCancelSMul (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
      R.representative x i
    let hT := stageAdditionalDeleted_actionInvariant (k := k) N R x i
    let hCstage := deletion_skeletal (k := k) C hC hlocal
      (stageDeletedSet (N : Subgroup G)
        R.representative x i.castSucc)
    letI := isClosedUnderIsomorphisms_of_skeletal hCstage T
    letI := deletionMulAction (k := k) T hT
    letI := deletionIsCancelSMul (k := k) T hT
    let Dfull := CoherentDeckShift.deletionCoherentDeckShift
      (k := k) Dstage T hT
    letI := Dfull.hasShift
    letI := Dfull.additiveShift
    letI := Dfull.linearShift (k := k)
    let Z := finiteDimensionalModuleRestrictionToDeletion
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) T M hvanish
    let hZ := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) T M hM hvanish
    let Pfull := Dfull.finiteDimensionalModuleOrbitSkeletonPushdown
      (k := k)
    ∀ (hDown : IsLocallyRepresentationFinite
        (k := k)
        (C := DeckOrbitSkeleton
          (StageFullOrbitCategory (k := k) N R x i)
          (N : Subgroup G)))
      (hPZ : Indecomposable (Pfull.obj Z)),
      finiteModuleLocalDensity hDown (Pfull.obj Z) hPZ =
        finiteModuleLocalDensity
          (isLocallyRepresentationFinite_deletion (k := k)
            (StageCategory (k := k) (N : Subgroup G)
              R.representative x i.castSucc) T
            (isLocallyRepresentationFinite_deletion (k := k) C
              (stageDeletedSet (N : Subgroup G)
                R.representative x i.castSucc) hrep))
          Z hZ := by
  let S := stageDeletedSet (N : Subgroup G)
    R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
  letI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G) C) :=
    CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  letI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)) :=
    finite_deletionOrbitQuotient (k := k) C S
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) R.representative x i.castSucc)
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
    R.representative x i
  let hT := stageAdditionalDeleted_actionInvariant (k := k) N R x i
  let hCstage : Skeletal
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    deletion_skeletal (k := k) C hC hlocal S
  letI : ObjectProperty.IsClosedUnderIsomorphisms T :=
    isClosedUnderIsomorphisms_of_skeletal hCstage T
  letI := deletionMulAction (k := k) T hT
  haveI : IsCancelSMul (N : Subgroup G)
      (StageFullOrbitCategory (k := k) N R x i) :=
    deletionIsCancelSMul (k := k) T hT
  letI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G)
        (StageFullOrbitCategory (k := k) N R x i)) :=
    finite_deletionOrbitQuotient (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) T hT
  let Dfull := CoherentDeckShift.deletionCoherentDeckShift
    (k := k) Dstage T hT
  letI := Dfull.hasShift
  letI := Dfull.additiveShift
  letI := Dfull.linearShift (k := k)
  haveI : ∀ a : Additive (N : Subgroup G),
      (Dfull.core.F a).Additive :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_additive
      (k := k) Dstage T hT a
  haveI : ∀ a : Additive (N : Subgroup G),
      (Dfull.core.F a).Linear k :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_linear
      (k := k) Dstage T hT a
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hIstage := fun X ↦
    deletion_dualLinearYoneda_isFiniteDimensional (k := k) C hI S X
  let hlocalStage := fun X ↦
    deletion_end_isLocalRing (k := k) C hC hlocal S X
  let hrepStage := isLocallyRepresentationFinite_deletion (k := k) C S hrep
  let hPfull := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) hPstage T X
  let hIfull := fun X ↦
    deletion_dualLinearYoneda_isFiniteDimensional
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) hIstage T X
  let hlocalFull := fun X ↦
    deletion_end_isLocalRing (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      hCstage hlocalStage T X
  let hrepFull := isLocallyRepresentationFinite_deletion (k := k)
    (StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc) T hrepStage
  let hfreeFull :=
    Dfull.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hPfull hlocalFull
  let Z := finiteDimensionalModuleRestrictionToDeletion
    (k := k)
    (StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc) T M hvanish
  let hZ := finiteDimensionalModuleRestrictionToDeletion_indec
    (k := k)
    (StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc) T M hM hvanish
  let Pfull := Dfull.finiteDimensionalModuleOrbitSkeletonPushdown
    (k := k)
  change ∀ (hDown : IsLocallyRepresentationFinite
      (k := k)
      (C := DeckOrbitSkeleton
        (StageFullOrbitCategory (k := k) N R x i)
        (N : Subgroup G)))
    (hPZ : Indecomposable (Pfull.obj Z)),
    finiteModuleLocalDensity hDown (Pfull.obj Z) hPZ =
      finiteModuleLocalDensity hrepFull Z hZ
  intro hDown hPZ
  exact Dfull.finiteDimensionalModuleOrbitSkeletonPushdown_localDensity_eq
    (k := k) hPfull hIfull hlocalFull hfreeFull hrepFull Z hZ hDown hPZ

set_option maxHeartbeats 2000000 in
/-- After one full orbit is deleted upstairs, the restricted skeletal
push-down has the same intrinsic local density as the direct upstairs
restriction.  The deleted downstairs set is written as the corresponding
singleton orbit class. -/
theorem stageFullOrbitRestriction_downstairsLocalDensity
    [IsAlgClosed k]
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) k)
    (hM : Indecomposable M)
    (hFull : ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      (StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i) M.obj.obj) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    letI := stageIsCancelSMul (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let Pstage := Dstage.finiteDimensionalModuleOrbitSkeletonPushdown
      (k := k)
    let y := stageNextObject (k := k) R x i
    let q := (Quotient.mk'' y : MulAction.orbitRel.Quotient
      (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc))
    ∀ (hPM : Indecomposable (Pstage.obj M))
      (hDownVanish : ModuleVanishesOnDeleted
        (k := k)
        (DeckOrbitSkeleton
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)
          (N : Subgroup G)) ({q} : Set _)
        (Pstage.obj M).obj.obj),
      let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i
      let Z := finiteDimensionalModuleRestrictionToDeletion
        (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc) T M hFull
      let hZ := finiteDimensionalModuleRestrictionToDeletion_indec
        (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc) T M hM hFull
      let Rdown := finiteDimensionalModuleRestrictionToDeletion
        (k := k)
        (DeckOrbitSkeleton
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)
          (N : Subgroup G)) ({q} : Set _) (Pstage.obj M) hDownVanish
      let hRdown := finiteDimensionalModuleRestrictionToDeletion_indec
        (k := k)
        (DeckOrbitSkeleton
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)
          (N : Subgroup G)) ({q} : Set _) (Pstage.obj M) hPM hDownVanish
      let Down := stageFiniteOrbitModuleIndecomposableSkeleton
        (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
      finiteModuleLocalDensity
          (isLocallyRepresentationFinite_deletion
            (k := k)
            (DeckOrbitSkeleton
              (StageCategory (k := k) (N : Subgroup G)
                R.representative x i.castSucc)
              (N : Subgroup G)) ({q} : Set _)
            Down.isLocallyRepresentationFinite)
          Rdown hRdown =
        finiteModuleLocalDensity
          (isLocallyRepresentationFinite_deletion
            (k := k)
            (StageCategory (k := k) (N : Subgroup G)
              R.representative x i.castSucc) T
            (isLocallyRepresentationFinite_deletion (k := k) C
              (stageDeletedSet (N : Subgroup G)
                R.representative x i.castSucc) hrep))
          Z hZ := by
  let S := stageDeletedSet (N : Subgroup G)
    R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
  letI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G) C) :=
    CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  letI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)) :=
    finite_deletionOrbitQuotient (k := k) C S
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) R.representative x i.castSucc)
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  let Pstage := Dstage.finiteDimensionalModuleOrbitSkeletonPushdown
    (k := k)
  let y := stageNextObject (k := k) R x i
  let q := (Quotient.mk'' y : MulAction.orbitRel.Quotient
    (N : Subgroup G)
    (StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc))
  change ∀ (hPM : Indecomposable (Pstage.obj M))
      (hDownVanish : ModuleVanishesOnDeleted
        (k := k)
        (DeckOrbitSkeleton
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)
          (N : Subgroup G)) ({q} : Set _)
        (Pstage.obj M).obj.obj), _
  intro hPM hDownVanish
  let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
    R.representative x i
  let hT := stageAdditionalDeleted_actionInvariant (k := k) N R x i
  let hCstage := deletion_skeletal (k := k) C hC hlocal S
  letI : ObjectProperty.IsClosedUnderIsomorphisms T :=
    isClosedUnderIsomorphisms_of_skeletal hCstage T
  letI := deletionMulAction (k := k) T hT
  haveI : IsCancelSMul (N : Subgroup G)
      (StageFullOrbitCategory (k := k) N R x i) :=
    deletionIsCancelSMul (k := k) T hT
  letI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G)
        (StageFullOrbitCategory (k := k) N R x i)) :=
    finite_deletionOrbitQuotient (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) T hT
  let Dfull := CoherentDeckShift.deletionCoherentDeckShift
    (k := k) Dstage T hT
  letI := Dfull.hasShift
  letI := Dfull.additiveShift
  letI := Dfull.linearShift (k := k)
  haveI : ∀ a : Additive (N : Subgroup G),
      (Dfull.core.F a).Additive :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_additive
      (k := k) Dstage T hT a
  haveI : ∀ a : Additive (N : Subgroup G),
      (Dfull.core.F a).Linear k :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_linear
      (k := k) Dstage T hT a
  let Z := finiteDimensionalModuleRestrictionToDeletion
    (k := k)
    (StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc) T M hFull
  let hZ : Indecomposable Z :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) T M hM hFull
  let Pfull := Dfull.finiteDimensionalModuleOrbitSkeletonPushdown
    (k := k)
  let Rdown := finiteDimensionalModuleRestrictionToDeletion
    (k := k)
    (DeckOrbitSkeleton
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      (N : Subgroup G)) ({q} : Set _) (Pstage.obj M) hDownVanish
  let hRdown : Indecomposable Rdown :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k)
      (DeckOrbitSkeleton
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (N : Subgroup G)) ({q} : Set _) (Pstage.obj M) hPM hDownVanish
  have hDeckEq : deckOrbitDeletedSet (G := (N : Subgroup G)) T =
      ({q} : Set (DeckOrbitSkeleton
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (N : Subgroup G))) := by
    change deckOrbitDeletedSet (G := (N : Subgroup G))
        (StageAdditionalDeleted (k := k) (N : Subgroup G)
          R.representative x i) =
      ({(Quotient.mk'' y : MulAction.orbitRel.Quotient
        (N : Subgroup G)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc))} : Set _)
    rw [stageAdditionalDeleted_eq_orbit (k := k) N R x i]
    exact deckOrbitDeletedSet_orbit (G := (N : Subgroup G)) y
  let hShift :=
    CoherentDeckShift.shiftInvariant_of_actionInvariant Dstage T hT
  letI := rawHasShift (k := k) T hShift
  letI : ∀ a : Additive (N : Subgroup G),
      (shiftFunctor
        (RawCategory (k := k)
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc) T) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) T hShift a
  letI : ∀ a : Additive (N : Subgroup G),
      (shiftFunctor
        (RawCategory (k := k)
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc) T) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) T hShift a
  letI := deletionHasShift (k := k) T hShift
  letI : ∀ a : Additive (N : Subgroup G),
      (shiftFunctor (StageFullOrbitCategory (k := k) N R x i) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) T hShift a
  letI : ∀ a : Additive (N : Subgroup G),
      (shiftFunctor (StageFullOrbitCategory (k := k) N R x i) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) T hShift a
  let hDeck :=
    MagnitudeConjecture.ObjectDeletion.orbitSkeletonPushdown_vanishesOnDeleted_of_vanishesOnDeleted
      (k := k) Dstage T hT M.obj hFull
  let eDeck := deckOrbitDeletionCommEquivalence
    (k := k) Dstage T hT
  letI : eDeck.functor.Additive :=
    deckOrbitDeletionCommEquivalence_functor_additive
      (k := k) Dstage T hT
  letI : eDeck.functor.Linear k :=
    deckOrbitDeletionCommEquivalence_functor_linear
      (k := k) Dstage T hT
  let DownBase := DeckOrbitSkeleton
    (StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc)
    (N : Subgroup G)
  let DownDeletion := DeletionCategory (k := k) DownBase ({q} : Set _)
  let eEq : DeletionCategory (k := k) DownBase
      (deckOrbitDeletedSet (G := (N : Subgroup G)) T) ≌ DownDeletion :=
    deletionEquivalenceOfEq (k := k) DownBase hDeckEq
  letI : eEq.functor.Additive := inferInstance
  letI : eEq.functor.Linear k := inferInstance
  let eBase :
      DeckOrbitSkeleton (StageFullOrbitCategory (k := k) N R x i)
          (N : Subgroup G) ≌ DownDeletion :=
    eDeck.trans eEq
  letI : eBase.functor.Additive := by
    change (eDeck.functor ⋙ eEq.functor).Additive
    constructor
    intro X Y f g
    change eEq.functor.map (eDeck.functor.map (f + g)) = _
    rw [eDeck.functor.map_add, eEq.functor.map_add]
    rfl
  letI : eBase.functor.Linear k := by
    change (eDeck.functor ⋙ eEq.functor).Linear k
    constructor
    intro X Y f r
    change eEq.functor.map (eDeck.functor.map (r • f)) = _
    rw [eDeck.functor.map_smul, eEq.functor.map_smul]
    rfl
  letI : Finite
      (DeckOrbitSkeleton (StageFullOrbitCategory (k := k) N R x i)
        (N : Subgroup G)) :=
    finite_deletionOrbitQuotient (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) T hT
  letI : Finite
      (DeckOrbitSkeleton
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (N : Subgroup G)) :=
    finite_deletionOrbitQuotient (k := k) C S
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) R.representative x i.castSucc)
  letI : Finite DownDeletion :=
    Finite.of_injective
      (fun X : DownDeletion ↦ X.obj.as)
      (fun X Y h ↦ by
        apply ObjectProperty.FullSubcategory.ext
        apply CategoryTheory.Quotient.ext
        exact h)
  let E := finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) eBase
  let hEadd : E.functor.Additive := by
    change (finiteDimensionalModuleCongrEquivalenceOfFinite
      (k := k) eBase).functor.Additive
    exact finiteDimensionalModuleCongrEquivalenceOfFinite_functor_additive
      (k := k) eBase
  letI : E.functor.Additive := hEadd
  let eEqRestriction :=
    deletionEquivalenceOfEq_linearModuleRestrictionIso
      (k := k)
      (DeckOrbitSkeleton
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (N : Subgroup G))
      (deckOrbitDeletedSet (G := (N : Subgroup G)) T)
      hDeckEq (Pstage.obj M).obj hDeck hDownVanish
  let n :=
    MagnitudeConjecture.ObjectDeletion.orbitSkeletonPushdownRestrictionIso
      (k := k) Dstage T hT M.obj hFull
  let n' : orbitSkeletonPushdown (G := (N : Subgroup G)) Z.obj.obj ≅
      eBase.functor ⋙ Rdown.obj.obj :=
    n ≪≫ (Functor.isoWhiskerLeft eDeck.functor eEqRestriction).symm
  let eFinite : Pfull.obj Z ≅ E.functor.obj Rdown :=
    ObjectProperty.isoMk _ (ObjectProperty.isoMk _ n')
  let hER : Indecomposable (E.functor.obj Rdown) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor Rdown).2 hRdown
  let hPZ : Indecomposable (Pfull.obj Z) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eFinite).2 hER
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hIstage := fun X ↦
    deletion_dualLinearYoneda_isFiniteDimensional (k := k) C hI S X
  let hlocalStage := fun X ↦
    deletion_end_isLocalRing (k := k) C hC hlocal S X
  let hrepStage := isLocallyRepresentationFinite_deletion (k := k) C S hrep
  let hPfull := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) hPstage T X
  let hIfull := fun X ↦
    deletion_dualLinearYoneda_isFiniteDimensional
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) hIstage T X
  let hlocalFull := fun X ↦
    deletion_end_isLocalRing (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      hCstage hlocalStage T X
  let hrepFull := isLocallyRepresentationFinite_deletion (k := k)
    (StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc) T hrepStage
  let hfreeFull :=
    Dfull.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hPfull hlocalFull
  let Full := Dfull.finiteOrbitModuleIndecomposableSkeleton
    (k := k) hPfull hIfull hlocalFull hfreeFull hrepFull
  let Down := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
  let hDownDeletion := isLocallyRepresentationFinite_deletion
    (k := k)
    (DeckOrbitSkeleton
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      (N : Subgroup G)) ({q} : Set _)
    Down.isLocallyRepresentationFinite
  have hMap := @finiteModuleLocalDensity_map_equivalence k _
    (DeckOrbitSkeleton (StageFullOrbitCategory (k := k) N R x i)
      (N : Subgroup G)) _ _ _
    DownDeletion _ _ _
    Full.isLocallyRepresentationFinite hDownDeletion E hEadd Rdown hRdown
  have hIso := finiteModuleLocalDensity_eq_of_iso
    Full.isLocallyRepresentationFinite hPZ hER eFinite
  have hPush := stageFullOrbitRestriction_pushdownLocalDensity
    (k := k) D hC hP hI hlocal hrep N R x i M hM hFull
      Full.isLocallyRepresentationFinite hPZ
  exact hMap.symm.trans (hIso.symm.trans hPush)

/-- The category obtained by first deleting the distinguished representative
from the current stage and then deleting the surviving objects of its full
subgroup orbit. -/
abbrev StageSingletonRemainingCategory
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :=
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  DeletionCategory (k := k)
    (DeletionCategory (k := k) C₀ ({y} : Set C₀))
    (AdditionalDeleted (k := k) C₀ ({y} : Set C₀)
      (StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i))

/-- The distinguished next object belongs to the full subgroup orbit removed
at its successor step. -/
theorem stageNextObject_mem_additionalDeleted
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    stageNextObject (k := k) R x i ∈
      StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i := by
  change (stageNextObject (k := k) R x i).obj.as ∈
    subgroupOrbit (N : Subgroup G) (R.representative i • x)
  have hy : (stageNextObject (k := k) R x i).obj.as =
      R.representative i • x := rfl
  rw [hy]
  exact ⟨1, by simp⟩

/-- Successive deletion of the representative and the rest of its orbit is
canonically equivalent to direct deletion of the full orbit. -/
noncomputable def stageSingletonRemainingToFullOrbitEquivalence
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    StageSingletonRemainingCategory (k := k) N R x i ≌
      StageFullOrbitCategory (k := k) N R x i := by
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
    R.representative x i
  have hyT : y ∈ T := stageNextObject_mem_additionalDeleted
    (k := k) N R x i
  have hunion : ({y} : Set C₀) ∪ T = T :=
    Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr hyT)
  exact
    (iteratedDeletionEquivalence (k := k) C₀ ({y} : Set C₀) T).trans
      (deletionEquivalenceOfEq (k := k) C₀ hunion)

/-- The direct-versus-successive deletion equivalence is literally
bijective on objects. -/
theorem stageSingletonRemainingToFullOrbitEquivalence_functor_obj_bijective
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    Function.Bijective
      (stageSingletonRemainingToFullOrbitEquivalence
        (k := k) N R x i).functor.obj := by
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
    R.representative x i
  have hyT : y ∈ T := stageNextObject_mem_additionalDeleted
    (k := k) N R x i
  have hunion : ({y} : Set C₀) ∪ T = T :=
    Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr hyT)
  exact
    (deletionEquivalenceOfEq_functor_obj_bijective
      (k := k) C₀ hunion).comp
        (iteratedDeletionEquivalence_functor_obj_bijective
          (k := k) C₀ ({y} : Set C₀) T)

noncomputable instance
    stageSingletonRemainingToFullOrbitEquivalence_functor_additive
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    (stageSingletonRemainingToFullOrbitEquivalence
      (k := k) N R x i).functor.Additive := by
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
    R.representative x i
  have hyT : y ∈ T := stageNextObject_mem_additionalDeleted
    (k := k) N R x i
  have hunion : ({y} : Set C₀) ∪ T = T :=
    Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr hyT)
  let e₁ := iteratedDeletionEquivalence (k := k) C₀ ({y} : Set C₀) T
  let e₂ := deletionEquivalenceOfEq (k := k) C₀ hunion
  letI : e₁.functor.Additive := inferInstance
  letI : e₂.functor.Additive := inferInstance
  change (e₁.functor ⋙ e₂.functor).Additive
  infer_instance

noncomputable instance
    stageSingletonRemainingToFullOrbitEquivalence_functor_linear
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    (stageSingletonRemainingToFullOrbitEquivalence
      (k := k) N R x i).functor.Linear k := by
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
    R.representative x i
  have hyT : y ∈ T := stageNextObject_mem_additionalDeleted
    (k := k) N R x i
  have hunion : ({y} : Set C₀) ∪ T = T :=
    Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr hyT)
  let e₁ := iteratedDeletionEquivalence (k := k) C₀ ({y} : Set C₀) T
  let e₂ := deletionEquivalenceOfEq (k := k) C₀ hunion
  letI : e₁.functor.Linear k := inferInstance
  letI : e₂.functor.Linear k := inferInstance
  change (e₁.functor ⋙ e₂.functor).Linear k
  infer_instance

/-- The object equivalence underlying the direct-versus-successive deletion
comparison. -/
noncomputable def stageSingletonRemainingToFullOrbitObjectEquiv
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    StageSingletonRemainingCategory (k := k) N R x i ≃
      StageFullOrbitCategory (k := k) N R x i :=
  Equiv.ofBijective
    (stageSingletonRemainingToFullOrbitEquivalence
      (k := k) N R x i).functor.obj
    (stageSingletonRemainingToFullOrbitEquivalence_functor_obj_bijective
      (k := k) N R x i)

/-- Direct full-orbit modules and successive representative/orbit modules
are equivalent by precomposition. -/
noncomputable def
    stageSingletonRemainingToFullOrbitFiniteDimensionalModuleEquivalence
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := StageFullOrbitCategory (k := k) N R x i) k ≌
      FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := StageSingletonRemainingCategory (k := k) N R x i) k := by
  let e := stageSingletonRemainingToFullOrbitEquivalence
    (k := k) N R x i
  letI : e.functor.Additive := inferInstance
  letI : e.functor.Linear k := inferInstance
  exact finiteDimensionalModuleCongrEquivalence (k := k) e
    (stageSingletonRemainingToFullOrbitObjectEquiv (k := k) N R x i)
    (fun _ ↦ rfl)

noncomputable instance
    stageSingletonRemainingToFullOrbitFiniteDimensionalModuleEquivalence_functor_additive
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m) :
    (stageSingletonRemainingToFullOrbitFiniteDimensionalModuleEquivalence
      (k := k) N R x i).functor.Additive := by
  unfold stageSingletonRemainingToFullOrbitFiniteDimensionalModuleEquivalence
  infer_instance

/-- Direct restriction along the full orbit and successive restriction along
the representative and its remaining orbit define isomorphic finite modules
under the canonical deletion equivalence. -/
noncomputable def stageFullOrbitRestriction_iteratedIso
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) k)
    (hFull : ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      (StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i) M.obj.obj)
    (hSingleton : ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      ({stageNextObject (k := k) R x i} :
        Set (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)) M.obj.obj)
    (hRemaining : ModuleVanishesOnDeleted
      (k := k)
      (DeletionCategory (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)))
      (AdditionalDeleted (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc))
        (StageAdditionalDeleted (k := k) (N : Subgroup G)
          R.representative x i))
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)) M hSingleton).obj.obj) :
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let y := stageNextObject (k := k) R x i
    let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
      R.representative x i
    let Zfull := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C₀ T M hFull
    let Z₁ := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C₀ ({y} : Set C₀) M hSingleton
    let Z₂ := finiteDimensionalModuleRestrictionToDeletion
      (k := k) (DeletionCategory (k := k) C₀ ({y} : Set C₀))
      (AdditionalDeleted (k := k) C₀ ({y} : Set C₀) T)
      Z₁ hRemaining
    let E :=
      stageSingletonRemainingToFullOrbitFiniteDimensionalModuleEquivalence
        (k := k) N R x i
    E.functor.obj Zfull ≅ Z₂ := by
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
    R.representative x i
  let Zfull := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C₀ T M hFull
  let Z₁ := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C₀ ({y} : Set C₀) M hSingleton
  let Z₂ := finiteDimensionalModuleRestrictionToDeletion
    (k := k) (DeletionCategory (k := k) C₀ ({y} : Set C₀))
    (AdditionalDeleted (k := k) C₀ ({y} : Set C₀) T)
    Z₁ hRemaining
  let E :=
    stageSingletonRemainingToFullOrbitFiniteDimensionalModuleEquivalence
      (k := k) N R x i
  have hyT : ({y} : Set C₀) ⊆ T :=
    Set.singleton_subset_iff.mpr
      (stageNextObject_mem_additionalDeleted (k := k) N R x i)
  let e := iteratedLinearModuleRestrictionIsoOfSubset
    (k := k) C₀ ({y} : Set C₀) T hyT M.obj hFull
      hSingleton hRemaining
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e)

/-- Direct full-orbit restriction and successive representative/remaining-
orbit restriction have the same intrinsic local density. -/
theorem stageFullOrbitRestriction_iteratedLocalDensity
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) k)
    (hM : Indecomposable M)
    (hFull : ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      (StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i) M.obj.obj)
    (hSingleton : ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      ({stageNextObject (k := k) R x i} :
        Set (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)) M.obj.obj)
    (hRemaining : ModuleVanishesOnDeleted
      (k := k)
      (DeletionCategory (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)))
      (AdditionalDeleted (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc))
        (StageAdditionalDeleted (k := k) (N : Subgroup G)
          R.representative x i))
      (finiteDimensionalModuleRestrictionToDeletion
        (k := k)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        ({stageNextObject (k := k) R x i} :
          Set (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.castSucc)) M hSingleton).obj.obj) :
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let y := stageNextObject (k := k) R x i
    let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
      R.representative x i
    let C₁ := DeletionCategory (k := k) C₀ ({y} : Set C₀)
    let T₁ := AdditionalDeleted (k := k) C₀ ({y} : Set C₀) T
    let Zfull := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C₀ T M hFull
    let hZfull := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C₀ T M hM hFull
    let Z₁ := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C₀ ({y} : Set C₀) M hSingleton
    let hZ₁ := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C₀ ({y} : Set C₀) M hM hSingleton
    let Z₂ := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C₁ T₁ Z₁ hRemaining
    let hZ₂ := finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C₁ T₁ Z₁ hZ₁ hRemaining
    finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C₀ T
          (isLocallyRepresentationFinite_deletion (k := k) C
            (stageDeletedSet (N : Subgroup G)
              R.representative x i.castSucc) hrep))
        Zfull hZfull =
      finiteModuleLocalDensity
        (isLocallyRepresentationFinite_deletion (k := k) C₁ T₁
          (isLocallyRepresentationFinite_deletion
            (k := k) C₀ ({y} : Set C₀)
            (isLocallyRepresentationFinite_deletion (k := k) C
              (stageDeletedSet (N : Subgroup G)
                R.representative x i.castSucc) hrep)))
        Z₂ hZ₂ := by
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
    R.representative x i
  let C₁ := DeletionCategory (k := k) C₀ ({y} : Set C₀)
  let T₁ := AdditionalDeleted (k := k) C₀ ({y} : Set C₀) T
  let Zfull := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C₀ T M hFull
  let hZfull : Indecomposable Zfull :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C₀ T M hM hFull
  let Z₁ := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C₀ ({y} : Set C₀) M hSingleton
  let hZ₁ : Indecomposable Z₁ :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C₀ ({y} : Set C₀) M hM hSingleton
  let Z₂ := finiteDimensionalModuleRestrictionToDeletion
    (k := k) C₁ T₁ Z₁ hRemaining
  let hZ₂ : Indecomposable Z₂ :=
    finiteDimensionalModuleRestrictionToDeletion_indec
      (k := k) C₁ T₁ Z₁ hZ₁ hRemaining
  let E :=
    stageSingletonRemainingToFullOrbitFiniteDimensionalModuleEquivalence
      (k := k) N R x i
  letI : E.functor.Additive := inferInstance
  let hFullRep := isLocallyRepresentationFinite_deletion (k := k) C₀ T
    (isLocallyRepresentationFinite_deletion (k := k) C
      (stageDeletedSet (N : Subgroup G)
        R.representative x i.castSucc) hrep)
  let hIterRep := isLocallyRepresentationFinite_deletion (k := k) C₁ T₁
    (isLocallyRepresentationFinite_deletion (k := k) C₀ ({y} : Set C₀)
      (isLocallyRepresentationFinite_deletion (k := k) C
        (stageDeletedSet (N : Subgroup G)
          R.representative x i.castSucc) hrep))
  let hEZ : Indecomposable (E.functor.obj Zfull) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      E.functor Zfull).2 hZfull
  let e := stageFullOrbitRestriction_iteratedIso
    (k := k) N R x i M hFull hSingleton hRemaining
  have hMap := finiteModuleLocalDensity_map_equivalence
    hIterRep hFullRep E Zfull hZfull
  have hIso := finiteModuleLocalDensity_eq_of_iso
    hIterRep hEZ hZ₂ e
  exact hMap.symm.trans hIso

/-- Vanishing at the distinguished representative together with the
separation theorem for its surviving orbit gives vanishing on the whole
subgroup orbit deleted at the successor step. -/
theorem stageTwoStepModule_vanishesOn_additionalDeleted
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n)
    (hvanish : ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      ({stageNextObject (k := k) R x i} :
        Set (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc))
      ((stageTwoStepModuleFamily (k := k) hrep R x i).obj t).obj.obj) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    ModuleVanishesOnDeleted
      (k := k)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc)
      (StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i)
      ((stageTwoStepModuleFamily (k := k) hrep R x i).obj t).obj.obj := by
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let T := StageAdditionalDeleted (k := k) (N : Subgroup G)
    R.representative x i
  let M := (stageTwoStepModuleFamily (k := k) hrep R x i).obj t
  let hremaining := stageTwoStepRestriction_vanishesOn_remainingOrbit
    (k := k) hP hlocal hrep N R x i havoid t hvanish
  intro z hz
  by_cases hzy : z = y
  · subst z
    exact hvanish y (by rfl)
  · let z' : DeletionCategory (k := k) C₀ ({y} : Set C₀) :=
      ⟨(rawFunctor (k := k) C₀ ({y} : Set C₀)).obj z, by
        change z ∉ ({y} : Set C₀)
        simpa only [Set.mem_singleton_iff] using hzy⟩
    have hz' : z' ∈ AdditionalDeleted (k := k) C₀ ({y} : Set C₀) T := hz
    have hzZero := hremaining z' hz'
    exact hzZero

set_option maxHeartbeats 1000000 in
/-- At every represented two-step endpoint, singleton deletion downstairs
has the same extended local density as singleton deletion at the
distinguished representative upstairs. -/
theorem stagePushedTwoStepModuleFamily_postLocalDensity
    [IsAlgClosed k]
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let y := stageNextObject (k := k) R x i
    let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
      (Quotient.mk'' y : MulAction.orbitRel.Quotient
        (N : Subgroup G) C₀)
    let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
    let P₂ := stagePushedTwoStepModuleFamily
      (k := k) (C := C) D hC hrep N R x i havoid
    let Down := stageFiniteOrbitModuleIndecomposableSkeleton
      (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
    finiteDeletionExtendedLocalDensity
        (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
        Down.isLocallyRepresentationFinite ({q} : Set _) (P₂.obj t)
          (P₂.indecomposable t) =
      finiteDeletionExtendedLocalDensity (k := k) C₀
        (isLocallyRepresentationFinite_deletion (k := k) C
          (stageDeletedSet (N : Subgroup G)
            R.representative x i.castSucc) hrep)
        ({y} : Set C₀) (W₂.obj t) (W₂.indecomposable t) := by
  let S := stageDeletedSet (N : Subgroup G)
    R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
    (Quotient.mk'' y : MulAction.orbitRel.Quotient
      (N : Subgroup G) C₀)
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let M := W₂.obj t
  let hM : Indecomposable M := W₂.indecomposable t
  let P₂ := stagePushedTwoStepModuleFamily
    (k := k) (C := C) D hC hrep N R x i havoid
  let hPM : Indecomposable (P₂.obj t) := P₂.indecomposable t
  let Down := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
  let hrep₀ := isLocallyRepresentationFinite_deletion
    (k := k) C S hrep
  let Pstage := Dstage.finiteDimensionalModuleOrbitSkeletonPushdown
    (k := k)
  have hPstageM : Indecomposable (Pstage.obj M) := by
    change Indecomposable (P₂.obj t)
    exact hPM
  by_cases hvanish : ModuleVanishesOnDeleted
      (k := k) C₀ ({y} : Set C₀) M.obj.obj
  · have hyZero : IsZero (M.obj.obj.obj y) := hvanish y (by simp)
    have hqZero : IsZero ((P₂.obj t).obj.obj.obj q) :=
      (stagePushedTwoStepModuleFamily_obj_isZero_iff
        (k := k) (C := C) D hC hP hlocal hrep N R x i havoid t).2 hyZero
    have hDownVanish : ModuleVanishesOnDeleted
        (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
        ({q} : Set _) (P₂.obj t).obj.obj := by
      intro z hz
      have hzq : z = q := by simpa only [Set.mem_singleton_iff] using hz
      subst z
      exact hqZero
    let hFull := stageTwoStepModule_vanishesOn_additionalDeleted
      (k := k) hP hlocal hrep N R x i havoid t hvanish
    let hRemaining := stageTwoStepRestriction_vanishesOn_remainingOrbit
      (k := k) hP hlocal hrep N R x i havoid t hvanish
    let C₁ := DeletionCategory (k := k) C₀ ({y} : Set C₀)
    let T₁ := AdditionalDeleted (k := k) C₀ ({y} : Set C₀)
      (StageAdditionalDeleted (k := k) (N : Subgroup G)
        R.representative x i)
    let Z₁ := finiteDimensionalModuleRestrictionToDeletion
      (k := k) C₀ ({y} : Set C₀) M hvanish
    let hZ₁ : Indecomposable Z₁ :=
      finiteDimensionalModuleRestrictionToDeletion_indec
        (k := k) C₀ ({y} : Set C₀) M hM hvanish
    let hrep₁ := isLocallyRepresentationFinite_deletion
      (k := k) C₀ ({y} : Set C₀) hrep₀
    have hDownFull := stageFullOrbitRestriction_downstairsLocalDensity
      (k := k) D hC hP hI hlocal hrep N R x i M hM hFull
        hPstageM hDownVanish
    have hFullIter := stageFullOrbitRestriction_iteratedLocalDensity
      (k := k) hrep N R x i M hM hFull hvanish hRemaining
    have hRemainingDensity :=
      stageTwoStepRestriction_remainingOrbitExtendedLocalDensity
        (k := k) hP hlocal hrep N R x i havoid t hvanish
    change finiteDeletionExtendedLocalDensity
        (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
        Down.isLocallyRepresentationFinite ({q} : Set _) (P₂.obj t) hPM =
      finiteDeletionExtendedLocalDensity (k := k) C₀ hrep₀
        ({y} : Set C₀) M hM
    rw [finiteDeletionExtendedLocalDensity, dif_pos hDownVanish,
      finiteDeletionExtendedLocalDensity, dif_pos hvanish]
    change finiteDeletionExtendedLocalDensity
        (k := k) C₁ hrep₁ T₁ Z₁ hZ₁ =
      finiteModuleLocalDensity hrep₁ Z₁ hZ₁
      at hRemainingDensity
    rw [finiteDeletionExtendedLocalDensity, dif_pos hRemaining]
      at hRemainingDensity
    exact hDownFull.trans (hFullIter.trans hRemainingDensity)
  · have hDownNonvanish : ¬ ModuleVanishesOnDeleted
        (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
        ({q} : Set _) (P₂.obj t).obj.obj := by
      intro hDownVanish
      apply hvanish
      intro z hz
      have hzy : z = y := by simpa only [Set.mem_singleton_iff] using hz
      subst z
      have hqZero : IsZero ((P₂.obj t).obj.obj.obj q) :=
        hDownVanish q (by simp)
      exact (stagePushedTwoStepModuleFamily_obj_isZero_iff
        (k := k) (C := C) D hC hP hlocal hrep N R x i havoid t).1 hqZero
    change finiteDeletionExtendedLocalDensity
        (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
        Down.isLocallyRepresentationFinite ({q} : Set _) (P₂.obj t) hPM =
      finiteDeletionExtendedLocalDensity (k := k) C₀ hrep₀
        ({y} : Set C₀) M hM
    rw [finiteDeletionExtendedLocalDensity, dif_neg hDownNonvanish,
      finiteDeletionExtendedLocalDensity, dif_neg hvanish]

/-- At every represented two-step endpoint, the downstairs singleton
deletion change is the corresponding upstairs stage-local change. -/
theorem stagePushedTwoStepModuleFamily_localChangeAt
    [IsAlgClosed k]
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (t : Fin (stageTwoStepModuleFamily (k := k) hrep R x i).n) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let y := stageNextObject (k := k) R x i
    let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
      (Quotient.mk'' y : MulAction.orbitRel.Quotient
        (N : Subgroup G) C₀)
    let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
    let P₂ := stagePushedTwoStepModuleFamily
      (k := k) (C := C) D hC hrep N R x i havoid
    let Down := stageFiniteOrbitModuleIndecomposableSkeleton
      (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
    finiteDeletionLocalChangeAt
        (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
        Down.isLocallyRepresentationFinite ({q} : Set _) (P₂.obj t)
          (P₂.indecomposable t) =
      finiteDeletionLocalChangeAt (k := k) C₀
        (isLocallyRepresentationFinite_deletion (k := k) C
          (stageDeletedSet (N : Subgroup G)
            R.representative x i.castSucc) hrep)
        ({y} : Set C₀) (W₂.obj t) (W₂.indecomposable t) := by
  let S := stageDeletedSet (N : Subgroup G)
    R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
    (Quotient.mk'' y : MulAction.orbitRel.Quotient
      (N : Subgroup G) C₀)
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let P₂ := stagePushedTwoStepModuleFamily
    (k := k) (C := C) D hC hrep N R x i havoid
  let Down := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
  let hrep₀ := isLocallyRepresentationFinite_deletion
    (k := k) C S hrep
  change finiteModuleLocalDensity Down.isLocallyRepresentationFinite
        (P₂.obj t) (P₂.indecomposable t) -
      finiteDeletionExtendedLocalDensity
        (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
        Down.isLocallyRepresentationFinite ({q} : Set _) (P₂.obj t)
          (P₂.indecomposable t) =
    finiteModuleLocalDensity hrep₀ (W₂.obj t) (W₂.indecomposable t) -
      finiteDeletionExtendedLocalDensity (k := k) C₀ hrep₀
        ({y} : Set C₀) (W₂.obj t) (W₂.indecomposable t)
  rw [stagePushedTwoStepModuleFamily_preLocalDensity
      (k := k) (C := C) D hC hP hI hlocal hrep N R x i havoid t,
    stagePushedTwoStepModuleFamily_postLocalDensity
      (k := k) (C := C) D hC hP hI hlocal hrep N R x i havoid t]

/-- The downstairs singleton-deletion sum over the pushed support family is
exactly the upstairs local change at this deletion stage. -/
theorem stagePushedTwoStepModuleFamily_localChangeSum
    [IsAlgClosed k]
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G)) :
    letI := stageMulAction (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x i.castSucc
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    let C₀ := StageCategory (k := k) (N : Subgroup G)
      R.representative x i.castSucc
    let y := stageNextObject (k := k) R x i
    let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
      (Quotient.mk'' y : MulAction.orbitRel.Quotient
        (N : Subgroup G) C₀)
    let P₂ := stagePushedTwoStepModuleFamily
      (k := k) (C := C) D hC hrep N R x i havoid
    let Down := stageFiniteOrbitModuleIndecomposableSkeleton
      (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
    finiteDeletionLocalChangeSum
        (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
        Down.isLocallyRepresentationFinite ({q} : Set _) P₂ =
      stageLocalChange (k := k) hrep R x i := by
  let S := stageDeletedSet (N : Subgroup G)
    R.representative x i.castSucc
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) Dstage.core
  letI := linearModuleCategoryHasShift (k := k) Dstage.core
  letI := linearModuleCategoryAdditiveShift (R := k) Dstage.core
  letI := linearModuleCategoryLinearShift (R := k) Dstage.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)
        (Additive (N : Subgroup G))) k)
    (Additive (N : Subgroup G))
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
    (Quotient.mk'' y : MulAction.orbitRel.Quotient
      (N : Subgroup G) C₀)
  let W₂ := stageTwoStepModuleFamily (k := k) hrep R x i
  let W₃ := deletionSurvivingModuleFamily (k := k) C
    (finiteThreeStepControlFamily hrep (R.representative i • x)) S
  let hW (r : Fin W₂.n) : W₃.additiveClosure (W₂.obj r) :=
    stageTwoStepModuleFamily_obj_mem_threeStepAdditiveClosure
      (k := k) hrep R x i r
  let P := Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow
    (k := k) W₃.additiveClosure
  have horthogonal : Dstage.FiniteModuleWindowShiftHomOrthogonal
      (k := k) W₃.additiveClosure :=
    stage_survivingModuleFamily_shiftHomOrthogonal_of_ambient_avoids
      (k := k) C D hC (N : Subgroup G) R.representative x i.castSucc
        (finiteThreeStepControlFamily hrep (R.representative i • x)) havoid
  let hFull : P.Full :=
    Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow_full
      (k := k) W₃.additiveClosure horthogonal
  let hFaithful : P.Faithful :=
    Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow_faithful
      (k := k) W₃.additiveClosure
  let hPushed (r : Fin W₂.n) :
      Indecomposable (P.obj ⟨W₂.obj r, hW r⟩) :=
    Dstage.finiteDimensionalModuleOrbitSkeletonPushdownWindow_obj_indecomposable
      (k := k) W₃.additiveClosure horthogonal
        ⟨W₂.obj r, hW r⟩ (W₂.indecomposable r)
  let P₂ := W₂.mapWindowFunctor W₃.additiveClosure hW P hPushed
  let Down := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
  change finiteDeletionLocalChangeSum
      (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
      Down.isLocallyRepresentationFinite ({q} : Set _) P₂ =
    finiteDeletionLocalChangeSum (k := k) C₀
      (isLocallyRepresentationFinite_deletion (k := k) C S hrep)
      ({y} : Set C₀) W₂
  unfold finiteDeletionLocalChangeSum
  let e : W₂.IsoClass ≃ P₂.IsoClass :=
    W₂.isoClassWindowEquiv W₃.additiveClosure hW P hPushed
      hFull hFaithful
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  induction r using Quotient.inductionOn with
  | _ t =>
      exact stagePushedTwoStepModuleFamily_localChangeAt
        (k := k) (C := C) D hC hP hI hlocal hrep N R x i havoid t

/-- The local change at one representative-deletion stage is exactly the
difference between the current and successor finite-orbit Auslander--Reiten
surpluses. -/
theorem stageLocalChange_eq_stageFiniteOrbitSurplus_sub
    [IsAlgClosed k]
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C)
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C) (i : Fin R.m)
    (havoid : ∀ g ∈ finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G)) :
    stageLocalChange (k := k) hrep R x i =
      stageFiniteOrbitSurplus
          (k := k) C D hC hP hI hlocal hrep N R x i.castSucc -
        stageFiniteOrbitSurplus
          (k := k) C D hC hP hI hlocal hrep N R x i.succ := by
  let S := stageDeletedSet (N : Subgroup G)
    R.representative x i.castSucc
  letI := (D.restrict (N : Subgroup G)).hasShift
  letI := (D.restrict (N : Subgroup G)).additiveShift
  letI := (D.restrict (N : Subgroup G)).linearShift (k := k)
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.castSucc) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.castSucc
  haveI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G) C) :=
    CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  haveI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc)) :=
    finite_deletionOrbitQuotient (k := k) C S
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) R.representative x i.castSucc)
  let Dcurrent := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.castSucc
  letI : ∀ a : Additive (N : Subgroup G),
      (Dcurrent.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI : ∀ a : Additive (N : Subgroup G),
      (Dcurrent.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC (N : Subgroup G) R.representative x i.castSucc a
  letI := Dcurrent.hasShift
  letI := Dcurrent.additiveShift
  letI := Dcurrent.linearShift (k := k)
  letI : Finite
      (DeckOrbitSkeleton
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.castSucc) (N : Subgroup G)) :=
    finite_deletionOrbitQuotient (k := k) C S
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) R.representative x i.castSucc)
  let C₀ := StageCategory (k := k) (N : Subgroup G)
    R.representative x i.castSucc
  let y := stageNextObject (k := k) R x i
  let q : DeckOrbitSkeleton C₀ (N : Subgroup G) :=
    (Quotient.mk'' y : MulAction.orbitRel.Quotient
      (N : Subgroup G) C₀)
  let P₂ := stagePushedTwoStepModuleFamily
    (k := k) (C := C) D hC hrep N R x i havoid
  let Down := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x i.castSucc
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hPdown := Dcurrent.orbitSkeletonLinearCoyonedaFinite (k := k) hPstage
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C₀ (N : Subgroup G)) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  have hsupport : ∀ r : Fin Down.n, Down.obj r ∉ P₂.isoClosure →
      finiteDeletionLocalChangeAt
        (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
        Down.isLocallyRepresentationFinite ({q} : Set _)
          (Down.obj r) (Down.indecomposable r) = 0 := by
    intro r hr
    exact stagePushedTwoStepModuleFamily_localChangeAt_eq_zero_of_not_mem
      (k := k) (C := C) D hC hP hI hlocal hrep N R x i havoid
        (Down.obj r) (Down.indecomposable r) hr
  let CurrentDeletion := DeletionCategory (k := k)
    (DeckOrbitSkeleton C₀ (N : Subgroup G)) ({q} : Set _)
  letI : Finite CurrentDeletion :=
    Finite.of_injective
      (fun X : CurrentDeletion ↦ X.obj.as)
      (fun X Y h ↦ by
        apply ObjectProperty.FullSubcategory.ext
        apply CategoryTheory.Quotient.ext
        exact h)
  let hPdeleted := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional
      (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
        hPdown ({q} : Set _) X
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := CurrentDeletion) k) :=
    enoughProjectives_of_finiteRepresentables hPdeleted
  let Snext := stageDeletedSet (N : Subgroup G)
    R.representative x i.succ
  letI := stageMulAction (k := k) (N : Subgroup G)
    R.representative x i.succ
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G)
        R.representative x i.succ) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x i.succ
  haveI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G)
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.succ)) :=
    finite_deletionOrbitQuotient (k := k) C Snext
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) R.representative x i.succ)
  let Dnext := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x i.succ
  letI := Dnext.hasShift
  letI := Dnext.additiveShift
  letI := Dnext.linearShift (k := k)
  letI : Finite
      (DeckOrbitSkeleton
        (StageCategory (k := k) (N : Subgroup G)
          R.representative x i.succ) (N : Subgroup G)) :=
    finite_deletionOrbitQuotient (k := k) C Snext
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) R.representative x i.succ)
  let Next := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x i.succ
  let hPnextStage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP Snext X
  let hPnext := Dnext.orbitSkeletonLinearCoyonedaFinite (k := k) hPnextStage
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton
          (StageCategory (k := k) (N : Subgroup G)
            R.representative x i.succ) (N : Subgroup G)) k) :=
    enoughProjectives_of_finiteRepresentables hPnext
  let eBase := stageOrbitSingletonToSuccEquivalence
    (k := k) D hC N R x i
  letI : eBase.functor.Additive := inferInstance
  letI : eBase.functor.Linear k := inferInstance
  let E := finiteDimensionalModuleCongrEquivalenceOfFinite
    (k := k) eBase
  letI : E.functor.Additive :=
    finiteDimensionalModuleCongrEquivalenceOfFinite_functor_additive
      (k := k) eBase
  let T := Next.mapEquivalence E
  have hsum := finiteDeletionLocalChangeSum_eq_surplus_sub
    (k := k) (DeckOrbitSkeleton C₀ (N : Subgroup G))
      Down.isLocallyRepresentationFinite ({q} : Set _) P₂ Down T hsupport
  have htransport := Next.surplus_mapEquivalence E
  rw [← stagePushedTwoStepModuleFamily_localChangeSum
      (k := k) (C := C) D hC hP hI hlocal hrep N R x i havoid,
    hsum, htransport]
  rfl


end MagnitudeConjecture.ObjectDeletion
