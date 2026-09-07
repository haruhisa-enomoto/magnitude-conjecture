import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteType
import MagnitudeConjecture.CategoryTheory.FiniteSkeletonDensityInvariance

/-!
# Finite indecomposable skeletons over orbit towers

An additive equivalence of finite-dimensional module categories transports a
duplicate-free complete indecomposable skeleton without changing its label
type.  The strict orbit-tower module equivalence therefore gives the
two-stage quotient a skeleton with exactly the direct quotient's coordinates.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton

universe u₁ u₂ v

variable {k : Type v} [Field k]
variable {C : Type u₁} [Category.{v} C] [Preadditive C]
variable {D : Type u₂} [Category.{v} D] [Preadditive D]
variable [CategoryTheory.Linear k C] [CategoryTheory.Linear k D]

/-- Transport a finite complete indecomposable skeleton along an additive
equivalence of finite-dimensional module categories. -/
noncomputable def mapEquivalence
    (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := D))
    (e : FiniteDimensionalModuleCategory.{u₂, v, v, v} (C := D) k ≌
      FiniteDimensionalModuleCategory.{u₁, v, v, v} (C := C) k)
    [e.functor.Additive] :
    FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C) where
  n := S.n
  obj i := e.functor.obj (S.obj i)
  indecomposable i :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      e.functor (S.obj i)).2 (S.indecomposable i)
  skeletal := by
    intro i j hij
    obtain ⟨hij⟩ := hij
    exact S.skeletal ⟨e.functor.preimageIso hij⟩
  complete := by
    intro M hM
    letI : e.inverse.Additive := inferInstance
    have hpre : Indecomposable (e.inverse.obj M) :=
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        e.inverse M).2 hM
    obtain ⟨i, ⟨hiso⟩⟩ := S.complete (e.inverse.obj M) hpre
    exact ⟨i, ⟨(e.counitIso.app M).symm ≪≫ e.functor.mapIso hiso⟩⟩

variable (S : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := D))
variable (e : FiniteDimensionalModuleCategory.{u₂, v, v, v} (C := D) k ≌
  FiniteDimensionalModuleCategory.{u₁, v, v, v} (C := C) k)
variable [e.functor.Additive]
variable [EnoughProjectives
  (FiniteDimensionalModuleCategory.{u₂, v, v, v} (C := D) k)]
variable [EnoughProjectives
  (FiniteDimensionalModuleCategory.{u₁, v, v, v} (C := C) k)]

/-- Incoming right-mesh arity is preserved when a finite indecomposable
skeleton is transported along an additive equivalence. -/
theorem rightMiddleArity_mapEquivalence (i : Fin S.n) :
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        (S.mapEquivalence e).toFiniteRightTauCategoryData i =
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
        S.toFiniteRightTauCategoryData i := by
  let T := S.toFiniteRightTauCategoryData
  let T' := (S.mapEquivalence e).toFiniteRightTauCategoryData
  let d :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition
      T i
  let dMap := d.mapOfIndecomposable e.functor fun j ↦
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      e.functor (d.summand j)).2 (d.indecomposable j)
  let m := (T.rightMesh (T.obj i)).g ≫ (T.rightTermIso (T.obj i)).hom
  have hmAS : IsRightAlmostSplit m :=
    MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit T i
  have hmMin : IsRightMinimal m :=
    MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightMinimal T i
  have hmapAS : IsRightAlmostSplit (e.functor.map m) := hmAS.map_equivalence e
  have hmapMin : IsRightMinimal (e.functor.map m) := hmMin.map_equivalence e
  exact
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      T' i dMap hmapAS hmapMin

/-- The finite-right-tau projectivity predicate is preserved when a finite
indecomposable skeleton is transported along an additive equivalence. -/
theorem isProjective_mapEquivalence_iff (i : Fin S.n) :
    (S.mapEquivalence e).toFiniteRightTauCategoryData.IsProjective i ↔
      S.toFiniteRightTauCategoryData.IsProjective i := by
  rw [MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj,
    MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj]
  exact e.map_projective_iff (S.obj i)

/-- Right-tau local density is preserved labelwise under transport of the
finite indecomposable skeleton along an additive equivalence. -/
theorem rightTauLocalDensity_mapEquivalence (i : Fin S.n) :
    (S.mapEquivalence e).rightTauLocalDensity i =
      S.rightTauLocalDensity i := by
  classical
  rw [rightTauLocalDensity, rightTauLocalDensity,
    MagnitudeConjecture.FiniteTauMatrix.occurrenceLocalDensity_rightArrowTarget_eq,
    MagnitudeConjecture.FiniteTauMatrix.occurrenceLocalDensity_rightArrowTarget_eq,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    S.rightMiddleArity_mapEquivalence e i]
  by_cases h : S.toFiniteRightTauCategoryData.IsProjective i
  · have h' :
        (S.mapEquivalence e).toFiniteRightTauCategoryData.IsProjective i :=
      (S.isProjective_mapEquivalence_iff e i).2 h
    simp [h, h']
  · have h' :
        ¬ (S.mapEquivalence e).toFiniteRightTauCategoryData.IsProjective i := by
      simpa only [S.isProjective_mapEquivalence_iff e i] using h
    simp [h, h']

/-- Transporting a complete finite indecomposable skeleton along an additive
equivalence preserves its Auslander--Reiten surplus. -/
theorem surplus_mapEquivalence :
    @MagnitudeConjecture.ARCount.surplus (Fin (S.mapEquivalence e).n)
        inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          (S.mapEquivalence e).toFiniteRightTauCategoryData)
        (S.mapEquivalence e).toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) =
      @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          S.toFiniteRightTauCategoryData)
        S.toFiniteRightTauCategoryData.IsProjective
        (Classical.decPred _) := by
  rw [← (S.mapEquivalence e).sum_rightTauLocalDensity_eq_surplus,
    ← S.sum_rightTauLocalDensity_eq_surplus]
  apply Finset.sum_congr rfl
  intro i _
  exact S.rightTauLocalDensity_mapEquivalence e i

include e in
/-- Any two complete indecomposable skeletons related by an additive
equivalence of finite-dimensional module categories have the same
Auslander--Reiten surplus. -/
theorem surplus_eq_of_equivalence
    (T : FiniteDimensionalModuleIndecomposableSkeleton (k := k) (C := C)) :
    @MagnitudeConjecture.ARCount.surplus (Fin T.n) inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData)
        T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
      @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          S.toFiniteRightTauCategoryData)
        S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) := by
  calc
    @MagnitudeConjecture.ARCount.surplus (Fin T.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData)
          T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) =
        @MagnitudeConjecture.ARCount.surplus (Fin (S.mapEquivalence e).n)
          inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            (S.mapEquivalence e).toFiniteRightTauCategoryData)
          (S.mapEquivalence e).toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) := by
      rw [← T.sum_rightTauLocalDensity_eq_surplus,
        ← (S.mapEquivalence e).sum_rightTauLocalDensity_eq_surplus]
      exact T.sum_rightTauLocalDensity_eq (S.mapEquivalence e)
    _ = @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            S.toFiniteRightTauCategoryData)
          S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) :=
      S.surplus_mapEquivalence e

end MagnitudeConjecture.CoveringHom.FiniteDimensionalModuleIndecomposableSkeleton

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {k : Type (max v w)} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {G : Type w} [Group G] [MulAction G C]
variable [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Transport a direct strict-orbit indecomposable skeleton to the two-stage
strict orbit tower, retaining the same finite label type. -/
noncomputable def deckOrbitTowerIndecomposableSkeleton
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
    FiniteDimensionalModuleIndecomposableSkeleton
        (k := k) (C := DeckOrbitSkeleton C G) →
      FiniteDimensionalModuleIndecomposableSkeleton
        (k := k)
        (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N)) := by
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
  intro S
  let e :
      FiniteDimensionalModuleCategory.{u, max v w, max v w, max v w}
          (C := DeckOrbitSkeleton C G) k ≌
        FiniteDimensionalModuleCategory.{u, max v w, max v w, max v w}
          (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N)) k :=
    D.deckOrbitTowerFiniteDimensionalModuleEquivalence (k := k) N
  letI : e.functor.Additive := by
    dsimp only [e]
    unfold deckOrbitTowerFiniteDimensionalModuleEquivalence
    infer_instance
  exact S.mapEquivalence e

/-- Transport through the strict orbit-tower equivalence preserves the
right-tau local density at every retained skeleton label. -/
theorem deckOrbitTowerIndecomposableSkeleton_rightTauLocalDensity
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
    ∀ [EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, max v w, max v w, max v w}
          (C := DeckOrbitSkeleton C G) k)]
      [EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, max v w, max v w, max v w}
          (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N)) k)]
      (S : FiniteDimensionalModuleIndecomposableSkeleton
        (k := k) (C := DeckOrbitSkeleton C G))
      (i : Fin S.n),
    (D.deckOrbitTowerIndecomposableSkeleton (k := k) N S).rightTauLocalDensity i =
      S.rightTauLocalDensity i := by
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
  intro _ _ S i
  let e := D.deckOrbitTowerFiniteDimensionalModuleEquivalence (k := k) N
  letI : e.functor.Additive := by
    dsimp only [e]
    unfold deckOrbitTowerFiniteDimensionalModuleEquivalence
    infer_instance
  exact S.rightTauLocalDensity_mapEquivalence e i

/-- Every complete indecomposable skeleton on the two-stage strict orbit has
the same total right-tau local density as every complete skeleton on the
direct strict orbit. -/
theorem sum_rightTauLocalDensity_eq_deckOrbitTower
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
    ∀ [EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, max v w, max v w, max v w}
          (C := DeckOrbitSkeleton C G) k)]
      [EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, max v w, max v w, max v w}
          (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N)) k)]
      (S : FiniteDimensionalModuleIndecomposableSkeleton
        (k := k) (C := DeckOrbitSkeleton C G))
      (T : FiniteDimensionalModuleIndecomposableSkeleton
        (k := k)
        (C := DeckOrbitSkeleton (DeckOrbitSkeleton C N) (G ⧸ N))),
    (∑ j : Fin T.n, T.rightTauLocalDensity j) =
      ∑ i : Fin S.n, S.rightTauLocalDensity i := by
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
  intro _ _ S T
  let ST := D.deckOrbitTowerIndecomposableSkeleton (k := k) N S
  calc
    (∑ j : Fin T.n, T.rightTauLocalDensity j) =
        ∑ i : Fin ST.n, ST.rightTauLocalDensity i :=
      T.sum_rightTauLocalDensity_eq ST
    _ = ∑ i : Fin S.n, S.rightTauLocalDensity i := by
      apply Finset.sum_congr rfl
      intro i _
      exact D.deckOrbitTowerIndecomposableSkeleton_rightTauLocalDensity N S i

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
