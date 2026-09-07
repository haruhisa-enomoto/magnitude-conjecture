import MagnitudeConjecture.CategoryTheory.FiniteOrbitResidualEndpoint
import MagnitudeConjecture.CategoryTheory.FiniteModuleControlWindowEquivariance
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStageTelescope

/-!
# Endpoint normalization for the finite covering telescope

The first subgroup-orbit stage is the undeleted ambient category, and the
last is deletion of the full ambient orbit.  This file transports the literal
finite-stage module skeletons across those base equivalences and applies the
residual finite-cover scaling theorem.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]

omit [IsAlgClosed k] [IsCancelSMul G C] in
/-- The fixed deck-orbit model of stage zero deletes no orbit classes. -/
theorem stageDeckDeletedSet_zero
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (N : Subgroup G) {m : ℕ} (representative : Fin m → G) (x : C) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    stageDeckDeletedSet N representative x 0 = ∅ := by
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  rw [stageDeckDeletedSet, stageDeletedSet_zero]
  rfl

/-- At stage zero, the actual subgroup deck-orbit skeleton is equivalent to
the undeleted subgroup deck-orbit skeleton. -/
noncomputable def stageZeroDeckOrbitEquivalence
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) (N : Subgroup G) {m : ℕ}
    (representative : Fin m → G) (x : C) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x 0
    let SD := stageCoherentDeckShift
      (k := k) D hC N representative x 0
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    DeckOrbitSkeleton (StageCategory (k := k) N representative x 0) N ≌
      DeckOrbitSkeleton C N := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := stageMulAction (k := k) N representative x 0
  let SD := stageCoherentDeckShift (k := k) D hC N representative x 0
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  exact (stageDeckOrbitNormalizedEquivalence
    (k := k) N D hC representative x 0).trans
      ((deletionEquivalenceOfEq (k := k) (DeckOrbitSkeleton C N)
        (stageDeckDeletedSet_zero
          (k := k) D N representative x)).trans
        (emptyDeletionEquivalence (k := k) (DeckOrbitSkeleton C N)).symm)

noncomputable instance stageZeroDeckOrbitEquivalence_functor_additive
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) (N : Subgroup G) {m : ℕ}
    (representative : Fin m → G) (x : C) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x 0
    let SD := stageCoherentDeckShift
      (k := k) D hC N representative x 0
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    (stageZeroDeckOrbitEquivalence
      (k := k) D hC N representative x).functor.Additive := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := stageMulAction (k := k) N representative x 0
  let SD := stageCoherentDeckShift (k := k) D hC N representative x 0
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  let e₁ := stageDeckOrbitNormalizedEquivalence
    (k := k) N D hC representative x 0
  let e₂ := deletionEquivalenceOfEq (k := k) (DeckOrbitSkeleton C N)
    (stageDeckDeletedSet_zero (k := k) D N representative x)
  let eEmpty := emptyDeletionEquivalence (k := k) (DeckOrbitSkeleton C N)
  let e₃ := eEmpty.symm
  letI : e₁.functor.Additive := by
    dsimp only [e₁]
    exact stageDeckOrbitNormalizedFunctor_additive
      (k := k) N D hC representative x 0
  letI : e₂.functor.Additive := inferInstance
  letI : eEmpty.functor.Additive := by
    change (emptyDeletionFunctor (k := k) (DeckOrbitSkeleton C N)).Additive
    infer_instance
  letI : e₃.functor.Additive := by
    change eEmpty.inverse.Additive
    infer_instance
  change (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor)).Additive
  infer_instance

noncomputable instance stageZeroDeckOrbitEquivalence_functor_linear
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) (N : Subgroup G) {m : ℕ}
    (representative : Fin m → G) (x : C) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    letI := stageMulAction (k := k) N representative x 0
    let SD := stageCoherentDeckShift
      (k := k) D hC N representative x 0
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    (stageZeroDeckOrbitEquivalence
      (k := k) D hC N representative x).functor.Linear k := by
  dsimp
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  letI := stageMulAction (k := k) N representative x 0
  let SD := stageCoherentDeckShift (k := k) D hC N representative x 0
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  let e₁ := stageDeckOrbitNormalizedEquivalence
    (k := k) N D hC representative x 0
  let e₂ := deletionEquivalenceOfEq (k := k) (DeckOrbitSkeleton C N)
    (stageDeckDeletedSet_zero (k := k) D N representative x)
  let eEmpty := emptyDeletionEquivalence (k := k) (DeckOrbitSkeleton C N)
  let e₃ := eEmpty.symm
  letI : e₁.functor.Linear k := by
    dsimp only [e₁]
    exact stageDeckOrbitNormalizedFunctor_linear
      (k := k) N D hC representative x 0
  letI : e₂.functor.Linear k := inferInstance
  letI : eEmpty.functor.Linear k := by
    change (emptyDeletionFunctor
      (k := k) (DeckOrbitSkeleton C N)).Linear k
    infer_instance
  letI : e₃.functor.Linear k := by
    change eEmpty.inverse.Linear k
    infer_instance
  change (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor)).Linear k
  infer_instance

set_option maxHeartbeats 1200000 in
/-- The stage-zero surplus is the canonical finite subgroup-orbit surplus. -/
theorem stageFiniteOrbitSurplus_zero_eq_restrict
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
    (x : C) :
    let N' : Subgroup G := N
    letI : Finite (MulAction.orbitRel.Quotient N' C) :=
      MagnitudeConjecture.CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
    let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hP hlocal
    stageFiniteOrbitSurplus
        (k := k) C D hC hP hI hlocal hrep N R x 0 =
      (D.restrict N').finiteOrbitSurplus
        (k := k) hP hI hlocal (hfree.restrict N') hrep := by
  let N' : Subgroup G := N
  letI : Finite (MulAction.orbitRel.Quotient N' C) :=
    MagnitudeConjecture.CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N').hasShift
  letI := (D.restrict N').additiveShift
  letI := (D.restrict N').linearShift (k := k)
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  let hfreeN := hfree.restrict N'
  let Szero := stageDeletedSet N' R.representative x 0
  letI := stageMulAction (k := k) N' R.representative x 0
  haveI : IsCancelSMul N'
      (StageCategory (k := k) N' R.representative x 0) :=
    stageIsCancelSMul (k := k) N' R.representative x 0
  let Dzero := stageCoherentDeckShift
    (k := k) D hC N' R.representative x 0
  letI := Dzero.hasShift
  letI := Dzero.additiveShift
  letI := Dzero.linearShift (k := k)
  letI : ∀ a : Additive N', (Dzero.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC N' R.representative x 0 a
  letI : ∀ a : Additive N', (Dzero.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC N' R.representative x 0 a
  letI : Finite
      (DeckOrbitSkeleton
        (StageCategory (k := k) N' R.representative x 0) N') :=
    finite_deletionOrbitQuotient (k := k) C Szero
      (stageDeletedSet_actionInvariant N' R.representative x 0)
  letI : Finite (DeckOrbitSkeleton C N') :=
    MagnitudeConjecture.CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  let Stage := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x 0
  let Source := (D.restrict N').finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfreeN hrep
  let hPzero := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP Szero X
  let hPStage := Dzero.orbitSkeletonLinearCoyonedaFinite (k := k) hPzero
  let hPN := (D.restrict N').orbitSkeletonLinearCoyonedaFinite (k := k) hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton
          (StageCategory (k := k) N' R.representative x 0) N') k) :=
    enoughProjectives_of_finiteRepresentables hPStage
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C N') k) :=
    enoughProjectives_of_finiteRepresentables hPN
  let eBase := stageZeroDeckOrbitEquivalence
    (k := k) D hC N' R.representative x
  letI : eBase.functor.Additive := inferInstance
  letI : eBase.functor.Linear k := inferInstance
  let E := finiteDimensionalModuleCongrEquivalenceOfFinite (k := k) eBase
  letI : E.functor.Additive :=
    finiteDimensionalModuleCongrEquivalenceOfFinite_functor_additive
      (k := k) eBase
  exact Source.surplus_eq_of_equivalence E Stage

set_option maxHeartbeats 2200000 in
/-- The first literal stage surplus is the residual covering degree times the
surplus of the full deck-orbit category. -/
theorem stageFiniteOrbitSurplus_zero_eq_card_mul
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
    (x : C) :
    letI : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
    let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hP hlocal
    stageFiniteOrbitSurplus
        (k := k) C D hC hP hI hlocal hrep N R x 0 =
      (Fintype.card (G ⧸ (N : Subgroup G)) : ℤ) *
        D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep := by
  let N' : Subgroup G := N
  letI : Finite (MulAction.orbitRel.Quotient N' C) :=
    MagnitudeConjecture.CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  letI : Fintype (G ⧸ N') := Fintype.ofFinite _
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  exact (stageFiniteOrbitSurplus_zero_eq_restrict
    (k := k) (C := C) D hC hP hI hlocal hrep N R x).trans
      (D.finiteOrbitSurplus_restrict_eq_card_mul
        (k := k) hP hI hlocal hfree hrep N)

omit [Category.{v} C] [Preadditive C] [IsAlgClosed k]
  [IsCancelSMul G C] in
/-- A full orbit is invariant under the ambient group action. -/
theorem fullOrbit_actionInvariant (x : C) :
    ActionInvariant (G := G) (MulAction.orbit G x) := by
  intro g Y
  rw [← MulAction.orbit_eq_iff, ← MulAction.orbit_eq_iff,
    MulAction.orbit_smul]

omit [Category.{v} C] [Preadditive C] [IsAlgClosed k]
  [IsCancelSMul G C] in
/-- A full ambient orbit is also invariant under every subgroup action. -/
theorem fullOrbit_subgroup_actionInvariant (N : Subgroup G) (x : C) :
    ActionInvariant (G := N) (MulAction.orbit G x) := by
  intro n Y
  simpa only [MulAction.subgroup_smul_def] using
    (fullOrbit_actionInvariant (G := G) x (n : G) Y)

/-- The finite-orbit Auslander--Reiten surplus after deleting one complete
ambient deck orbit.  This is the manuscript's terminal quantity
`sigma(Abar / Abar e Abar)`. -/
noncomputable def fullOrbitDeletionFiniteOrbitSurplus
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
    (x : C) : ℤ := by
  let S := MulAction.orbit G x
  let hSG := fullOrbit_actionInvariant (G := G) x
  letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
    isClosedUnderIsomorphisms_of_skeletal hC S
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := deletionMulAction (k := k) S hSG
  haveI : IsCancelSMul G (DeletionCategory (k := k) C S) :=
    deletionIsCancelSMul (k := k) S hSG
  let DG := CoherentDeckShift.deletionCoherentDeckShift (k := k) D S hSG
  letI : ∀ a : Additive G, (DG.core.F a).Additive :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_additive
      (k := k) D S hSG a
  letI : ∀ a : Additive G, (DG.core.F a).Linear k :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_linear
      (k := k) D S hSG a
  letI : Finite
      (MulAction.orbitRel.Quotient G (DeletionCategory (k := k) C S)) :=
    finite_deletionOrbitQuotient (k := k) C S hSG
  let hPdel := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hIdel := fun X ↦
    deletion_dualLinearYoneda_isFiniteDimensional (k := k) C hI S X
  let hlocalDel := fun X ↦
    deletion_end_isLocalRing (k := k) C hC hlocal S X
  let hrepDel := isLocallyRepresentationFinite_deletion (k := k) C S hrep
  let hfreeDel := DG.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hPdel hlocalDel
  exact DG.finiteOrbitSurplus
    (k := k) hPdel hIdel hlocalDel hfreeDel hrepDel

omit [IsAlgClosed k] [IsCancelSMul G C] in
/-- At the terminal stage, the fixed deck-orbit model deletes exactly the
deck classes represented by the full ambient orbit. -/
theorem stageDeckDeletedSet_last_eq_fullOrbit
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (N : Subgroup G) [N.Normal]
    (R : FiniteQuotientRepresentatives N) (x : C) :
    letI := (D.restrict N).hasShift
    letI := (D.restrict N).additiveShift
    letI := (D.restrict N).linearShift (k := k)
    stageDeckDeletedSet N R.representative x (Fin.last R.m) =
      deckOrbitDeletedSet (G := N) (MulAction.orbit G x) := by
  letI := (D.restrict N).hasShift
  letI := (D.restrict N).additiveShift
  letI := (D.restrict N).linearShift (k := k)
  rw [stageDeckDeletedSet, R.stageDeletedSet_last_eq_orbit]

set_option backward.isDefEq.respectTransparency false in
/-- The actual terminal subgroup deck-orbit skeleton is equivalent to the
subgroup deck-orbit skeleton after deletion of the full ambient orbit. -/
noncomputable def stageLastDeckOrbitEquivalence
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G)) (x : C) :
    let N' : Subgroup G := N
    let S := MulAction.orbit G x
    let hSN := fullOrbit_subgroup_actionInvariant N' x
    letI := (D.restrict N').hasShift
    letI := (D.restrict N').additiveShift
    letI := (D.restrict N').linearShift (k := k)
    letI := stageMulAction (k := k) N' R.representative x (Fin.last R.m)
    let SD := stageCoherentDeckShift
      (k := k) D hC N' R.representative x (Fin.last R.m)
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
      isClosedUnderIsomorphisms_of_skeletal hC S
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
      (D.restrict N') S hSN
    letI := rawHasShift (k := k) S hShift
    letI : ∀ a : Additive N',
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
    letI : ∀ a : Additive N',
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
    letI := deletionHasShift (k := k) S hShift
    letI : ∀ a : Additive N',
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hShift a
    letI : ∀ a : Additive N',
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hShift a
    letI := deletionMulAction (k := k) S hSN
    DeckOrbitSkeleton
        (StageCategory (k := k) N' R.representative x (Fin.last R.m)) N' ≌
      DeckOrbitSkeleton (DeletionCategory (k := k) C S) N' := by
  dsimp
  let N' : Subgroup G := N
  let S := MulAction.orbit G x
  let hSN := fullOrbit_subgroup_actionInvariant N' x
  letI := (D.restrict N').hasShift
  letI := (D.restrict N').additiveShift
  letI := (D.restrict N').linearShift (k := k)
  letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
    isClosedUnderIsomorphisms_of_skeletal hC S
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
    (D.restrict N') S hSN
  letI := rawHasShift (k := k) S hShift
  letI : ∀ a : Additive N',
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
  letI : ∀ a : Additive N',
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
  letI := deletionHasShift (k := k) S hShift
  letI : ∀ a : Additive N',
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hShift a
  letI : ∀ a : Additive N',
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hShift a
  letI := stageMulAction
    (k := k) N' R.representative x (Fin.last R.m)
  let SD := stageCoherentDeckShift
    (k := k) D hC N' R.representative x (Fin.last R.m)
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  letI := deletionMulAction (k := k) S hSN
  exact (stageDeckOrbitNormalizedEquivalence
    (k := k) N' D hC R.representative x (Fin.last R.m)).trans
      ((deletionEquivalenceOfEq (k := k) (DeckOrbitSkeleton C N')
        (stageDeckDeletedSet_last_eq_fullOrbit
          (k := k) D N' R x)).trans
        (deckOrbitDeletionCommEquivalence
          (k := k) (D.restrict N') S hSN).symm)

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance stageLastDeckOrbitEquivalence_functor_additive
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G)) (x : C) :
    let N' : Subgroup G := N
    let S := MulAction.orbit G x
    let hSN := fullOrbit_subgroup_actionInvariant N' x
    letI := (D.restrict N').hasShift
    letI := (D.restrict N').additiveShift
    letI := (D.restrict N').linearShift (k := k)
    letI := stageMulAction (k := k) N' R.representative x (Fin.last R.m)
    let SD := stageCoherentDeckShift
      (k := k) D hC N' R.representative x (Fin.last R.m)
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
      isClosedUnderIsomorphisms_of_skeletal hC S
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
      (D.restrict N') S hSN
    letI := rawHasShift (k := k) S hShift
    letI : ∀ a : Additive N',
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
    letI : ∀ a : Additive N',
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
    letI := deletionHasShift (k := k) S hShift
    letI : ∀ a : Additive N',
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hShift a
    letI : ∀ a : Additive N',
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hShift a
    letI := deletionMulAction (k := k) S hSN
    (stageLastDeckOrbitEquivalence
      (k := k) D hC N R x).functor.Additive := by
  dsimp
  let N' : Subgroup G := N
  let S := MulAction.orbit G x
  let hSN := fullOrbit_subgroup_actionInvariant N' x
  letI := (D.restrict N').hasShift
  letI := (D.restrict N').additiveShift
  letI := (D.restrict N').linearShift (k := k)
  letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
    isClosedUnderIsomorphisms_of_skeletal hC S
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
    (D.restrict N') S hSN
  letI := rawHasShift (k := k) S hShift
  letI : ∀ a : Additive N',
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
  letI : ∀ a : Additive N',
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
  letI := deletionHasShift (k := k) S hShift
  letI : ∀ a : Additive N',
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hShift a
  letI : ∀ a : Additive N',
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hShift a
  letI := stageMulAction
    (k := k) N' R.representative x (Fin.last R.m)
  let SD := stageCoherentDeckShift
    (k := k) D hC N' R.representative x (Fin.last R.m)
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  letI := deletionMulAction (k := k) S hSN
  let e₁ := stageDeckOrbitNormalizedEquivalence
    (k := k) N' D hC R.representative x (Fin.last R.m)
  let e₂ := deletionEquivalenceOfEq (k := k) (DeckOrbitSkeleton C N')
    (stageDeckDeletedSet_last_eq_fullOrbit (k := k) D N' R x)
  let eComm := deckOrbitDeletionCommEquivalence
    (k := k) (D.restrict N') S hSN
  let e₃ := eComm.symm
  letI : e₁.functor.Additive := by
    dsimp only [e₁]
    exact stageDeckOrbitNormalizedFunctor_additive
      (k := k) N' D hC R.representative x (Fin.last R.m)
  letI : e₂.functor.Additive := inferInstance
  letI : eComm.functor.Additive :=
    deckOrbitDeletionCommEquivalence_functor_additive
      (k := k) (D.restrict N') S hSN
  letI : e₃.functor.Additive := by
    change eComm.inverse.Additive
    infer_instance
  change (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor)).Additive
  infer_instance

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance stageLastDeckOrbitEquivalence_functor_linear
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (hC : Skeletal C) (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G)) (x : C) :
    let N' : Subgroup G := N
    let S := MulAction.orbit G x
    let hSN := fullOrbit_subgroup_actionInvariant N' x
    letI := (D.restrict N').hasShift
    letI := (D.restrict N').additiveShift
    letI := (D.restrict N').linearShift (k := k)
    letI := stageMulAction (k := k) N' R.representative x (Fin.last R.m)
    let SD := stageCoherentDeckShift
      (k := k) D hC N' R.representative x (Fin.last R.m)
    letI := SD.hasShift
    letI := SD.additiveShift
    letI := SD.linearShift (k := k)
    letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
      isClosedUnderIsomorphisms_of_skeletal hC S
    let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
      (D.restrict N') S hSN
    letI := rawHasShift (k := k) S hShift
    letI : ∀ a : Additive N',
        (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
      fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
    letI : ∀ a : Additive N',
        (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
      fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
    letI := deletionHasShift (k := k) S hShift
    letI : ∀ a : Additive N',
        (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
      fun a ↦ deletionShift_additive (k := k) S hShift a
    letI : ∀ a : Additive N',
        (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
      fun a ↦ deletionShift_linear (k := k) S hShift a
    letI := deletionMulAction (k := k) S hSN
    (stageLastDeckOrbitEquivalence
      (k := k) D hC N R x).functor.Linear k := by
  dsimp
  let N' : Subgroup G := N
  let S := MulAction.orbit G x
  let hSN := fullOrbit_subgroup_actionInvariant N' x
  letI := (D.restrict N').hasShift
  letI := (D.restrict N').additiveShift
  letI := (D.restrict N').linearShift (k := k)
  letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
    isClosedUnderIsomorphisms_of_skeletal hC S
  let hShift := CoherentDeckShift.shiftInvariant_of_actionInvariant
    (D.restrict N') S hSN
  letI := rawHasShift (k := k) S hShift
  letI : ∀ a : Additive N',
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hShift a
  letI : ∀ a : Additive N',
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hShift a
  letI := deletionHasShift (k := k) S hShift
  letI : ∀ a : Additive N',
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hShift a
  letI : ∀ a : Additive N',
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hShift a
  letI := stageMulAction
    (k := k) N' R.representative x (Fin.last R.m)
  let SD := stageCoherentDeckShift
    (k := k) D hC N' R.representative x (Fin.last R.m)
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  letI := deletionMulAction (k := k) S hSN
  let e₁ := stageDeckOrbitNormalizedEquivalence
    (k := k) N' D hC R.representative x (Fin.last R.m)
  let e₂ := deletionEquivalenceOfEq (k := k) (DeckOrbitSkeleton C N')
    (stageDeckDeletedSet_last_eq_fullOrbit (k := k) D N' R x)
  let eComm := deckOrbitDeletionCommEquivalence
    (k := k) (D.restrict N') S hSN
  let e₃ := eComm.symm
  letI : e₁.functor.Linear k := by
    dsimp only [e₁]
    exact stageDeckOrbitNormalizedFunctor_linear
      (k := k) N' D hC R.representative x (Fin.last R.m)
  letI : e₂.functor.Linear k := inferInstance
  letI : eComm.functor.Linear k :=
    deckOrbitDeletionCommEquivalence_functor_linear
      (k := k) (D.restrict N') S hSN
  letI : e₃.functor.Linear k := by
    change eComm.inverse.Linear k
    infer_instance
  change (e₁.functor ⋙ (e₂.functor ⋙ e₃.functor)).Linear k
  infer_instance

set_option maxHeartbeats 6000000 in
/-- The terminal literal stage surplus is the residual covering degree times
the surplus after deleting the complete ambient deck orbit. -/
theorem stageFiniteOrbitSurplus_last_eq_card_mul
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
    (x : C) :
    letI : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
    stageFiniteOrbitSurplus
        (k := k) C D hC hP hI hlocal hrep N R x (Fin.last R.m) =
      (Fintype.card (G ⧸ (N : Subgroup G)) : ℤ) *
        fullOrbitDeletionFiniteOrbitSurplus
          (k := k) D hC hP hI hlocal hrep x := by
  let N' : Subgroup G := N
  let S := MulAction.orbit G x
  let hSG := fullOrbit_actionInvariant (G := G) x
  let hSN := fullOrbit_subgroup_actionInvariant N' x
  letI : ObjectProperty.IsClosedUnderIsomorphisms S :=
    isClosedUnderIsomorphisms_of_skeletal hC S
  letI : Finite (MulAction.orbitRel.Quotient N' C) :=
    MagnitudeConjecture.CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  letI : Fintype (G ⧸ N') := Fintype.ofFinite _
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N').hasShift
  letI := (D.restrict N').additiveShift
  letI := (D.restrict N').linearShift (k := k)
  let j := Fin.last R.m
  let Slast := stageDeletedSet N' R.representative x j
  letI := stageMulAction (k := k) N' R.representative x j
  haveI : IsCancelSMul N'
      (StageCategory (k := k) N' R.representative x j) :=
    stageIsCancelSMul (k := k) N' R.representative x j
  let SD := stageCoherentDeckShift
    (k := k) D hC N' R.representative x j
  letI := SD.hasShift
  letI := SD.additiveShift
  letI := SD.linearShift (k := k)
  letI : ∀ a : Additive N', (SD.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC N' R.representative x j a
  letI : ∀ a : Additive N', (SD.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC N' R.representative x j a
  let hShiftN := CoherentDeckShift.shiftInvariant_of_actionInvariant
    (D.restrict N') S hSN
  letI := rawHasShift (k := k) S hShiftN
  letI : ∀ a : Additive N',
      (shiftFunctor (RawCategory (k := k) C S) a).Additive :=
    fun a ↦ rawShiftFunctor_additive (k := k) S hShiftN a
  letI : ∀ a : Additive N',
      (shiftFunctor (RawCategory (k := k) C S) a).Linear k :=
    fun a ↦ rawShiftFunctor_linear (k := k) S hShiftN a
  letI := deletionHasShift (k := k) S hShiftN
  letI : ∀ a : Additive N',
      (shiftFunctor (DeletionCategory (k := k) C S) a).Additive :=
    fun a ↦ deletionShift_additive (k := k) S hShiftN a
  letI : ∀ a : Additive N',
      (shiftFunctor (DeletionCategory (k := k) C S) a).Linear k :=
    fun a ↦ deletionShift_linear (k := k) S hShiftN a
  letI := deletionMulAction (k := k) S hSN
  haveI : IsCancelSMul N' (DeletionCategory (k := k) C S) :=
    deletionIsCancelSMul (k := k) S hSN
  let DN := CoherentDeckShift.deletionCoherentDeckShift
    (k := k) (D.restrict N') S hSN
  let hDNHas : DN.hasShift = deletionHasShift (k := k) S hShiftN :=
    CoherentDeckShift.deletionCoherentDeckShift_hasShift_eq
      (k := k) (D.restrict N') S hSN
  letI : ∀ a : Additive N', (DN.core.F a).Additive :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_additive
      (k := k) (D.restrict N') S hSN a
  letI : ∀ a : Additive N', (DN.core.F a).Linear k :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_linear
      (k := k) (D.restrict N') S hSN a
  letI : Finite
      (MulAction.orbitRel.Quotient N'
        (DeletionCategory (k := k) C S)) :=
    finite_deletionOrbitQuotient (k := k) C S hSN
  letI : Finite
      (MulAction.orbitRel.Quotient N'
        (StageCategory (k := k) N' R.representative x j)) :=
    finite_deletionOrbitQuotient (k := k) C Slast
      (stageDeletedSet_actionInvariant N' R.representative x j)
  letI : Finite
      (DeckOrbitSkeleton
        (StageCategory (k := k) N' R.representative x j) N') :=
    finite_deletionOrbitQuotient (k := k) C Slast
      (stageDeletedSet_actionInvariant N' R.representative x j)
  letI : Finite
      (DeckOrbitSkeleton (DeletionCategory (k := k) C S) N') :=
    finite_deletionOrbitQuotient (k := k) C S hSN
  let hPdel := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hIdel := fun X ↦
    deletion_dualLinearYoneda_isFiniteDimensional (k := k) C hI S X
  let hlocalDel := fun X ↦
    deletion_end_isLocalRing (k := k) C hC hlocal S X
  let hrepDel := isLocallyRepresentationFinite_deletion (k := k) C S hrep
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP Slast X
  let hPStageDown := SD.orbitSkeletonLinearCoyonedaFinite (k := k) hPstage
  let hPDirectDown := DN.orbitSkeletonLinearCoyonedaFinite (k := k) hPdel
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton
          (StageCategory (k := k) N' R.representative x j) N') k) :=
    enoughProjectives_of_finiteRepresentables hPStageDown
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton (DeletionCategory (k := k) C S) N') k) :=
    enoughProjectives_of_finiteRepresentables hPDirectDown
  let Stage := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x j
  let hfreeN := DN.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hPdel hlocalDel
  let Direct := DN.finiteOrbitModuleIndecomposableSkeleton_of_hasShift_eq
    (k := k) (deletionHasShift (k := k) S hShiftN)
      (fun a ↦ deletionShift_additive (k := k) S hShiftN a)
      (fun a ↦ deletionShift_linear (k := k) S hShiftN a)
      hDNHas.symm hPdel hIdel hlocalDel hfreeN hrepDel
  let eBase := stageLastDeckOrbitEquivalence (k := k) D hC N R x
  letI : eBase.functor.Additive := inferInstance
  letI : eBase.functor.Linear k := inferInstance
  let E := finiteDimensionalModuleCongrEquivalenceOfFinite (k := k) eBase
  letI : E.functor.Additive :=
    finiteDimensionalModuleCongrEquivalenceOfFinite_functor_additive
      (k := k) eBase
  have hstage :
      stageFiniteOrbitSurplus
          (k := k) C D hC hP hI hlocal hrep N R x j =
        DN.finiteOrbitSurplus_of_hasShift_eq
          (k := k) (deletionHasShift (k := k) S hShiftN)
            (fun a ↦ deletionShift_additive (k := k) S hShiftN a)
            (fun a ↦ deletionShift_linear (k := k) S hShiftN a)
            hDNHas.symm hPdel hIdel hlocalDel hfreeN hrepDel := by
    calc
      stageFiniteOrbitSurplus
          (k := k) C D hC hP hI hlocal hrep N R x j =
        @MagnitudeConjecture.ARCount.surplus (Fin Direct.n) inferInstance
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            Direct.toFiniteRightTauCategoryData)
          Direct.toFiniteRightTauCategoryData.IsProjective
          (Classical.decPred _) :=
        Direct.surplus_eq_of_equivalence E Stage
      _ = DN.finiteOrbitSurplus_of_hasShift_eq
          (k := k) (deletionHasShift (k := k) S hShiftN)
            (fun a ↦ deletionShift_additive (k := k) S hShiftN a)
            (fun a ↦ deletionShift_linear (k := k) S hShiftN a)
            hDNHas.symm hPdel hIdel hlocalDel hfreeN hrepDel :=
        (DN.finiteOrbitSurplus_of_hasShift_eq_eq_skeleton
          (k := k) (deletionHasShift (k := k) S hShiftN)
            (fun a ↦ deletionShift_additive (k := k) S hShiftN a)
            (fun a ↦ deletionShift_linear (k := k) S hShiftN a)
            hDNHas.symm hPdel hIdel hlocalDel hfreeN hrepDel
            (by infer_instance)).symm
  letI := deletionMulAction (k := k) S hSG
  haveI : IsCancelSMul G (DeletionCategory (k := k) C S) :=
    deletionIsCancelSMul (k := k) S hSG
  let DG := CoherentDeckShift.deletionCoherentDeckShift (k := k) D S hSG
  letI : ∀ a : Additive G, (DG.core.F a).Additive :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_additive
      (k := k) D S hSG a
  letI : ∀ a : Additive G, (DG.core.F a).Linear k :=
    fun a ↦ CoherentDeckShift.deletionCoherentDeckShift_core_linear
      (k := k) D S hSG a
  letI : Finite
      (MulAction.orbitRel.Quotient G (DeletionCategory (k := k) C S)) :=
    finite_deletionOrbitQuotient (k := k) C S hSG
  let hfreeG := DG.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hPdel hlocalDel
  let hfreeNG := hfreeG.restrict N'
  have hcore : (DG.restrict N').core = DN.core :=
    CoherentDeckShift.deletionCoherentDeckShift_restrict_core_eq
      (k := k) D N' S hSG hSN
  have hnormalize :
      (DG.restrict N').finiteOrbitSurplus
          (k := k) hPdel hIdel hlocalDel hfreeNG hrepDel =
        DN.finiteOrbitSurplus
          (k := k) hPdel hIdel hlocalDel hfreeNG hrepDel :=
    (DG.restrict N').finiteOrbitSurplus_eq_of_core_eq
      (k := k) DN hcore hPdel hIdel hlocalDel hfreeNG hrepDel
  have hscale := DG.finiteOrbitSurplus_restrict_eq_card_mul
    (k := k) hPdel hIdel hlocalDel hfreeG hrepDel N
  have hdirectCanonical :
      DN.finiteOrbitSurplus_of_hasShift_eq
          (k := k) (deletionHasShift (k := k) S hShiftN)
            (fun a ↦ deletionShift_additive (k := k) S hShiftN a)
            (fun a ↦ deletionShift_linear (k := k) S hShiftN a)
            hDNHas.symm hPdel hIdel hlocalDel hfreeN hrepDel =
        DN.finiteOrbitSurplus
          (k := k) hPdel hIdel hlocalDel hfreeNG hrepDel := by
    calc
      _ = DN.finiteOrbitSurplus
          (k := k) hPdel hIdel hlocalDel hfreeN hrepDel :=
        DN.finiteOrbitSurplus_of_hasShift_eq_eq
          (k := k) (deletionHasShift (k := k) S hShiftN)
            (fun a ↦ deletionShift_additive (k := k) S hShiftN a)
            (fun a ↦ deletionShift_linear (k := k) S hShiftN a)
            hDNHas.symm hPdel hIdel hlocalDel hfreeN hrepDel
      _ = _ := by congr
  rw [hstage]
  rw [hdirectCanonical]
  rw [← hnormalize]
  exact hscale

/-- The manuscript's finite-covering average: the downstairs surplus drop
caused by deleting one complete deck orbit is the average of the literal
adjacent local changes over the residual quotient representatives. -/
theorem finiteOrbitSurplus_sub_fullOrbitDeletion_eq_quotientAverage
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
    (x : C)
    (havoid : ∀ i : Fin R.m, ∀ g ∈
      finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G)) :
    letI : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
    let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hP hlocal
    ((D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep -
        fullOrbitDeletionFiniteOrbitSurplus
          (k := k) D hC hP hI hlocal hrep x : ℤ) : ℚ) =
      (1 / (Fintype.card (G ⧸ (N : Subgroup G)) : ℚ)) *
        ∑ i, (stageLocalChange (k := k) hrep R x i : ℚ) := by
  letI : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  exact R.downstairs_difference_eq_quotientAverage
    (D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep)
    (fullOrbitDeletionFiniteOrbitSurplus
      (k := k) D hC hP hI hlocal hrep x)
    (fun j ↦ stageFiniteOrbitSurplus
      (k := k) C D hC hP hI hlocal hrep N R x j)
    (fun i ↦ stageLocalChange (k := k) hrep R x i)
    (fun i ↦ stageLocalChange_eq_stageFiniteOrbitSurplus_sub
      (k := k) (C := C) D hC hP hI hlocal hrep N R x i (havoid i))
    (stageFiniteOrbitSurplus_zero_eq_card_mul
      (k := k) (C := C) D hC hP hI hlocal hrep N R x)
    (stageFiniteOrbitSurplus_last_eq_card_mul
      (k := k) (C := C) D hC hP hI hlocal hrep N R x)

/-- Nonnegativity of every literal stage deletion gives the monotonicity
conclusion of the manuscript's finite-covering average. -/
theorem fullOrbitDeletionFiniteOrbitSurplus_le_finiteOrbitSurplus
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
    (x : C)
    (havoid : ∀ i : Fin R.m, ∀ g ∈
      finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (hchange : ∀ i : Fin R.m,
      0 ≤ stageLocalChange (k := k) hrep R x i) :
    fullOrbitDeletionFiniteOrbitSurplus
        (k := k) D hC hP hI hlocal hrep x ≤
      D.finiteOrbitSurplus (k := k) hP hI hlocal
        (D.isFreeOnIsomorphismClasses_of_finiteRepresentables
          (k := k) hP hlocal) hrep := by
  letI : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  have hdiff := R.downstairs_difference_nonnegative
    (D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep)
    (fullOrbitDeletionFiniteOrbitSurplus
      (k := k) D hC hP hI hlocal hrep x)
    (fun j ↦ stageFiniteOrbitSurplus
      (k := k) C D hC hP hI hlocal hrep N R x j)
    (fun i ↦ stageLocalChange (k := k) hrep R x i)
    (fun i ↦ stageLocalChange_eq_stageFiniteOrbitSurplus_sub
      (k := k) (C := C) D hC hP hI hlocal hrep N R x i (havoid i))
    (stageFiniteOrbitSurplus_zero_eq_card_mul
      (k := k) (C := C) D hC hP hI hlocal hrep N R x)
    (stageFiniteOrbitSurplus_last_eq_card_mul
      (k := k) (C := C) D hC hP hI hlocal hrep N R x)
    hchange
  omega

/-- Source-facing finite-cover monotonicity: admissibility supplies the
nonnegativity of every stage-local deletion, so no separate local-change
hypothesis remains. -/
theorem fullOrbitDeletionFiniteOrbitSurplus_le_finiteOrbitSurplus_of_admissible
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (H : IsAdmissible (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C)
    (havoid : ∀ i : Fin R.m, ∀ g ∈
      finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily
          H.locallyRepresentationFinite (R.representative i • x)),
      g ∉ (N : Subgroup G)) :
    fullOrbitDeletionFiniteOrbitSurplus
        (k := k) D H.locallyBounded.skeletal
          H.locallyBounded.finiteCovariantRepresentables
          H.locallyBounded.finiteDualCorepresentables
          H.locallyBounded.localEndomorphismRings
          H.locallyRepresentationFinite x ≤
      D.finiteOrbitSurplus
        (k := k) H.locallyBounded.finiteCovariantRepresentables
          H.locallyBounded.finiteDualCorepresentables
          H.locallyBounded.localEndomorphismRings
          (D.isFreeOnIsomorphismClasses_of_finiteRepresentables
            (k := k) H.locallyBounded.finiteCovariantRepresentables
              H.locallyBounded.localEndomorphismRings)
          H.locallyRepresentationFinite := by
  apply fullOrbitDeletionFiniteOrbitSurplus_le_finiteOrbitSurplus
    (k := k) D H.locallyBounded.skeletal
      H.locallyBounded.finiteCovariantRepresentables
      H.locallyBounded.finiteDualCorepresentables
      H.locallyBounded.localEndomorphismRings
      H.locallyRepresentationFinite N R x havoid
  exact fun i ↦ stageLocalChange_nonneg (k := k) H R x i

/-- If the two downstairs endpoints have equal surplus, nonnegativity makes
every deletion in the separated finite-cover chain an equality step. -/
theorem stageLocalChange_eq_zero_of_finiteOrbitSurplus_eq_fullOrbitDeletion
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
    (x : C)
    (havoid : ∀ i : Fin R.m, ∀ g ∈
      finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily hrep (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (hchange : ∀ i : Fin R.m,
      0 ≤ stageLocalChange (k := k) hrep R x i)
    (hEquality :
      D.finiteOrbitSurplus (k := k) hP hI hlocal
          (D.isFreeOnIsomorphismClasses_of_finiteRepresentables
            (k := k) hP hlocal) hrep =
        fullOrbitDeletionFiniteOrbitSurplus
          (k := k) D hC hP hI hlocal hrep x) :
    ∀ i : Fin R.m, stageLocalChange (k := k) hrep R x i = 0 := by
  letI : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
  let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
    (k := k) hP hlocal
  apply R.localChange_eq_zero_of_downstairs_eq
    (D.finiteOrbitSurplus (k := k) hP hI hlocal hfree hrep)
    (fullOrbitDeletionFiniteOrbitSurplus
      (k := k) D hC hP hI hlocal hrep x)
    (fun j ↦ stageFiniteOrbitSurplus
      (k := k) C D hC hP hI hlocal hrep N R x j)
    (fun i ↦ stageLocalChange (k := k) hrep R x i)
    (fun i ↦ stageLocalChange_eq_stageFiniteOrbitSurplus_sub
      (k := k) (C := C) D hC hP hI hlocal hrep N R x i (havoid i))
    (stageFiniteOrbitSurplus_zero_eq_card_mul
      (k := k) (C := C) D hC hP hI hlocal hrep N R x)
    (stageFiniteOrbitSurplus_last_eq_card_mul
      (k := k) (C := C) D hC hP hI hlocal hrep N R x)
    hchange
  simpa only [hfree] using hEquality

/-- Source-facing equality propagation for the finite covering average:
admissibility supplies stagewise nonnegativity, so equality of the two
downstairs endpoints forces every stage-local change to vanish. -/
theorem stageLocalChange_eq_zero_of_finiteOrbitSurplus_eq_fullOrbitDeletion_of_admissible
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (H : IsAdmissible (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C)
    (havoid : ∀ i : Fin R.m, ∀ g ∈
      finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily
          H.locallyRepresentationFinite (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (hEquality :
      D.finiteOrbitSurplus
          (k := k) H.locallyBounded.finiteCovariantRepresentables
          H.locallyBounded.finiteDualCorepresentables
          H.locallyBounded.localEndomorphismRings
          (D.isFreeOnIsomorphismClasses_of_finiteRepresentables
            (k := k) H.locallyBounded.finiteCovariantRepresentables
              H.locallyBounded.localEndomorphismRings)
          H.locallyRepresentationFinite =
        fullOrbitDeletionFiniteOrbitSurplus
          (k := k) D H.locallyBounded.skeletal
            H.locallyBounded.finiteCovariantRepresentables
            H.locallyBounded.finiteDualCorepresentables
            H.locallyBounded.localEndomorphismRings
            H.locallyRepresentationFinite x) :
    ∀ i : Fin R.m,
      stageLocalChange
        (k := k) H.locallyRepresentationFinite R x i = 0 := by
  apply stageLocalChange_eq_zero_of_finiteOrbitSurplus_eq_fullOrbitDeletion
    (k := k) D H.locallyBounded.skeletal
      H.locallyBounded.finiteCovariantRepresentables
      H.locallyBounded.finiteDualCorepresentables
      H.locallyBounded.localEndomorphismRings
      H.locallyRepresentationFinite N R x havoid
      (fun i ↦ stageLocalChange_nonneg (k := k) H R x i)
  exact hEquality

/-- The equality clause of the finite covering average.  Equality of its
two downstairs endpoint surpluses makes the first local deletion vanish; as
the first representative is the identity and the initial stage is undeleted,
every ambient indecomposable nonzero at `x` has one-dimensional fibre there. -/
theorem finrank_obj_eq_one_of_finiteOrbitSurplus_eq_fullOrbitDeletion_of_admissible
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (H : IsAdmissible (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G)
    (R : FiniteQuotientRepresentatives (N : Subgroup G))
    (x : C)
    (havoid : ∀ i : Fin R.m, ∀ g ∈
      finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily
          H.locallyRepresentationFinite (R.representative i • x)),
      g ∉ (N : Subgroup G))
    (hEquality :
      D.finiteOrbitSurplus
          (k := k) H.locallyBounded.finiteCovariantRepresentables
          H.locallyBounded.finiteDualCorepresentables
          H.locallyBounded.localEndomorphismRings
          (D.isFreeOnIsomorphismClasses_of_finiteRepresentables
            (k := k) H.locallyBounded.finiteCovariantRepresentables
              H.locallyBounded.localEndomorphismRings)
          H.locallyRepresentationFinite =
        fullOrbitDeletionFiniteOrbitSurplus
          (k := k) D H.locallyBounded.skeletal
            H.locallyBounded.finiteCovariantRepresentables
            H.locallyBounded.finiteDualCorepresentables
            H.locallyBounded.localEndomorphismRings
            H.locallyRepresentationFinite x)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hMx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 := by
  have hzero :=
    stageLocalChange_eq_zero_of_finiteOrbitSurplus_eq_fullOrbitDeletion_of_admissible
      (k := k) D H N R x havoid hEquality R.firstIndex
  exact firstStageLocalChange_rigidity (k := k) H R x hzero M hM hMx

/-- The manuscript's source-facing finite covering average.  Residual
finiteness selects one normal finite-index subgroup which separates every
translated three-step control window; its canonical quotient representatives
then give the exact average formula, with every local summand nonnegative. -/
theorem exists_finiteCoveringAverage_of_admissible
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    [Group.ResiduallyFinite G]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (H : IsAdmissible (k := k) (C := C))
    (x : C) :
    ∃ (N : FiniteIndexNormalSubgroup G)
      (R : FiniteQuotientRepresentatives (N : Subgroup G)),
      (letI : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
       let hfree := D.isFreeOnIsomorphismClasses_of_finiteRepresentables
         (k := k) H.locallyBounded.finiteCovariantRepresentables
           H.locallyBounded.localEndomorphismRings
       ((D.finiteOrbitSurplus
             (k := k) H.locallyBounded.finiteCovariantRepresentables
               H.locallyBounded.finiteDualCorepresentables
               H.locallyBounded.localEndomorphismRings hfree
               H.locallyRepresentationFinite -
           fullOrbitDeletionFiniteOrbitSurplus
             (k := k) D H.locallyBounded.skeletal
               H.locallyBounded.finiteCovariantRepresentables
               H.locallyBounded.finiteDualCorepresentables
               H.locallyBounded.localEndomorphismRings
               H.locallyRepresentationFinite x : ℤ) : ℚ) =
         (1 / (Fintype.card (G ⧸ (N : Subgroup G)) : ℚ)) *
           ∑ i, (stageLocalChange
             (k := k) H.locallyRepresentationFinite R x i : ℚ)) ∧
        ∀ i : Fin R.m,
          0 ≤ stageLocalChange
            (k := k) H.locallyRepresentationFinite R x i := by
  obtain ⟨N, hN⟩ :=
    D.exists_finiteIndexNormalSubgroup_avoiding_orbit_threeStepControlFamilies
      (k := k) H.locallyRepresentationFinite x
  let R := finiteIndexQuotientRepresentatives N
  have hAvoid : ∀ i : Fin R.m, ∀ g ∈
      finiteModuleFamilySupportBadDegrees (G := G)
        (finiteThreeStepControlFamily
          H.locallyRepresentationFinite (R.representative i • x)),
      g ∉ (N : Subgroup G) := by
    intro i g hg
    exact hN (R.representative i) g hg
  refine ⟨N, R, ?_, ?_⟩
  · exact finiteOrbitSurplus_sub_fullOrbitDeletion_eq_quotientAverage
      (k := k) D H.locallyBounded.skeletal
        H.locallyBounded.finiteCovariantRepresentables
        H.locallyBounded.finiteDualCorepresentables
        H.locallyBounded.localEndomorphismRings
        H.locallyRepresentationFinite N R x hAvoid
  · exact fun i ↦ stageLocalChange_nonneg (k := k) H R x i

/-- Residual-finite source-facing covering monotonicity, with the finite
subgroup, representatives, and separation certificate all constructed
internally. -/
theorem fullOrbitDeletionFiniteOrbitSurplus_le_finiteOrbitSurplus_of_residuallyFinite_admissible
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    [Group.ResiduallyFinite G]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (H : IsAdmissible (k := k) (C := C))
    (x : C) :
    fullOrbitDeletionFiniteOrbitSurplus
        (k := k) D H.locallyBounded.skeletal
          H.locallyBounded.finiteCovariantRepresentables
          H.locallyBounded.finiteDualCorepresentables
          H.locallyBounded.localEndomorphismRings
          H.locallyRepresentationFinite x ≤
      D.finiteOrbitSurplus
        (k := k) H.locallyBounded.finiteCovariantRepresentables
          H.locallyBounded.finiteDualCorepresentables
          H.locallyBounded.localEndomorphismRings
          (D.isFreeOnIsomorphismClasses_of_finiteRepresentables
            (k := k) H.locallyBounded.finiteCovariantRepresentables
              H.locallyBounded.localEndomorphismRings)
          H.locallyRepresentationFinite := by
  obtain ⟨N, hN⟩ :=
    D.exists_finiteIndexNormalSubgroup_avoiding_orbit_threeStepControlFamilies
      (k := k) H.locallyRepresentationFinite x
  let R := finiteIndexQuotientRepresentatives N
  apply fullOrbitDeletionFiniteOrbitSurplus_le_finiteOrbitSurplus_of_admissible
    (k := k) D H N R x
  intro i g hg
  exact hN (R.representative i) g hg

/-- Residual-finite source-facing equality rigidity.  Equality of the two
downstairs endpoint surpluses forces every ambient indecomposable nonzero at
the selected lift to have one-dimensional fibre there. -/
theorem finrank_obj_eq_one_of_finiteOrbitSurplus_eq_fullOrbitDeletion_of_residuallyFinite_admissible
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    [Group.ResiduallyFinite G]
    (D : CoherentDeckShift C G)
    [∀ a : Additive G, (D.core.F a).Additive]
    [∀ a : Additive G, (D.core.F a).Linear k]
    (H : IsAdmissible (k := k) (C := C))
    (x : C)
    (hEquality :
      D.finiteOrbitSurplus
          (k := k) H.locallyBounded.finiteCovariantRepresentables
          H.locallyBounded.finiteDualCorepresentables
          H.locallyBounded.localEndomorphismRings
          (D.isFreeOnIsomorphismClasses_of_finiteRepresentables
            (k := k) H.locallyBounded.finiteCovariantRepresentables
              H.locallyBounded.localEndomorphismRings)
          H.locallyRepresentationFinite =
        fullOrbitDeletionFiniteOrbitSurplus
          (k := k) D H.locallyBounded.skeletal
            H.locallyBounded.finiteCovariantRepresentables
            H.locallyBounded.finiteDualCorepresentables
            H.locallyBounded.localEndomorphismRings
            H.locallyRepresentationFinite x)
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (hM : Indecomposable M)
    (hMx : ¬ IsZero (M.obj.obj.obj x)) :
    Module.finrank k (M.obj.obj.obj x) = 1 := by
  obtain ⟨N, hN⟩ :=
    D.exists_finiteIndexNormalSubgroup_avoiding_orbit_threeStepControlFamilies
      (k := k) H.locallyRepresentationFinite x
  let R := finiteIndexQuotientRepresentatives N
  apply finrank_obj_eq_one_of_finiteOrbitSurplus_eq_fullOrbitDeletion_of_admissible
    (k := k) D H N R x _ hEquality M hM hMx
  intro i g hg
  exact hN (R.representative i) g hg

end MagnitudeConjecture.ObjectDeletion
