import MagnitudeConjecture.CategoryTheory.FiniteOrbitDownstreamSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteSkeletonIntrinsicLocalDensity
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteOrbit
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStages
import MagnitudeConjecture.CategoryTheory.ObjectDeletionFiniteStructure
import MagnitudeConjecture.CategoryTheory.ObjectDeletionStagePushdown

/-!
# Finite indecomposable skeletons at the downstairs deletion stages

Every literal upstairs deletion stage retains the structural and local
representation-finiteness hypotheses needed by Gabriel push-down.  Its
subgroup deck-orbit category therefore has a complete finite indecomposable
module skeleton.  The associated Auslander--Reiten surplus is the literal
quantity `sigma(Cbar_j)` used in the covering telescope.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.ObjectDeletion

open MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]

/-- A complete finite indecomposable module skeleton on the actual subgroup
deck-orbit category of deletion stage `j`. -/
noncomputable def stageFiniteOrbitModuleIndecomposableSkeleton
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
    (x : C) (j : Fin (R.m + 1)) :
    letI := stageMulAction (k := k) (N : Subgroup G) R.representative x j
    let Dstage := stageCoherentDeckShift (k := k)
      D hC (N : Subgroup G) R.representative x j
    letI := Dstage.hasShift
    letI := Dstage.additiveShift
    letI := Dstage.linearShift (k := k)
    FiniteDimensionalModuleIndecomposableSkeleton
      (k := k)
      (C := DeckOrbitSkeleton
        (StageCategory (k := k) (N : Subgroup G) R.representative x j)
        (N : Subgroup G)) := by
  let S := stageDeletedSet (N : Subgroup G) R.representative x j
  letI := stageMulAction (k := k) (N : Subgroup G) R.representative x j
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G) R.representative x j) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x j
  letI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G) C) :=
    CoveringAction.finite_subgroupOrbitQuotient_of_finiteIndex N
  letI : Finite
      (MulAction.orbitRel.Quotient (N : Subgroup G)
        (StageCategory (k := k) (N : Subgroup G) R.representative x j)) :=
    finite_deletionOrbitQuotient (k := k) C S
      (stageDeletedSet_actionInvariant
        (N : Subgroup G) R.representative x j)
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x j
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC (N : Subgroup G) R.representative x j a
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC (N : Subgroup G) R.representative x j a
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hIstage := fun X ↦
    deletion_dualLinearYoneda_isFiniteDimensional (k := k) C hI S X
  let hlocalStage := fun X ↦
    deletion_end_isLocalRing (k := k) C hC hlocal S X
  let hrepStage := isLocallyRepresentationFinite_deletion
    (k := k) C S hrep
  let hfreeStage :=
    Dstage.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hPstage hlocalStage
  exact Dstage.finiteOrbitModuleIndecomposableSkeleton
    (k := k) hPstage hIstage hlocalStage hfreeStage hrepStage

/-- The literal Auslander--Reiten surplus of the finite subgroup-orbit
module category at deletion stage `j`. -/
noncomputable def stageFiniteOrbitSurplus
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
    (x : C) (j : Fin (R.m + 1)) : ℤ := by
  letI := stageMulAction (k := k) (N : Subgroup G) R.representative x j
  let S := stageDeletedSet (N : Subgroup G) R.representative x j
  haveI : IsCancelSMul (N : Subgroup G)
      (StageCategory (k := k) (N : Subgroup G) R.representative x j) :=
    stageIsCancelSMul (k := k)
      (N : Subgroup G) R.representative x j
  let Dstage := stageCoherentDeckShift (k := k)
    D hC (N : Subgroup G) R.representative x j
  letI := Dstage.hasShift
  letI := Dstage.additiveShift
  letI := Dstage.linearShift (k := k)
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Additive :=
    fun a ↦ stageCoherentDeckShift_core_additive
      (k := k) D hC (N : Subgroup G) R.representative x j a
  letI : ∀ a : Additive (N : Subgroup G),
      (Dstage.core.F a).Linear k :=
    fun a ↦ stageCoherentDeckShift_core_linear
      (k := k) D hC (N : Subgroup G) R.representative x j a
  let hPstage := fun X ↦
    deletion_linearCoyoneda_isFiniteDimensional (k := k) C hP S X
  let hPdown := Dstage.orbitSkeletonLinearCoyonedaFinite (k := k) hPstage
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton
          (StageCategory (k := k) (N : Subgroup G) R.representative x j)
          (N : Subgroup G)) k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  let T := stageFiniteOrbitModuleIndecomposableSkeleton
    (k := k) C D hC hP hI hlocal hrep N R x j
  exact @MagnitudeConjecture.ARCount.surplus (Fin T.n) inferInstance
    (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      T.toFiniteRightTauCategoryData)
    T.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _)

end MagnitudeConjecture.ObjectDeletion
