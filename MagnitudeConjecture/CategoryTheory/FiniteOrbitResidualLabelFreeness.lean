import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownResidualFreeness
import MagnitudeConjecture.CategoryTheory.FiniteOrbitDownstreamSkeleton
import MagnitudeConjecture.CategoryTheory.FiniteSkeletonShiftAction
import MagnitudeConjecture.CategoryTheory.RepresentableDeckShift

/-!
# Freeness of the residual action on finite skeleton labels

For a finite-index normal subgroup, module-level residual freeness and Gabriel
density imply that the quotient group acts freely on the labels of the actual
complete duplicate-free indecomposable skeleton over the subgroup orbit.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [IsMulTorsionFree G]
variable [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

theorem finiteOrbitModuleIndecomposableSkeleton_residual_isShiftFreeOnLabels
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G) :
    let N' : Subgroup G := N
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N').hasShift
    letI := (D.restrict N').additiveShift
    letI := (D.restrict N').linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) (D.restrict N').core
    letI := linearModuleCategoryHasShift (k := k) (D.restrict N').core
    letI := linearModuleCategoryAdditiveShift (R := k) (D.restrict N').core
    letI := linearModuleCategoryLinearShift (R := k) (D.restrict N').core
    letI := (D.restrict N').isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := (D.restrict N').finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive N')) k) (Additive N')
    letI : MulAction (G ⧸ N') (DeckOrbitSkeleton C N') :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N'
    letI := D.deckOrbitResidualHasShift N'
    letI := D.deckOrbitResidualAdditiveShift N'
    letI := D.deckOrbitResidualLinearShift (k := k) N'
    let R := D.deckOrbitResidualCoherentDeckShift N'
    letI := R.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := R.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := R.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    letI : Fintype (G ⧸ N') := Fintype.ofFinite _
    let S := (D.restrict N').finiteOrbitModuleIndecomposableSkeleton
      (k := k) hP hI hlocal (hfree.restrict N') hrep
    S.IsShiftFreeOnLabels (G := G ⧸ N') := by
  let N' : Subgroup G := N
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N').hasShift
  letI := (D.restrict N').additiveShift
  letI := (D.restrict N').linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := isLinearModule_stableUnderShift (k := k) (D.restrict N').core
  letI := linearModuleCategoryHasShift (k := k) (D.restrict N').core
  letI := linearModuleCategoryAdditiveShift (R := k) (D.restrict N').core
  letI := linearModuleCategoryLinearShift (R := k) (D.restrict N').core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := (D.restrict N').isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := (D.restrict N').finiteDimensionalModuleCategoryHasShift (k := k)
  letI := (D.restrict N').finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive N')) k) (Additive N')
  letI : MulAction (G ⧸ N') (DeckOrbitSkeleton C N') :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N'
  letI := D.deckOrbitResidualHasShift N'
  letI := D.deckOrbitResidualAdditiveShift N'
  letI := D.deckOrbitResidualLinearShift (k := k) N'
  let R := D.deckOrbitResidualCoherentDeckShift N'
  letI := R.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := R.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := R.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI : Fintype (G ⧸ N') := Fintype.ofFinite _
  let hfreeN : IsFreeOnIsomorphismClasses (C := C) (G := N') := by
    intro n X hn
    apply Subtype.ext
    apply hfree (n : G) X
    simpa only [MulAction.subgroup_smul_def] using hn
  let P := (D.restrict N').finiteDimensionalModuleOrbitSkeletonPushdown
    (k := k)
  letI : P.Faithful :=
    (D.restrict N').finiteDimensionalModuleOrbitSkeletonPushdown_faithful
      (k := k)
  let S := (D.restrict N').finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal hfreeN hrep
  let hDensity :=
    (D.restrict N').finiteOrbitPushdownDensity_of_locallyRepresentationFinite
      (k := k) hP hI hlocal hfreeN hrep
  change S.IsShiftFreeOnLabels (G := G ⧸ N')
  intro q i hqi
  obtain ⟨M, ⟨eM⟩⟩ := hDensity.essSurj.mem_essImage (S.obj i)
  have hPM : Indecomposable (P.obj M) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso eM).2
      (S.indecomposable i)
  have hM : Indecomposable M :=
    MagnitudeConjecture.indecomposable_of_faithful_additive P M hPM
  let a : Additive (G ⧸ N') := Additive.ofMul q⁻¹
  obtain ⟨eqi⟩ := hqi
  let eShift := (shiftFunctor
    (FiniteDimensionalModuleCategory.{u, v, v, v}
      (C := DeckOrbitSkeleton C N') k) a).mapIso eM
  have ha : a = 0 :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_residual_trivialStabilizer
      (k := k) M hM N' a
        ⟨eM ≪≫ eqi.symm ≪≫ eShift.symm⟩
  exact inv_eq_one.mp (by
    simpa [a] using congrArg Additive.toMul ha)

/-- The total local density on the subgroup orbit is the covering degree
times its residual label-orbit sum. -/
theorem finiteOrbitModuleIndecomposableSkeleton_sum_eq_card_mul_residualOrbitSum
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (N : FiniteIndexNormalSubgroup G) :
    let N' : Subgroup G := N
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := (D.restrict N').hasShift
    letI := (D.restrict N').additiveShift
    letI := (D.restrict N').linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) (D.restrict N').core
    letI := linearModuleCategoryHasShift (k := k) (D.restrict N').core
    letI := linearModuleCategoryAdditiveShift (R := k) (D.restrict N').core
    letI := linearModuleCategoryLinearShift (R := k) (D.restrict N').core
    letI := (D.restrict N').isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := (D.restrict N').finiteDimensionalModuleCategoryHasShift (k := k)
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive N')) k) (Additive N')
    letI : MulAction (G ⧸ N') (DeckOrbitSkeleton C N') :=
      MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N'
    letI := D.deckOrbitResidualHasShift N'
    letI := D.deckOrbitResidualAdditiveShift N'
    letI := D.deckOrbitResidualLinearShift (k := k) N'
    let R := D.deckOrbitResidualCoherentDeckShift N'
    letI := R.isFiniteDimensionalModule_stableUnderShift (k := k)
    letI := R.finiteDimensionalModuleCategoryHasShift (k := k)
    letI := R.finiteDimensionalModuleCategoryAdditiveShift (k := k)
    letI : Fintype (G ⧸ N') := Fintype.ofFinite _
    let hPdown := (D.restrict N').orbitSkeletonLinearCoyonedaFinite
      (k := k) hP
    letI : EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C N') k) :=
      enoughProjectives_of_finiteRepresentables hPdown
    let S := (D.restrict N').finiteOrbitModuleIndecomposableSkeleton
      (k := k) hP hI hlocal (hfree.restrict N') hrep
    letI := S.labelMulAction (G := G ⧸ N')
    letI := S.labelOrbitFintype (G := G ⧸ N')
    (∑ i : Fin S.n, S.rightTauLocalDensity i) =
      (Fintype.card (G ⧸ N') : ℤ) *
        ∑ q : MulAction.orbitRel.Quotient (G ⧸ N') (Fin S.n),
          MagnitudeConjecture.CoveringAction.orbitInvariantDescend
            S.rightTauLocalDensity S.rightTauLocalDensity_smul q := by
  let N' : Subgroup G := N
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := (D.restrict N').hasShift
  letI := (D.restrict N').additiveShift
  letI := (D.restrict N').linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) (D.restrict N').core
  letI := linearModuleCategoryHasShift (k := k) (D.restrict N').core
  letI := linearModuleCategoryAdditiveShift (R := k) (D.restrict N').core
  letI := linearModuleCategoryLinearShift (R := k) (D.restrict N').core
  letI := (D.restrict N').isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := (D.restrict N').finiteDimensionalModuleCategoryHasShift (k := k)
  letI := trivialHasShift
    (LinearModuleCategory.{u, v, v, v}
      (C := ShiftOrbitCategory C (Additive N')) k) (Additive N')
  letI : MulAction (G ⧸ N') (DeckOrbitSkeleton C N') :=
    MagnitudeConjecture.CoveringAction.orbitQuotientMulAction N'
  letI := D.deckOrbitResidualHasShift N'
  letI := D.deckOrbitResidualAdditiveShift N'
  letI := D.deckOrbitResidualLinearShift (k := k) N'
  let R := D.deckOrbitResidualCoherentDeckShift N'
  letI := R.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := R.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := R.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  letI : Fintype (G ⧸ N') := Fintype.ofFinite _
  let hPdown := (D.restrict N').orbitSkeletonLinearCoyonedaFinite
    (k := k) hP
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C N') k) :=
    enoughProjectives_of_finiteRepresentables hPdown
  let S := (D.restrict N').finiteOrbitModuleIndecomposableSkeleton
    (k := k) hP hI hlocal (hfree.restrict N') hrep
  change (∑ i : Fin S.n, S.rightTauLocalDensity i) = _
  exact S.sum_occurrenceLocalDensity_eq_card_mul_orbitSum
    (D.finiteOrbitModuleIndecomposableSkeleton_residual_isShiftFreeOnLabels
      (k := k) hP hI hlocal hfree hrep N)

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
