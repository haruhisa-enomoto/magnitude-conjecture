import MagnitudeConjecture.CategoryTheory.FiniteOrbitARComponentExhaustion
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleControlWindow
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownAdditiveControlWindow

/-!
# Finite control windows with Gabriel density discharged

The finite-window irreducibility theorem is useful in the covering average
only after Gabriel density has been obtained from the manuscript's local
representation-finiteness hypotheses.  This file performs that substitution:
the public endpoint below has no separately supplied density premise.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- Under the manuscript's local representation-finiteness and finite-orbit
hypotheses, the additive hull of the third finite Hom-neighborhood identifies
irreducible morphisms before and after finite skeletal Gabriel push-down for
endpoints in the second neighborhood.  The conclusion retains neither
Gabriel density nor an arbitrary factorization-closure premise. -/
theorem
    isIrreducibleMorphism_finiteOrbitPushdownWindowMap_iff_of_locallyRepresentationFinite
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (horthogonal : D.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (Set.range (S.iterateHomNeighborhood hrep 3).obj))
    {X Y : CoveringSeparation.WindowCategory
      (S.iterateHomNeighborhood hrep 3).additiveClosure} {f : X ⟶ Y}
    (hX : X.1 ∈ (S.iterateHomNeighborhood hrep 2).isoClosure) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    (IsIrreducibleMorphism
        ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
          (k := k)
            (S.iterateHomNeighborhood hrep 3).additiveClosure).map f) ↔
      IsIrreducibleMorphism f) := by
  let hDensity :=
    D.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
      (k := k) hP hI hlocal hfree hrep
  have horthogonalIso : D.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (S.iterateHomNeighborhood hrep 3).isoClosure :=
    D.finiteModuleWindowShiftHomOrthogonal_isoClosure
      (S.iterateHomNeighborhood hrep 3) horthogonal
  have horthogonalAdditive : D.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (S.iterateHomNeighborhood hrep 3).additiveClosure :=
    D.finiteModuleWindowShiftHomOrthogonal_additiveClosure
      (S.iterateHomNeighborhood hrep 3) horthogonalIso
  have hstep : CoveringSeparation.interactionNeighborhood
        indecomposableHomInteraction
        (S.iterateHomNeighborhood hrep 2).isoClosure ⊆
      (S.iterateHomNeighborhood hrep 3).isoClosure := by
    simpa using S.interactionNeighborhood_iterateHomNeighborhood_subset
      hrep 2
  have hUW : CoveringSeparation.interactionNeighborhood
        (fun M N ↦ Indecomposable N ∧
          CoveringSeparation.homInteraction M N)
        (S.iterateHomNeighborhood hrep 2).isoClosure ⊆
      (S.iterateHomNeighborhood hrep 3).additiveClosure := by
    intro M hM
    exact (S.iterateHomNeighborhood hrep 3).isoClosure_subset_additiveClosure
      (hstep hM)
  exact
    D.isIrreducibleMorphism_finiteOrbitPushdownWindowMap_iff_of_density_finiteCore
      (S.iterateHomNeighborhood hrep 2).isoClosure
      (S.iterateHomNeighborhood hrep 3).additiveClosure
      hUW hDensity horthogonalAdditive hX

/-- Under the manuscript hypotheses, the third certified Hom-neighborhood
transports right almost-split maps ending in the second neighborhood. -/
theorem
    rightAlmostSplit_finiteOrbitPushdownWindowMap_of_locallyRepresentationFinite
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (horthogonal : D.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (Set.range (S.iterateHomNeighborhood hrep 3).obj))
    {X Y : CoveringSeparation.WindowCategory
      (S.iterateHomNeighborhood hrep 3).additiveClosure} {f : X ⟶ Y}
    (hf : IsRightAlmostSplit f)
    (hY : Y.1 ∈ (S.iterateHomNeighborhood hrep 2).isoClosure) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    IsRightAlmostSplit
      ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
        (k := k)
          (S.iterateHomNeighborhood hrep 3).additiveClosure).map f) := by
  let hDensity :=
    D.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
      (k := k) hP hI hlocal hfree hrep
  have horthogonalIso : D.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (S.iterateHomNeighborhood hrep 3).isoClosure :=
    D.finiteModuleWindowShiftHomOrthogonal_isoClosure
      (S.iterateHomNeighborhood hrep 3) horthogonal
  have horthogonalAdditive : D.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (S.iterateHomNeighborhood hrep 3).additiveClosure :=
    D.finiteModuleWindowShiftHomOrthogonal_additiveClosure
      (S.iterateHomNeighborhood hrep 3) horthogonalIso
  have hstep : CoveringSeparation.interactionNeighborhood
        indecomposableHomInteraction
        (S.iterateHomNeighborhood hrep 2).isoClosure ⊆
      (S.iterateHomNeighborhood hrep 3).isoClosure := by
    simpa using S.interactionNeighborhood_iterateHomNeighborhood_subset
      hrep 2
  have hUW : CoveringSeparation.interactionNeighborhood
        (fun M N ↦ Indecomposable N ∧
          CoveringSeparation.homInteraction M N)
        (S.iterateHomNeighborhood hrep 2).isoClosure ⊆
      (S.iterateHomNeighborhood hrep 3).additiveClosure := by
    intro M hM
    exact (S.iterateHomNeighborhood hrep 3).isoClosure_subset_additiveClosure
      (hstep hM)
  exact
    D.rightAlmostSplit_finiteOrbitPushdownWindowMap_of_density_finiteCore
      (S.iterateHomNeighborhood hrep 2).isoClosure
      (S.iterateHomNeighborhood hrep 3).additiveClosure
      hUW hDensity horthogonalAdditive hf hY

/-- The dual certified-window statement transports left almost-split maps
starting in the second neighborhood. -/
theorem
    leftAlmostSplit_finiteOrbitPushdownWindowMap_of_locallyRepresentationFinite
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hfree : IsFreeOnIsomorphismClasses (C := C) (G := G))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (S : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (horthogonal : D.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (Set.range (S.iterateHomNeighborhood hrep 3).obj))
    {X Y : CoveringSeparation.WindowCategory
      (S.iterateHomNeighborhood hrep 3).additiveClosure} {f : X ⟶ Y}
    (hf : IsLeftAlmostSplit f)
    (hX : X.1 ∈ (S.iterateHomNeighborhood hrep 2).isoClosure) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, v, v, v}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    IsLeftAlmostSplit
      ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
        (k := k)
          (S.iterateHomNeighborhood hrep 3).additiveClosure).map f) := by
  let hDensity :=
    D.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
      (k := k) hP hI hlocal hfree hrep
  have horthogonalIso : D.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (S.iterateHomNeighborhood hrep 3).isoClosure :=
    D.finiteModuleWindowShiftHomOrthogonal_isoClosure
      (S.iterateHomNeighborhood hrep 3) horthogonal
  have horthogonalAdditive : D.FiniteModuleWindowShiftHomOrthogonal (k := k)
      (S.iterateHomNeighborhood hrep 3).additiveClosure :=
    D.finiteModuleWindowShiftHomOrthogonal_additiveClosure
      (S.iterateHomNeighborhood hrep 3) horthogonalIso
  have hstep : CoveringSeparation.interactionNeighborhood
        indecomposableHomInteraction
        (S.iterateHomNeighborhood hrep 2).isoClosure ⊆
      (S.iterateHomNeighborhood hrep 3).isoClosure := by
    simpa using S.interactionNeighborhood_iterateHomNeighborhood_subset
      hrep 2
  have hUW : CoveringSeparation.interactionNeighborhood
        (fun M N ↦ Indecomposable N ∧
          CoveringSeparation.homInteraction M N)
        (S.iterateHomNeighborhood hrep 2).isoClosure ⊆
      (S.iterateHomNeighborhood hrep 3).additiveClosure := by
    intro M hM
    exact (S.iterateHomNeighborhood hrep 3).isoClosure_subset_additiveClosure
      (hstep hM)
  exact
    D.leftAlmostSplit_finiteOrbitPushdownWindowMap_of_density_finiteCore
      (S.iterateHomNeighborhood hrep 2).isoClosure
      (S.iterateHomNeighborhood hrep 3).additiveClosure
      hUW hDensity horthogonalAdditive hf hX

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
