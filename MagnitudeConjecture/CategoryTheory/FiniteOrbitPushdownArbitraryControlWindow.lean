import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownDerivedControlWindow
import MagnitudeConjecture.CategoryTheory.FiniteOrbitDownstreamPresentation
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownMultiplicity
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownProjective
import MagnitudeConjecture.CategoryTheory.FiniteOrbitDownstreamRightTau
import MagnitudeConjecture.CategoryTheory.FiniteTauOccurrences
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableBaseFreeness

/-!
# Finite push-down on an arbitrary certified control window

The covering-average proof uses a finite control family chosen uniformly over
the deletion stages, not necessarily an iterated neighborhood of one seed.
This file assembles the existing arbitrary-core push-down theorems into the
exact common interface: factorization closure around a prescribed endpoint
core and shifted-Hom orthogonality on the additive control window preserve
irreducibility, left and right almost-split maps, projectivity, and incoming
local density.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The five push-down comparisons controlled by a finite additive window:
irreducibility, both almost-split directions, projectivity, and incoming local
density.  Naming this proposition lets literal deletion stages expose the
comparison without repeating its shift-instance boundary. -/
abbrev ArbitraryControlWindowComparison
    (Core : Set
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k))
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C)) : Prop :=
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
  (∀ {X Y : CoveringSeparation.WindowCategory W.additiveClosure}
      (f : X ⟶ Y),
    X.1 ∈ Core →
      (IsIrreducibleMorphism
          ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
            (k := k) W.additiveClosure).map f) ↔
        IsIrreducibleMorphism f)) ∧
  (∀ {X Y : CoveringSeparation.WindowCategory W.additiveClosure}
      (f : X ⟶ Y),
    IsRightAlmostSplit f → Y.1 ∈ Core →
      IsRightAlmostSplit
        ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
          (k := k) W.additiveClosure).map f)) ∧
  (∀ {X Y : CoveringSeparation.WindowCategory W.additiveClosure}
      (f : X ⟶ Y),
    IsLeftAlmostSplit f → X.1 ∈ Core →
      IsLeftAlmostSplit
        ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
          (k := k) W.additiveClosure).map f)) ∧
  (∀ X : CoveringSeparation.WindowCategory W.additiveClosure,
    (Projective
        ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
          (k := k) W.additiveClosure).obj X) ↔
      Projective X.1)) ∧
  (∀ {X Y : CoveringSeparation.WindowCategory W.additiveClosure}
      {f : X ⟶ Y},
    IsRightAlmostSplit f → IsRightMinimal f → Y.1 ∈ Core →
    ∃ d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition X,
      (∀ i, Indecomposable (d.summand i).1) ∧
      ∀ {Ind : Type w} [Fintype Ind]
        (T : QuotientSubmoduleEquidistribution.Iyama.FiniteRightTauCategoryData
          (FiniteDimensionalModuleCategory.{u, v, v, v}
            (C := DeckOrbitSkeleton C G) k) Ind)
        [DecidablePred T.IsProjective]
        (y : Ind)
        (_eY :
          ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
            (k := k) W.additiveClosure).obj Y) ≅ T.obj y),
        CoveringAction.occurrenceLocalDensity
            (MagnitudeConjecture.FiniteTauMatrix.rightArrowTarget T)
            T.IsProjective y =
          ARCount.localDensityOfIncomingArity d.n (Projective Y.1))

/-- A certified finite additive window controls all push-down data entering
the local density at endpoints in `Core`. -/
theorem finiteOrbitPushdown_arbitraryControlWindow
    [IsMulTorsionFree G]
    [Finite (MulAction.orbitRel.Quotient G C)]
    (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (linearCoyonedaLinearModule (k := k) X))
    (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
      (dualLinearYonedaLinearModule (k := k) X))
    (hlocal : ∀ X : C, IsLocalRing (End X))
    (hrep : IsLocallyRepresentationFinite (k := k) (C := C))
    (Core : Set
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k))
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hCoreWindow : CoveringSeparation.interactionNeighborhood
      (fun M N ↦ Indecomposable N ∧
        CoveringSeparation.homInteraction M N) Core ⊆
      W.additiveClosure)
    (horthogonal : D.FiniteModuleWindowShiftHomOrthogonal
      (k := k) W.additiveClosure) :
    D.ArbitraryControlWindowComparison Core W := by
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
  let hfree :=
    D.isFreeOnIsomorphismClasses_of_finiteRepresentables
      (k := k) hP hlocal
  let hDensity :=
    D.finiteOrbitPushdownDensity_of_locallyRepresentationFinite
      (k := k) hP hI hlocal hfree hrep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Y f hX
    exact D.isIrreducibleMorphism_finiteOrbitPushdownWindowMap_iff_of_density_finiteCore
      Core W.additiveClosure hCoreWindow hDensity horthogonal hX
  · intro X Y f hf hY
    exact D.rightAlmostSplit_finiteOrbitPushdownWindowMap_of_density_finiteCore
      Core W.additiveClosure hCoreWindow hDensity horthogonal hf hY
  · intro X Y f hf hX
    exact D.leftAlmostSplit_finiteOrbitPushdownWindowMap_of_density_finiteCore
      Core W.additiveClosure hCoreWindow hDensity horthogonal hf hX
  · intro X
    exact D.finiteDimensionalModuleOrbitSkeletonPushdown_projective_iff
      (k := k) hP hlocal X.1
  · intro X Y f hf hfmin hY
    let hPdown := D.orbitSkeletonLinearCoyonedaFinite (k := k) hP
    letI : EnoughProjectives
        (FiniteDimensionalModuleCategory.{u, v, v, v}
          (C := DeckOrbitSkeleton C G) k) :=
      enoughProjectives_of_finiteRepresentables hPdown
    obtain ⟨d, hSummandIndec⟩ :=
      W.exists_finiteIndecomposableDecomposition_additiveClosure X
    refine ⟨d, hSummandIndec, ?_⟩
    intro Ind _ T _ y eY
    have hfPush :
        IsRightAlmostSplit
          ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
            (k := k) W.additiveClosure).map f) :=
      D.rightAlmostSplit_finiteOrbitPushdownWindowMap_of_density_finiteCore
        Core W.additiveClosure hCoreWindow hDensity horthogonal hf hY
    have hArity :
        d.n = MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity T y :=
      D.finiteOrbitPushdownWindow_rightMiddleArity_eq
        (k := k) W.additiveClosure horthogonal d hSummandIndec
          hfPush hfmin T y eY
    have hIsoProjective :
        Projective (T.obj y) ↔
          Projective
            ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
              (k := k) W.additiveClosure).obj Y) := by
      constructor
      · intro h
        exact Projective.of_iso eY.symm h
      · intro h
        exact Projective.of_iso eY h
    have hPushProjective :
        Projective
            ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
              (k := k) W.additiveClosure).obj Y) ↔
          Projective Y.1 :=
      D.finiteDimensionalModuleOrbitSkeletonPushdown_projective_iff
        (k := k) hP hlocal Y.1
    rw [← MagnitudeConjecture.FiniteTauMatrix.localDensity_eq_occurrenceLocalDensity
      T y]
    exact
      MagnitudeConjecture.FiniteTauMatrix.localDensity_eq_localDensityOfIncomingArity
        T y d.n hArity.symm (Projective Y.1)
          ((MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj
              T y).trans (hIsoProjective.trans hPushProjective))

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
