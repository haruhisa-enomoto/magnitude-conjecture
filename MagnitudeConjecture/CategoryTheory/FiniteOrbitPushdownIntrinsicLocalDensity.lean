import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownArbitraryControlWindow
import MagnitudeConjecture.CategoryTheory.LocallyFiniteModuleLocalDensity
import MagnitudeConjecture.CategoryTheory.ObjectDeletionControlWindow

/-!
# Intrinsic local density under arbitrary-window finite push-down

The arbitrary-window comparison already identifies the pushed local density
with the arity of a minimal sink inside the window.  This file removes that
chosen window decomposition from the conclusion: finite Krull--Schmidt
uniqueness identifies its arity with the intrinsic local density in the
ambient locally representation-finite module category.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
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

omit [IsAlgClosed k] in
/-- A certified arbitrary control window identifies the pushed local density
at every core endpoint with the intrinsic local density upstairs. -/
theorem finiteOrbitPushdown_arbitraryControlWindow_localDensity
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (Core : Set
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k))
    (W : FiniteIndecomposableModuleFamily (k := k) (C := C))
    (hCoreWindow : CoveringSeparation.interactionNeighborhood
      (fun M N ↦ Indecomposable N ∧
        CoveringSeparation.homInteraction M N) Core ⊆
      W.additiveClosure)
    (hcomparison : D.ArbitraryControlWindowComparison.{u, v, w} Core W)
    (Y : CoveringSeparation.WindowCategory W.additiveClosure)
    (hYind : Indecomposable Y.1) (hYCore : Y.1 ∈ Core) :
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
        finiteModuleLocalDensity hlocal Y.1 hYind := by
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
  letI : HasFiniteBiproducts
      (CoveringSeparation.WindowCategory W.additiveClosure) :=
    W.additiveClosure_hasFiniteBiproducts
  letI : HasBinaryBiproducts
      (CoveringSeparation.WindowCategory W.additiveClosure) :=
    W.additiveClosure_hasBinaryBiproducts
  let A := finiteModuleMinimalSinkData hlocal Y.1 hYind
  have hSummand (i : Fin A.decomposition.n) :
      A.decomposition.summand i ∈ W.additiveClosure := by
    apply hCoreWindow
    refine ⟨Y.1, hYCore, A.decomposition.indecomposable i, ?_⟩
    exact Or.inr (Or.inr ⟨⟨
      A.decomposition.inclusion i ≫ A.map, 0,
      A.decomposition.inclusion_comp_ne_zero_of_isRightMinimal
        i A.map A.rightMinimal⟩⟩)
  let P : ObjectProperty
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
    W.additiveClosure
  haveI : P.IsClosedUnderFiniteProducts :=
    W.additiveClosure_isClosedUnderFiniteProducts
  have hBiproduct : P (⨁ A.decomposition.summand) :=
    P.prop_of_isLimit_fan
      (biproduct.isLimit A.decomposition.summand) hSummand
  have hSource : A.source ∈ W.additiveClosure :=
    P.prop_of_iso A.decomposition.isoBiproduct.symm hBiproduct
  let X : CoveringSeparation.WindowCategory W.additiveClosure :=
    ⟨A.source, hSource⟩
  let f : X ⟶ Y := P.homMk A.map
  haveI : P.ι.Additive :=
    CategoryTheory.Functor.fullSubcategoryInclusion_additive P
  have hf : IsRightAlmostSplit f := by
    apply MagnitudeConjecture.rightAlmostSplit_of_map_full_faithful P.ι
    change IsRightAlmostSplit A.map
    exact A.rightAlmostSplit
  have hfmin : IsRightMinimal f := by
    apply MagnitudeConjecture.rightMinimal_of_map_full_faithful P.ι
    change IsRightMinimal A.map
    exact A.rightMinimal
  obtain ⟨d, hInd, hDensity⟩ :=
    hcomparison.2.2.2.2 hf hfmin hYCore
  let J : Functor
      (CoveringSeparation.WindowCategory W.additiveClosure)
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) := P.ι
  haveI : J.Additive := by
    dsimp only [J]
    exact CategoryTheory.Functor.fullSubcategoryInclusion_additive P
  have hIndJ (i : Fin d.n) : Indecomposable (J.obj (d.summand i)) := by
    dsimp only [J]
    exact hInd i
  let dMap := d.mapOfIndecomposable J hIndJ
  have hIndMap : ∀ i, Indecomposable (dMap.summand i) := by
    simpa only [dMap,
      MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.mapOfIndecomposable]
      using hIndJ
  have hArity : d.n = A.decomposition.n := by
    simpa only [dMap,
      MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.mapOfIndecomposable]
      using dMap.n_eq_of_iso A.decomposition
        (fun i ↦ finiteDimensionalModule_end_isLocalRing
          k (dMap.summand i) (hIndMap i)) (Iso.refl A.source)
  have hIntrinsic :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      hlocal Y.1 hYind A.decomposition A.rightAlmostSplit A.rightMinimal
  intro Ind _ T _ y eY
  calc
    CoveringAction.occurrenceLocalDensity
        (MagnitudeConjecture.FiniteTauMatrix.rightArrowTarget T)
        T.IsProjective y =
        MagnitudeConjecture.ARCount.localDensityOfIncomingArity d.n
          (Projective Y.1) := hDensity (Ind := Ind) T y eY
    _ = MagnitudeConjecture.ARCount.localDensityOfIncomingArity
        A.decomposition.n (Projective Y.1) := by rw [hArity]
    _ = finiteModuleLocalDensity hlocal Y.1 hYind := hIntrinsic.symm

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
