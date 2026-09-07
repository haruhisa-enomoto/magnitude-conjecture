import MagnitudeConjecture.CategoryTheory.AlmostSplitMultiplicity
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownWindow
import MagnitudeConjecture.CategoryTheory.FiniteTauAlmostSplitMultiplicity

/-!
# Incoming multiplicity under finite skeletal push-down

On a shift-orthogonal additive window, finite skeletal push-down is fully
faithful and preserves the indecomposability of every displayed summand.
Consequently the source of a pushed minimal right almost-split map has the
same number of indecomposable occurrences as any minimal right almost-split
source at the downstream endpoint.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type v} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- A shift-orthogonal finite push-down preserves the total number of
incoming indecomposable occurrences represented by a minimal right
almost-split source. -/
theorem finiteOrbitPushdownWindow_minimalRightAlmostSplitMultiplicity
    (W : Set
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k))
    [HasFiniteBiproducts (CoveringSeparation.WindowCategory W)]
    [HasBinaryBiproducts (CoveringSeparation.WindowCategory W)]
    (horthogonal : D.FiniteModuleWindowShiftHomOrthogonal (k := k) W)
    {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition X)
    (hSummandIndec : ∀ i, Indecomposable (d.summand i).1)
    (hf : letI := D.hasShift
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
          (k := k) W).map f))
    (hfmin : IsRightMinimal f) :
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
    ∀ {E : FiniteDimensionalModuleCategory.{u, v, v, v}
        (C := DeckOrbitSkeleton C G) k}
      {g : E ⟶
        ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
          (k := k) W).obj Y)}
      (d' : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition E),
      IsRightAlmostSplit g → IsRightMinimal g → d.n = d'.n := by
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
  intro E g d' hg hgmin
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W
  letI : P.Additive := by
    dsimp [P, finiteDimensionalModuleOrbitSkeletonPushdownWindow]
    infer_instance
  letI : P.Full := D.finiteDimensionalModuleOrbitSkeletonPushdownWindow_full
    (k := k) W horthogonal
  letI : P.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownWindow_faithful
      (k := k) W
  have hIndec (i : Fin d.n) : Indecomposable (P.obj (d.summand i)) :=
    D.finiteDimensionalModuleOrbitSkeletonPushdownWindow_obj_indecomposable
      (k := k) W horthogonal (d.summand i) (hSummandIndec i)
  have hlocal (i : Fin d.n) :
      IsLocalRing (End (P.obj (d.summand i))) :=
    finiteDimensionalModule_end_isLocalRing k
      (P.obj (d.summand i)) (hIndec i)
  exact d.n_eq_of_map_minimalRightAlmostSplit P hIndec hlocal d'
    hf (rightMinimal_map_of_full_faithful P hfmin) hg hgmin

/-- In a finite downstream tau-category, the preceding invariant is exactly
the chosen right-mesh arity, hence the total incoming-arrow multiplicity at
the identified endpoint. -/
theorem finiteOrbitPushdownWindow_rightMiddleArity_eq
    (W : Set
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k))
    [HasFiniteBiproducts (CoveringSeparation.WindowCategory W)]
    [HasBinaryBiproducts (CoveringSeparation.WindowCategory W)]
    (horthogonal : D.FiniteModuleWindowShiftHomOrthogonal (k := k) W)
    {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y}
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition X)
    (hSummandIndec : ∀ i, Indecomposable (d.summand i).1)
    (hf : letI := D.hasShift
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
          (k := k) W).map f))
    (hfmin : IsRightMinimal f) :
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
      (y : Ind)
      (_eY :
        ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
          (k := k) W).obj Y) ≅ T.obj y),
      d.n = MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity T y := by
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
  intro Ind _ T y eY
  let q :=
    (T.rightMesh (T.obj y)).g ≫
      (T.rightTermIso (T.obj y)).hom ≫ eY.inv
  have hq : IsRightAlmostSplit q :=
    IsRightAlmostSplit.postcomp_iso eY.symm
      (MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit
        T y)
  have hqmin : IsRightMinimal q :=
    IsRightMinimal.postcomp_iso eY.symm
      (MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightMinimal T y)
  have h :=
    D.finiteOrbitPushdownWindow_minimalRightAlmostSplitMultiplicity
      (k := k) W horthogonal d hSummandIndec hf hfmin
      (g := q)
      (MagnitudeConjecture.FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition
        T y) hq hqmin
  exact h

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
