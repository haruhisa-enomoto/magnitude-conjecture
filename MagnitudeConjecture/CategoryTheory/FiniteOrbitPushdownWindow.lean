import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownHomEquiv
import MagnitudeConjecture.CategoryTheory.ShiftOrbitWindow

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom.CoherentDeckShift

universe u v w uK uM

variable {k : Type uK} [Field k]
variable {C : Type u} [Category.{v} C]
variable {G : Type w} [Group G] [MulAction G C] [IsCancelSMul G C]
variable [Preadditive C] [CategoryTheory.Linear k C]
variable (D : CoherentDeckShift C G)
variable [∀ a : Additive G, (D.core.F a).Additive]
variable [∀ a : Additive G, (D.core.F a).Linear k]

/-- The finite-dimensional skeletal push-down restricted to a full control
window of upstairs modules. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownWindow
    (W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringSeparation.WindowCategory W ⥤
      FiniteDimensionalModuleCategory.{u, max v w, uK, max w uM}
        (C := DeckOrbitSkeleton C G) k := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact windowInclusion W ⋙
    D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)

/-- The finite push-down's orbit Hom decomposition restricted to a full
control window. -/
noncomputable def finiteDimensionalModuleOrbitSkeletonPushdownWindowOrbitHomDecomposition
    (W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    FunctorOrbitHomDecomposition (k := k)
      (D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W)
      (fun M N g ↦ multiplicativeShiftHom
        (C := LinearModuleCategory.{u, v, uK, uM} (C := C) k)
        (A := Additive G) M.1.obj N.1.obj g) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  let E := D.finiteDimensionalModuleOrbitSkeletonPushdownOrbitHomDecomposition
    (k := k)
  exact
    { sourceEquiv := fun M N ↦
        (InducedCategory.homLinearEquiv (R := k)).trans
          (E.sourceEquiv M.1 N.1)
      homDecomposition := fun M N ↦ E.homDecomposition M.1 N.1
      map_compat := by
        intro M N f
        exact E.map_compat M.1 N.1 f.hom }

/-- Nonidentity shifted Homs vanish between every ordered pair of modules in
the control window. -/
def FiniteModuleWindowShiftHomOrthogonal
    (W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    Prop := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  exact ∀ (M N : CoveringSeparation.WindowCategory W) (a : Additive G),
    a ≠ 0 → Subsingleton (ShiftHom M.1.obj N.1.obj a)

omit [IsCancelSMul G C] in
theorem finiteModuleWindowTranslateHomOrthogonal_of_shiftHomOrthogonal
    (W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    D.FiniteModuleWindowShiftHomOrthogonal (k := k) W →
      TranslateHomOrthogonal
        (fun (M N : CoveringSeparation.WindowCategory W)
            (g : Multiplicative (Additive G)) ↦ multiplicativeShiftHom
          (C := LinearModuleCategory.{u, v, uK, uM} (C := C) k)
          (A := Additive G) M.1.obj N.1.obj g) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  intro orthogonal M N g hg
  apply orthogonal M N g.toAdd
  intro hzero
  apply hg
  exact Multiplicative.toAdd.injective (by simpa using hzero)

/-- A translate-orthogonal module window makes finite skeletal push-down full
on that window. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdownWindow_full
    (W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    D.FiniteModuleWindowShiftHomOrthogonal (k := k) W →
      (D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
        (k := k) W).Full := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro h
  exact
    (D.finiteDimensionalModuleOrbitSkeletonPushdownWindowOrbitHomDecomposition
      (k := k) W).fullOfOrthogonal
        (D.finiteModuleWindowTranslateHomOrthogonal_of_shiftHomOrthogonal
          (k := k) W h)

/-- Finite skeletal push-down is faithful on every full control window. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdownWindow_faithful
    (W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    (D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
      (k := k) W).Faithful := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  exact
    (D.finiteDimensionalModuleOrbitSkeletonPushdownWindowOrbitHomDecomposition
      (k := k) W).faithful

/-- Every indecomposable object in a translate-orthogonal window has
indecomposable finite skeletal push-down.  In particular, the finite-cover
separation used by the campaign preserves the selected indecomposable
vertices without invoking global density. -/
theorem finiteDimensionalModuleOrbitSkeletonPushdownWindow_obj_indecomposable
    (W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    D.FiniteModuleWindowShiftHomOrthogonal (k := k) W →
      ∀ (M : CoveringSeparation.WindowCategory W),
        Indecomposable M.1 →
        Indecomposable
          ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
            (k := k) W).obj M) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro orthogonal M hM
  exact
    D.finiteDimensionalModuleOrbitSkeletonPushdown_indecomposable_of_selfShiftHomOrthogonal
      (k := k) M.1 hM (orthogonal M M)

/-- On a translate-orthogonal window, finite skeletal push-down identifies
irreducibility once the relevant downstairs factorizations stay in the local
essential image. -/
theorem isIrreducibleMorphism_finiteOrbitPushdownWindowMap_iff
    (W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    D.FiniteModuleWindowShiftHomOrthogonal (k := k) W →
      ∀ {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y},
      MagnitudeConjecture.IsLocallyFactorizationClosedAt
          (D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W) f →
        (IsIrreducibleMorphism
            ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
              (k := k) W).map f) ↔
          IsIrreducibleMorphism f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro orthogonal X Y f hclosed
  exact
    (D.finiteDimensionalModuleOrbitSkeletonPushdownWindowOrbitHomDecomposition
      (k := k) W).isIrreducibleMorphism_map_iff_of_orthogonal
        (D.finiteModuleWindowTranslateHomOrthogonal_of_shiftHomOrthogonal
          (k := k) W orthogonal) hclosed

/-- The same local interface transports right almost-split maps. -/
theorem rightAlmostSplit_finiteOrbitPushdownWindowMap
    (W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    D.FiniteModuleWindowShiftHomOrthogonal (k := k) W →
      ∀ {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y},
      IsRightAlmostSplit f →
      MagnitudeConjecture.IsLocallyRightObjectClosedAt
          (D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W) Y →
        IsRightAlmostSplit
          ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
            (k := k) W).map f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro orthogonal X Y f hf hclosed
  exact
    (D.finiteDimensionalModuleOrbitSkeletonPushdownWindowOrbitHomDecomposition
      (k := k) W).rightAlmostSplit_map_of_orthogonal
        (D.finiteModuleWindowTranslateHomOrthogonal_of_shiftHomOrthogonal
          (k := k) W orthogonal) hf hclosed

/-- The dual local interface transports left almost-split maps. -/
theorem leftAlmostSplit_finiteOrbitPushdownWindowMap
    (W : Set (FiniteDimensionalModuleCategory.{u, v, uK, uM} (C := C) k)) :
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    letI := isLinearModule_stableUnderShift (k := k) D.core
    letI := linearModuleCategoryHasShift (k := k) D.core
    letI := linearModuleCategoryAdditiveShift (R := k) D.core
    letI := linearModuleCategoryLinearShift (R := k) D.core
    letI := trivialHasShift
      (LinearModuleCategory.{u, max v w, uK, max w uM}
        (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
    D.FiniteModuleWindowShiftHomOrthogonal (k := k) W →
      ∀ {X Y : CoveringSeparation.WindowCategory W} {f : X ⟶ Y},
      IsLeftAlmostSplit f →
      MagnitudeConjecture.IsLocallyLeftObjectClosedAt
          (D.finiteDimensionalModuleOrbitSkeletonPushdownWindow (k := k) W) X →
        IsLeftAlmostSplit
          ((D.finiteDimensionalModuleOrbitSkeletonPushdownWindow
            (k := k) W).map f) := by
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := isLinearModule_stableUnderShift (k := k) D.core
  letI := linearModuleCategoryHasShift (k := k) D.core
  letI := linearModuleCategoryAdditiveShift (R := k) D.core
  letI := linearModuleCategoryLinearShift (R := k) D.core
  letI := trivialHasShift
    (LinearModuleCategory.{u, max v w, uK, max w uM}
      (C := ShiftOrbitCategory C (Additive G)) k) (Additive G)
  intro orthogonal X Y f hf hclosed
  exact
    (D.finiteDimensionalModuleOrbitSkeletonPushdownWindowOrbitHomDecomposition
      (k := k) W).leftAlmostSplit_map_of_orthogonal
        (D.finiteModuleWindowTranslateHomOrthogonal_of_shiftHomOrthogonal
          (k := k) W orthogonal) hf hclosed

end MagnitudeConjecture.CoveringHom.CoherentDeckShift
