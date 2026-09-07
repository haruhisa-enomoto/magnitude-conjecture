import MagnitudeConjecture.CategoryTheory.LocallyFiniteModuleLocalDensity
import MagnitudeConjecture.CategoryTheory.FiniteSkeletonShiftAction

/-!
# Intrinsic and finite-skeleton local density

A complete finite indecomposable skeleton implies local representation-
finiteness.  At each skeleton label, the intrinsic local density defined
from an arbitrary minimal sink agrees with the finite right-tau density.
Thus the manuscript's sum of intrinsic local densities is the existing
finite Auslander--Reiten surplus.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

namespace FiniteDimensionalModuleIndecomposableSkeleton

variable (S : FiniteDimensionalModuleIndecomposableSkeleton
  (k := k) (C := C))

/-- A complete finite indecomposable skeleton supplies the manuscript's
pointwise local representation-finiteness condition. -/
theorem isLocallyRepresentationFinite
    (S : FiniteDimensionalModuleIndecomposableSkeleton
      (k := k) (C := C)) :
    IsLocallyRepresentationFinite (k := k) (C := C) := by
  intro X
  exact ⟨
    { n := S.n
      obj := S.obj
      indecomposable := S.indecomposable
      covers := by
        intro Y hY _
        obtain ⟨i, ⟨e⟩⟩ := S.complete Y hY
        exact ⟨i, ⟨e.symm⟩⟩ }⟩

variable [EnoughProjectives
  (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]

/-- Intrinsic local density agrees labelwise with the local density of the
complete finite right-tau skeleton. -/
theorem finiteModuleLocalDensity_eq_rightTauLocalDensity
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C))
    (i : Fin S.n) :
    finiteModuleLocalDensity hlocal (S.obj i) (S.indecomposable i) =
      S.rightTauLocalDensity i := by
  classical
  let T := S.toFiniteRightTauCategoryData
  let d :=
    MagnitudeConjecture.FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition
      T i
  let f := (T.rightMesh (T.obj i)).g ≫ (T.rightTermIso (T.obj i)).hom
  change finiteModuleLocalDensity hlocal (S.obj i) (S.indecomposable i) =
    CoveringAction.occurrenceLocalDensity
      (MagnitudeConjecture.FiniteTauMatrix.rightArrowTarget T)
      T.IsProjective i
  have hf : IsRightAlmostSplit f :=
    MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit T i
  have hfmin : IsRightMinimal f :=
    MagnitudeConjecture.FiniteTauMatrix.rightMesh_terminal_isRightMinimal T i
  rw [finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      hlocal (S.obj i) (S.indecomposable i) d hf hfmin,
    MagnitudeConjecture.FiniteTauMatrix.occurrenceLocalDensity_rightArrowTarget_eq,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity]
  have hProjective : Projective (S.obj i) ↔ T.IsProjective i :=
    (MagnitudeConjecture.FiniteTauMatrix.isProjective_iff_projective_obj
      T i).symm
  have hArity : d.n =
      MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity T i := rfl
  rw [hArity]
  by_cases h : Projective (S.obj i)
  · have h' : T.IsProjective i := hProjective.1 h
    simp [h, h']
  · have h' : ¬ T.IsProjective i := fun hT ↦ h (hProjective.2 hT)
    simp [h, h']

/-- Summing intrinsic local density over a complete finite skeleton recovers
its Auslander--Reiten surplus. -/
theorem sum_finiteModuleLocalDensity_eq_surplus
    (hlocal : IsLocallyRepresentationFinite (k := k) (C := C)) :
    (∑ i : Fin S.n,
        finiteModuleLocalDensity hlocal (S.obj i) (S.indecomposable i)) =
      @MagnitudeConjecture.ARCount.surplus (Fin S.n) inferInstance
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          S.toFiniteRightTauCategoryData)
        S.toFiniteRightTauCategoryData.IsProjective (Classical.decPred _) := by
  calc
    (∑ i : Fin S.n,
        finiteModuleLocalDensity hlocal (S.obj i) (S.indecomposable i)) =
        ∑ i : Fin S.n, S.rightTauLocalDensity i := by
      apply Finset.sum_congr rfl
      intro i _
      exact S.finiteModuleLocalDensity_eq_rightTauLocalDensity hlocal i
    _ = _ := S.sum_rightTauLocalDensity_eq_surplus

end FiniteDimensionalModuleIndecomposableSkeleton

end MagnitudeConjecture.CoveringHom
