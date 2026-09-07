import MagnitudeConjecture.CategoryTheory.AlmostSplitEquivalence
import MagnitudeConjecture.CategoryTheory.LocallyFiniteModuleLocalDensity

/-!
# Intrinsic local density under module equivalence

An additive equivalence of finite-dimensional module categories preserves a
minimal sink, its indecomposable source arity, and projectivity of its
endpoint.  It therefore preserves intrinsic local density.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u₁ u₂ v

variable {k : Type v} [Field k]
variable {C : Type u₁} [Category.{v} C] [Preadditive C] [Linear k C]
variable {D : Type u₂} [Category.{v} D] [Preadditive D] [Linear k D]

/-- Intrinsic module local density is preserved by an additive equivalence
of finite-dimensional module categories. -/
theorem finiteModuleLocalDensity_map_equivalence
    (hC : IsLocallyRepresentationFinite (k := k) (C := C))
    (hD : IsLocallyRepresentationFinite (k := k) (C := D))
    (e : FiniteDimensionalModuleCategory.{u₂, v, v, v} (C := D) k ≌
      FiniteDimensionalModuleCategory.{u₁, v, v, v} (C := C) k)
    [e.functor.Additive]
    (M : FiniteDimensionalModuleCategory.{u₂, v, v, v} (C := D) k)
    (hM : Indecomposable M) :
    finiteModuleLocalDensity hC (e.functor.obj M)
        ((MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
          e.functor M).2 hM) =
      finiteModuleLocalDensity hD M hM := by
  classical
  let A := finiteModuleMinimalSinkData hD M hM
  let hMapIndec (i : Fin A.decomposition.n) :
      Indecomposable (e.functor.obj (A.decomposition.summand i)) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      e.functor (A.decomposition.summand i)).2
        (A.decomposition.indecomposable i)
  let dMap := A.decomposition.mapOfIndecomposable e.functor hMapIndec
  have hAS : IsRightAlmostSplit (e.functor.map A.map) :=
    A.rightAlmostSplit.map_equivalence e
  have hmin : IsRightMinimal (e.functor.map A.map) :=
    A.rightMinimal.map_equivalence e
  have hMapped :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      hC (e.functor.obj M)
      ((MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        e.functor M).2 hM)
      dMap hAS hmin
  have hOriginal :=
    finiteModuleLocalDensity_eq_of_minimalRightAlmostSplitDecomposition
      hD M hM A.decomposition A.rightAlmostSplit A.rightMinimal
  rw [hMapped, hOriginal,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity,
    MagnitudeConjecture.ARCount.localDensityOfIncomingArity]
  have hprojective : Projective (e.functor.obj M) ↔ Projective M :=
    e.map_projective_iff M
  have hn : dMap.n = A.decomposition.n := by
    rfl
  rw [hn]
  by_cases h : Projective M
  · have h' : Projective (e.functor.obj M) := hprojective.2 h
    simp [h, h']
  · have h' : ¬ Projective (e.functor.obj M) :=
      fun hE ↦ h (hprojective.1 hE)
    simp [h, h']

end MagnitudeConjecture.CoveringHom
