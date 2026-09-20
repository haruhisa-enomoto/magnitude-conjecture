import MagnitudeConjecture.Algebra.RightModuleStandardGradedIncoming
import MagnitudeConjecture.Algebra.RightModuleStandardFormARRightAlmostSplit
import MagnitudeConjecture.CategoryTheory.AlmostSplitNatIso

/-! # The actual graded incoming maps are minimal right almost split -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
local instance gradedIncomingASQuiver : Quiver (Fin S.n) := S.standardFormQuiver
local instance gradedIncomingASArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- The actual incoming matrix has the same finitely generated realization
as the established recovered mesh. -/
def standardGradedIncomingRecoveryIso :
    (S.standardFormMeshRawFunctor (k := k)).mapMat_ ⋙
      (S.standardFormGradedFunctor ⋙ Graded.FiniteGradedModule.underlyingFG) ≅
    S.standardFormAdditiveRestrictedYonedaFunctor (k := k) ⋙
      S.standardFormProjectiveVertexModuleAlgebraEquivalence.functor :=
  Functor.isoWhiskerLeft _ S.standardFormGradedUnderlyingFGNatIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight S.standardGradedRawRecoveryIso
      S.standardFormProjectiveVertexModuleAlgebraEquivalence.functor

/-- Before the endpoint identification, the recovered incoming matrix is almost split. -/
theorem standardGradedRecoveryIncoming_rightAlmostSplit (z : Fin S.n) :
    IsRightAlmostSplit
      ((S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).map
        (S.standardFormRightMeshData.additiveIncomingMap (k := k) z)) := by
  have h := (S.standardFormRecoveredIncomingMap_rightAlmostSplit (k := k) z).postcomp_iso
    (S.standardFormAdditiveRestrictedYonedaSingletonIso (k := k) z).symm
  rw [S.standardFormRecoveredIncomingMap_eq_map_additiveIncoming_comp_singletonIso] at h
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- Before the endpoint identification, the recovered incoming matrix is right minimal. -/
theorem standardGradedRecoveryIncoming_rightMinimal (z : Fin S.n) :
    IsRightMinimal
      ((S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).map
        (S.standardFormRightMeshData.additiveIncomingMap (k := k) z)) := by
  have h := (S.standardFormRecoveredIncomingMap_rightMinimal (k := k) z).postcomp_iso
    (S.standardFormAdditiveRestrictedYonedaSingletonIso (k := k) z).symm
  rw [S.standardFormRecoveredIncomingMap_eq_map_additiveIncoming_comp_singletonIso] at h
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- The degree-one incoming map is almost split in the full graded module category. -/
theorem standardFormGradedIncomingMap_rightAlmostSplit (z : Fin S.n) (t : ℤ) :
    IsRightAlmostSplit (S.standardFormGradedIncomingMap z t) := by
  apply Graded.FiniteGradedModule.rightAlmostSplit_of_underlyingFG
  exact MagnitudeConjecture.CategoryTheory.rightAlmostSplit_map_of_natIso
    S.standardGradedIncomingRecoveryIso
    (S.standardFormRightMeshData.additiveIncomingMap (k := k) z)
    ((S.standardGradedRecoveryIncoming_rightAlmostSplit z).map_equivalence
      S.standardFormProjectiveVertexModuleAlgebraEquivalence)

/-- The same concrete map is right minimal after grading and shifting. -/
theorem standardFormGradedIncomingMap_rightMinimal (z : Fin S.n) (t : ℤ) :
    IsRightMinimal (S.standardFormGradedIncomingMap z t) := by
  apply Graded.FiniteGradedModule.rightMinimal_of_underlyingFG
  exact MagnitudeConjecture.CategoryTheory.rightMinimal_map_of_natIso
    S.standardGradedIncomingRecoveryIso
    (S.standardFormRightMeshData.additiveIncomingMap (k := k) z)
    ((S.standardGradedRecoveryIncoming_rightMinimal z).map_equivalence
      S.standardFormProjectiveVertexModuleAlgebraEquivalence)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
