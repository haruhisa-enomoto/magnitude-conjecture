import MagnitudeConjecture.Algebra.RightModuleDirectHeightRank
import MagnitudeConjecture.Combinatorics.DirectMeshHeight

/-! # Direct heights on the actual primitive factor -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

/-- The official nonzero-arrow relation in the primitive factor. -/
def directFactorArrow (X Y : S.SurvivingLabel K) : Prop :=
  MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
    (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y ≠ 0

/-- Height constructed by predecessor induction, without standardness. -/
def PrimitiveDirectedBoundaryData.directFactorHeight
    (B : S.PrimitiveDirectedBoundaryData D) : S.SurvivingLabel K → ℕ :=
  DirectMeshHeight.height B.directHeightRank (directFactorArrow (S := S) (K := K))
    B.directHeightRank_lt_of_arrow

/-- Every actual arrow increases the direct height by one. -/
theorem PrimitiveDirectedBoundaryData.directFactorHeight_arrow
    (B : S.PrimitiveDirectedBoundaryData D)
    (X Y : S.SurvivingLabel K) (h : directFactorArrow X Y) :
    B.directFactorHeight Y = B.directFactorHeight X + 1 :=
  DirectMeshHeight.height_arrow B.directHeightRank _ B.directHeightRank_lt_of_arrow
    B.directHeight_local_conditions X Y h

/-- Every nonempty chosen middle term provides a nonzero incoming arrow. -/
theorem directFactorArrow_rightMiddleLabel
    (Y : S.SurvivingLabel K)
    (i : Fin (MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData Y)) :
    directFactorArrow
      (MagnitudeConjecture.FiniteTauMatrix.rightMiddleLabel
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData Y i) Y := by
  classical
  unfold directFactorArrow MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
  have h := Finset.single_le_sum (f := fun j ↦
      if MagnitudeConjecture.FiniteTauMatrix.rightMiddleLabel
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData Y j =
        MagnitudeConjecture.FiniteTauMatrix.rightMiddleLabel
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData Y i then 1 else 0)
    (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  simp only [ite_true] at h
  convert Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one h) using 1
  congr 1
  funext j
  split_ifs <;> rfl

/-- Translation lowers the direct height by two. -/
theorem PrimitiveDirectedBoundaryData.directFactorHeight_tauPlus
    (B : S.PrimitiveDirectedBoundaryData D)
    (Y : (S.factorFiniteTauCategoryData K).Nonprojective) :
    B.directFactorHeight Y.1 =
      B.directFactorHeight ((S.factorFiniteTauCategoryData K).tauPlus Y) + 2 := by
  let T := S.factorFiniteTauCategoryData K
  let i : Fin (MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
      T.toFiniteRightTauCategoryData Y.1) :=
    ⟨0, MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_pos_of_nonprojective T Y⟩
  exact DirectMeshHeight.height_mesh B.directHeightRank _ B.directHeightRank_lt_of_arrow
    B.directHeight_local_conditions (T.tauPlus Y) Y.1
    ⟨_, directFactorArrow_rightMiddleLabel Y.1 i⟩
    (B.directHeight_mesh_predecessor Y)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
