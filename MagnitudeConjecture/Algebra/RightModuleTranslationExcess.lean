import MagnitudeConjecture.Algebra.RightModuleTranslationSlices

/-!
# Global Euler counts from concrete translation slices

The concrete level fibers partition all surviving indecomposables.  Since
official arrow multiplicities are supported only on adjacent levels, the
sum of the adjacent slice counts is the global arrow count.  These two facts
identify the mesh-matrix total with the graded Euler expression used by the
intrinsic factor-excess theorem.
-/

set_option autoImplicit false
noncomputable section

open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}

namespace PrimitiveDirectedBoundaryData

/-- Every surviving label, tagged by its concrete level. -/
def standardFactorLevelSigmaEquiv
    (B : S.PrimitiveDirectedBoundaryData D) :
    S.SurvivingLabel K ≃
      Σ j : Fin (B.standardFactorLength + 1),
        B.StandardFactorLevelVertex j.val where
  toFun x :=
    ⟨⟨B.standardFactorLevel x,
        Nat.lt_succ_iff.mpr (B.standardFactorLevel_le_length x)⟩,
      ⟨x, rfl⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨j, hj⟩, ⟨x, hx⟩⟩
    dsimp at hx
    subst j
    rfl

/-- The sum of the concrete level-fiber cardinalities is the global factor
vertex count. -/
theorem standardFactorVertexTotal_eq_vertexCount
    (B : S.PrimitiveDirectedBoundaryData D) :
    MagnitudeConjecture.GradedTreeExcess.vertexTotal
        (fun j : Fin (B.standardFactorLength + 1) ↦
          B.standardFactorVertexCount j.val) =
      MagnitudeConjecture.ARCount.vertexCount
        (ι := S.SurvivingLabel K) := by
  have hcard := Fintype.card_congr B.standardFactorLevelSigmaEquiv
  have hsigma :
      Fintype.card
          (Σ j : Fin (B.standardFactorLength + 1),
            B.StandardFactorLevelVertex j.val) =
        ∑ j : Fin (B.standardFactorLength + 1),
          Fintype.card (B.StandardFactorLevelVertex j.val) :=
    Fintype.card_sigma
  rw [MagnitudeConjecture.GradedTreeExcess.vertexTotal]
  simp only [standardFactorVertexCount,
    MagnitudeConjecture.ARCount.vertexCount]
  exact_mod_cast hsigma.symm.trans hcard.symm

/-- There is no adjacent arrow slice above the top concrete level. -/
theorem standardFactorArrowCount_length
    (B : S.PrimitiveDirectedBoundaryData D) :
    B.standardFactorArrowCount B.standardFactorLength = 0 := by
  classical
  rw [standardFactorArrowCount]
  apply Finset.sum_eq_zero
  intro X hX
  apply Finset.sum_eq_zero
  intro Y hY
  have hle := B.standardFactorLevel_le_length Y.1
  have hlevel : B.standardFactorLevel Y.1 =
      B.standardFactorLength + 1 := Y.2
  omega

/-- Summing the concrete adjacent-level slices recovers the global official
arrow multiplicity count. -/
theorem standardFactorArrowTotal_eq_arrowCount
    (B : S.PrimitiveDirectedBoundaryData D) :
    MagnitudeConjecture.GradedTreeExcess.arrowTotal
        (fun j : Fin B.standardFactorLength ↦
          B.standardFactorArrowCount j.val) =
      MagnitudeConjecture.ARCount.arrowCount
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData) := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let E := B.standardFactorLevelSigmaEquiv
  let outgoing
      (p : Σ j : Fin (B.standardFactorLength + 1),
        B.StandardFactorLevelVertex j.val) : ℤ :=
    ∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      T.toFiniteRightTauCategoryData p.2.1 Y : ℤ)
  have hreindex :
      (∑ X : S.SurvivingLabel K, outgoing (E X)) =
        ∑ p : Σ j : Fin (B.standardFactorLength + 1),
          B.StandardFactorLevelVertex j.val, outgoing p :=
    E.sum_comp outgoing
  symm
  calc
    MagnitudeConjecture.ARCount.arrowCount
        (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData) =
        ∑ X : S.SurvivingLabel K,
          ∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData X Y : ℤ) := rfl
    _ = ∑ p : Σ j : Fin (B.standardFactorLength + 1),
          B.StandardFactorLevelVertex j.val,
        ∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData p.2.1 Y : ℤ) := by
      exact hreindex
    _ = ∑ p : Σ j : Fin (B.standardFactorLength + 1),
          B.StandardFactorLevelVertex j.val,
        ∑ Y : B.StandardFactorLevelVertex (p.1.val + 1),
          (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData p.2.1 Y.1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (B.sum_factorArrowMultiplicity_target_level
        p.1.val p.2.1 p.2.2).symm
    _ = ∑ j : Fin (B.standardFactorLength + 1),
          B.standardFactorArrowCount j.val := by
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ j : Fin B.standardFactorLength,
          B.standardFactorArrowCount j.val := by
      have hlast : B.standardFactorArrowCount
          (Fin.last B.standardFactorLength).val = 0 := by
        simpa using B.standardFactorArrowCount_length
      rw [Fin.sum_univ_castSucc, hlast]
      simp
    _ = MagnitudeConjecture.GradedTreeExcess.arrowTotal
        (fun j : Fin B.standardFactorLength ↦
          B.standardFactorArrowCount j.val) := rfl

omit [IsAlgClosed k] in
/-- The global tau-projective count is the root plus the cardinality of the
projective poset used in the realization. -/
theorem standardFactorProjectiveCount_eq_projectivePoset_card_add_one
    (B : S.PrimitiveDirectedBoundaryData D) :
    MagnitudeConjecture.ARCount.projectiveCount
        (S.factorFiniteTauCategoryData K).IsProjective =
      (Fintype.card B.ProjectivePoset : ℤ) + 1 := by
  classical
  have hcard := B.card_factorProjectiveLabel
  rw [MagnitudeConjecture.ARCount.projectiveCount]
  exact_mod_cast hcard

/-- The factor mesh-matrix total is exactly the global Euler expression
obtained by summing the concrete level slices. -/
theorem standardFactorMeshEulerTotal
    (B : S.PrimitiveDirectedBoundaryData D) :
    MagnitudeConjecture.ARCount.matrixTotal
        (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
          (S.factorFiniteTauCategoryData K)) =
      MagnitudeConjecture.GradedTreeExcess.vertexTotal
          (fun j : Fin (B.standardFactorLength + 1) ↦
            B.standardFactorVertexCount j.val) -
        MagnitudeConjecture.GradedTreeExcess.arrowTotal
          (fun j : Fin B.standardFactorLength ↦
            B.standardFactorArrowCount j.val) +
          (MagnitudeConjecture.GradedTreeExcess.vertexTotal
              (fun j : Fin (B.standardFactorLength + 1) ↦
                B.standardFactorVertexCount j.val) -
            MagnitudeConjecture.ARCount.projectiveCount
              (S.factorFiniteTauCategoryData K).IsProjective) := by
  classical
  have hpartition :=
    MagnitudeConjecture.ARCount.vertexCount_eq_projectiveCount_add_meshCount
      (S.factorFiniteTauCategoryData K).IsProjective
  rw [MagnitudeConjecture.FiniteTauMatrix.meshMatrix]
  rw [MagnitudeConjecture.ARCount.matrixTotal_meshMatrix_eq_eulerMagnitude]
  rw [MagnitudeConjecture.ARCount.eulerMagnitude]
  rw [B.standardFactorVertexTotal_eq_vertexCount,
    B.standardFactorArrowTotal_eq_arrowCount]
  omega

end PrimitiveDirectedBoundaryData

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
