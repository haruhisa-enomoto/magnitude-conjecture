import MagnitudeConjecture.Algebra.RightModuleDirectHeightWeightedCount

/-! # Exact boundary degrees for the direct height count -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
namespace PrimitiveDirectedBoundaryData

private theorem sum_eq_one_of_positive_weighted_sum_eq_one
    {ι : Type u} [Fintype ι]
    (a weight : ι → ℕ) (weight_pos : ∀ i, 0 < weight i)
    (hweighted : ∑ i, (a i : ℤ) * weight i = 1) :
    (∑ i, (a i : ℤ)) = 1 := by
  classical
  have hweightedNat : ∑ i, a i * weight i = 1 := by
    exact_mod_cast hweighted
  have hle : ∑ i, a i ≤ ∑ i, a i * weight i := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.le_mul_of_pos_right (a i) (weight_pos i)
  have hne : ∑ i, a i ≠ 0 := by
    intro hzero
    have ha : ∀ i, a i = 0 := by
      have hafun : a = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg
          (fun j ↦ Nat.zero_le (a j))).1 hzero
      exact fun i ↦ congrFun hafun i
    simp [ha] at hweightedNat
  have hsum : ∑ i, a i = 1 := by omega
  exact_mod_cast hsum

/-- A tau-projective vertex other than the distinguished source has exactly
one incoming official arrow occurrence. -/
theorem directCount_incoming_eq_one
    (B : S.PrimitiveDirectedBoundaryData D)
    (Y : S.SurvivingLabel K)
    (hprojective : (S.factorFiniteTauCategoryData K).IsProjective Y)
    (hsource : Y ≠ D.source) :
    (∑ X, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y : ℤ)) = 1 := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let weight : S.SurvivingLabel K → ℕ := fun X ↦ D.multiplicity X.1
  have hunit := D.meshUnitEquations.1 Y
  have hweightY : weight Y = 1 := by
    exact B.projective_multiplicity_eq_one ⟨Y, hprojective⟩
  have hweighted :
      ∑ X, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
          T.toFiniteRightTauCategoryData X Y : ℤ) * weight X = 1 := by
    change MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight T
      (fun X ↦ (weight X : ℤ)) Y = if Y = D.source then 1 else 0 at hunit
    rw [MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight] at hunit
    simp_rw [MagnitudeConjecture.FiniteTauMatrix.meshMatrix_apply_of_projective
      T hprojective] at hunit
    simp only [mul_sub, Finset.sum_sub_distrib] at hunit
    have hindicator :
        ∑ X, (weight X : ℤ) * (if X = Y then 1 else 0) = weight Y := by
      simp
    rw [hindicator] at hunit
    simp [hsource, hweightY] at hunit
    simpa only [mul_comm] using (show
      ∑ X, (weight X : ℤ) *
          MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X Y = 1 by
        omega)
  exact sum_eq_one_of_positive_weighted_sum_eq_one
    (fun X ↦ MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X Y)
    weight
    (fun X ↦ PrimitiveMultiplicityInput.multiplicity_pos (S := S) D X)
    hweighted

/-- A tau-injective vertex other than the distinguished sink has exactly one
outgoing official arrow occurrence. -/
theorem directCount_outgoing_eq_one
    (B : S.PrimitiveDirectedBoundaryData D)
    (X : S.SurvivingLabel K)
    (hinjective : (S.factorFiniteTauCategoryData K).IsInjective X)
    (hsink : X ≠ D.sink) :
    (∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y : ℤ)) = 1 := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let weight : S.SurvivingLabel K → ℕ := fun Y ↦ D.multiplicity Y.1
  have hunit := D.meshUnitEquations.2 X
  have hweightX : weight X = 1 := by
    exact B.injective_multiplicity_eq_one ⟨X, hinjective⟩
  rw [MagnitudeConjecture.FiniteTauMatrix.meshRowWeight_eq_of_injective T
      (fun Y ↦ (weight Y : ℤ)) X hinjective] at hunit
  have hweighted :
      ∑ Y, (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
            T.toFiniteRightTauCategoryData X Y : ℤ) * weight Y = 1 := by
    simp [hsink, hweightX] at hunit
    omega
  exact sum_eq_one_of_positive_weighted_sum_eq_one
    (fun Y ↦ MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity T.toFiniteRightTauCategoryData X Y)
    weight
    (fun Y ↦ PrimitiveMultiplicityInput.multiplicity_pos (S := S) D Y)
    hweighted


end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
