import MagnitudeConjecture.Algebra.RightModuleDirectFactorHeight
import MagnitudeConjecture.Combinatorics.RankedReachability

/-! # Source normalization of the direct factor height -/
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

/-- The source mesh equation has zero incoming contribution. -/
theorem PrimitiveDirectedBoundaryData.directHeight_source_incoming_zero
    (B : S.PrimitiveDirectedBoundaryData D) :
    (∑ X, MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X D.source) = 0 := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let a := fun X ↦ MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
    T.toFiniteRightTauCategoryData X D.source
  let w := fun X : S.SurvivingLabel K ↦ D.multiplicity X.1
  have hw : w D.source = 1 := B.projective_multiplicity_eq_one D.sourceProjectiveLabel
  have hu := D.meshUnitEquations.1 D.source
  change MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight T
    (fun X ↦ (w X : ℤ)) D.source = if D.source = D.source then 1 else 0 at hu
  rw [MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight] at hu
  have hp : T.IsProjective D.source := D.sourceProjectiveLabel.2
  simp_rw [MagnitudeConjecture.FiniteTauMatrix.meshMatrix_apply_of_projective T hp] at hu
  simp only [mul_sub, Finset.sum_sub_distrib, ite_true] at hu
  have hd : ∑ X, (w X : ℤ) * (if X = D.source then 1 else 0) = w D.source := by simp
  rw [hd, hw] at hu
  have hz : ∑ X, (a X : ℤ) * w X = 0 := by
    dsimp only [a]
    simp only [mul_comm] at hu ⊢
    omega
  have hzNat : ∑ X, a X * w X = 0 := by exact_mod_cast hz
  have hle : ∑ X, a X ≤ ∑ X, a X * w X := by
    apply Finset.sum_le_sum
    intro X _
    exact Nat.le_mul_of_pos_right _
      (PrimitiveMultiplicityInput.multiplicity_pos (S := S) D X)
  change (∑ X, a X) = 0
  omega

/-- No official arrow ends at the distinguished source. -/
theorem PrimitiveDirectedBoundaryData.directFactorArrow_source_false
    (B : S.PrimitiveDirectedBoundaryData D) (X : S.SurvivingLabel K) :
    ¬ directFactorArrow X D.source := by
  classical
  have h := B.directHeight_source_incoming_zero
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun Y (_ : Y ∈ (Finset.univ : Finset (S.SurvivingLabel K))) ↦
      Nat.zero_le (MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData Y D.source))).mp h
  exact fun hx ↦ hx (hz X (Finset.mem_univ X))

/-- The actual direct height is normalized to zero at P. -/
theorem PrimitiveDirectedBoundaryData.directFactorHeight_source
    (B : S.PrimitiveDirectedBoundaryData D) :
    B.directFactorHeight D.source = 0 := by
  apply DirectMeshHeight.height_eq_zero
  rintro ⟨X, hX⟩
  exact B.directFactorArrow_source_false X hX

/-- A vertex of height zero must be the distinguished source. -/
theorem PrimitiveDirectedBoundaryData.directFactorHeight_eq_zero_iff
    (B : S.PrimitiveDirectedBoundaryData D) (Y : S.SurvivingLabel K) :
    B.directFactorHeight Y = 0 ↔ Y = D.source := by
  classical
  constructor
  · intro hy
    let T := S.factorFiniteTauCategoryData K
    have ha : ∀ X, MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        T.toFiniteRightTauCategoryData X Y = 0 := by
      intro X
      by_contra hx
      have he := B.directFactorHeight_arrow X Y hx
      omega
    have hp : T.IsProjective Y := by
      by_contra hn
      let i : Fin (MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity
          T.toFiniteRightTauCategoryData Y) :=
        ⟨0, MagnitudeConjecture.FiniteTauMatrix.rightMiddleArity_pos_of_nonprojective
          T ⟨Y, hn⟩⟩
      exact directFactorArrow_rightMiddleLabel Y i (ha _)
    have hu := D.meshUnitEquations.1 Y
    change MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight T
      (fun X ↦ (D.multiplicity X.1 : ℤ)) Y = if Y = D.source then 1 else 0 at hu
    rw [MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight] at hu
    simp_rw [MagnitudeConjecture.FiniteTauMatrix.meshMatrix_apply_of_projective T hp,
      ha] at hu
    by_contra hne
    simp [hne] at hu
    have hpos := PrimitiveMultiplicityInput.multiplicity_pos (S := S) D Y
    omega
  · rintro rfl
    exact B.directFactorHeight_source

/-- Every surviving vertex is reached from P by official arrows. -/
theorem PrimitiveDirectedBoundaryData.directFactor_source_reaches
    (B : S.PrimitiveDirectedBoundaryData D) (Y : S.SurvivingLabel K) :
    Relation.ReflTransGen (directFactorArrow (S := S) (K := K)) D.source Y := by
  apply RankedReachability.source_reaches B.directHeightRank _
    B.directHeightRank_lt_of_arrow D.source _ Y
  intro X hx
  apply (B.directFactorHeight_eq_zero_iff X).1
  exact DirectMeshHeight.height_eq_zero _ _ _ X hx

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
