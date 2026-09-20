import MagnitudeConjecture.Algebra.RightModulePrimitiveFiniteKernelFactorBoundary
import MagnitudeConjecture.CategoryTheory.FiniteTauTranslationMultiplicity

/-! # Incoming boundary bounds for direct heights -/
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

/-- The positive coordinate mesh equation bounds the total incoming
multiplicity at every projective boundary vertex by one. -/
theorem PrimitiveDirectedBoundaryData.directHeight_incoming_le_one
    (B : S.PrimitiveDirectedBoundaryData D)
    (Y : S.SurvivingLabel K)
    (hY : (S.factorFiniteTauCategoryData K).IsProjective Y) :
    (∑ X, MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y) ≤ 1 := by
  classical
  let T := S.factorFiniteTauCategoryData K
  let a := fun X ↦ MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
    T.toFiniteRightTauCategoryData X Y
  let w := fun X : S.SurvivingLabel K ↦ D.multiplicity X.1
  have hw : w Y = 1 := B.projective_multiplicity_eq_one ⟨Y, hY⟩
  have hu := D.meshUnitEquations.1 Y
  change MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight T
    (fun X ↦ (w X : ℤ)) Y = if Y = D.source then 1 else 0 at hu
  rw [MagnitudeConjecture.FiniteTauMatrix.meshColumnWeight] at hu
  simp_rw [MagnitudeConjecture.FiniteTauMatrix.meshMatrix_apply_of_projective T hY] at hu
  simp only [mul_sub, Finset.sum_sub_distrib] at hu
  have hd : ∑ X, (w X : ℤ) * (if X = Y then 1 else 0) = w Y := by simp
  rw [hd, hw] at hu
  have hweighted : ∑ X, (a X : ℤ) * w X ≤ 1 := by
    dsimp only [a]
    simp only [mul_comm] at hu ⊢
    split_ifs at hu <;> omega
  have hweightedNat : ∑ X, a X * w X ≤ 1 := by exact_mod_cast hweighted
  have hle : ∑ X, a X ≤ ∑ X, a X * w X := by
    apply Finset.sum_le_sum
    intro X _
    exact Nat.le_mul_of_pos_right _
      (PrimitiveMultiplicityInput.multiplicity_pos (S := S) D X)
  exact hle.trans hweightedNat

/-- In particular, a projective boundary vertex has at most one distinct
predecessor in the official arrow relation. -/
theorem PrimitiveDirectedBoundaryData.directHeight_predecessor_unique
    (B : S.PrimitiveDirectedBoundaryData D)
    (Y : S.SurvivingLabel K)
    (hY : (S.factorFiniteTauCategoryData K).IsProjective Y)
    (X Z : S.SurvivingLabel K)
    (hX : MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y ≠ 0)
    (hZ : MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData Z Y ≠ 0) : X = Z := by
  classical
  by_contra hne
  let a := fun W ↦ MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
    (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData W Y
  have hpair : a X + a Z ≤ ∑ W, a W := by
    have h := Finset.sum_le_sum_of_subset
      (f := a) (show ({X, Z} : Finset (S.SurvivingLabel K)) ⊆ Finset.univ by simp)
    simpa [hne] using h
  have hbound := B.directHeight_incoming_le_one Y hY
  change a X ≠ 0 at hX
  change a Z ≠ 0 at hZ
  change (∑ W, a W) ≤ 1 at hbound
  omega

/-- Every predecessor of an interior vertex receives an arrow from its
translate, by equality of the official mesh multiplicities. -/
theorem PrimitiveDirectedBoundaryData.directHeight_mesh_predecessor
    (_B : S.PrimitiveDirectedBoundaryData D)
    (Y : (S.factorFiniteTauCategoryData K).Nonprojective)
    (X : S.SurvivingLabel K)
    (hX : MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y.1 ≠ 0) :
    MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
      (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData
      ((S.factorFiniteTauCategoryData K).tauPlus Y) X ≠ 0 := by
  classical
  let T := S.factorFiniteTauCategoryData K
  have h := MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity_eq_translation
    T D.homMeshInverseData D.leftMesh_epi (T.tauPlusEquiv Y) X
  have ht : T.tauMinus (T.tauPlusEquiv Y) = Y.1 :=
    congrArg Subtype.val (T.tauPlusEquiv.symm_apply_apply Y)
  rw [ht] at h
  exact h.trans_ne hX

/-- The actual primitive factor satisfies the complete local predecessor
hypothesis of the direct height induction. -/
theorem PrimitiveDirectedBoundaryData.directHeight_local_conditions
    (B : S.PrimitiveDirectedBoundaryData D) :
    let E := fun X Y : S.SurvivingLabel K ↦
      MagnitudeConjecture.FiniteTauMatrix.arrowMultiplicity
        (S.factorFiniteTauCategoryData K).toFiniteRightTauCategoryData X Y ≠ 0
    ∀ Y, (∀ X Z, E X Y → E Z Y → X = Z) ∨
      ∃ t, ∀ X, E X Y → E t X := by
  classical
  intro E Y
  by_cases hy : (S.factorFiniteTauCategoryData K).IsProjective Y
  · exact Or.inl (fun X Z ↦ B.directHeight_predecessor_unique Y hy X Z)
  · exact Or.inr ⟨(S.factorFiniteTauCategoryData K).tauPlus ⟨Y, hy⟩,
      fun X ↦ B.directHeight_mesh_predecessor ⟨Y, hy⟩ X⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
