import MagnitudeConjecture.Algebra.RightModuleDirectPosetExcess
import MagnitudeConjecture.Combinatorics.PosetSpaceUpperSetHeight

/-! # Sharp upper-set heights in a zero-excess primitive factor -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A} {e : A} {D : PrimitiveIdempotentData e}
namespace PrimitiveDirectedBoundaryData

/-- Zero excess makes the direct sink height equal to the size of the poset. -/
theorem directHeight_sink_eq_card_of_excess_zero
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (hz : DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D))) = 0) :
    B.directFactorHeight (S.primitiveMultiplicityInput D).sink =
      Fintype.card B.ProjectivePoset := by
  have he := B.directHeight_intrinsicExcess_eq_zero_iff.mp hz
  have hc := B.projectivePosetData.card_factorProjectiveLabel
  change (B.directFactorHeight (S.primitiveMultiplicityInput D).sink : ℤ) =
    (Fintype.card (S.FactorProjectiveLabel (S.primitiveKilledLabels D)) : ℤ) - 1 at he
  rw [hc] at he
  omega

/-- Every upper-set line has its support cardinality as direct height in
the equality case. -/
theorem directSchurLevel_line_eq_card_of_excess_zero
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (hz : DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D))) = 0)
    (U : Finset B.ProjectivePoset) (hU : IsUpperSet (U : Set B.ProjectivePoset)) :
    B.directFactorSchurLevel (PosetSpace.line k B.ProjectivePoset (U : Set _) hU) = U.card :=
  PosetSpace.line_level_eq_card_of_sharp_grading B.directFactorSchurPositiveGrading
    (le_of_eq (B.directHeight_sink_eq_card_of_excess_zero hz)) U hU

/-- The actual selected factor representative of an upper-set line has
height equal to the support cardinality. -/
theorem directHeight_lineLabel_eq_card_of_excess_zero
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D))
    (hz : DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D))) = 0)
    (U : Finset B.ProjectivePoset) (hU : IsUpperSet (U : Set B.ProjectivePoset)) :
    B.directFactorHeight (B.directFactorSchurLabel
      (PosetSpace.line k B.ProjectivePoset (U : Set _) hU)
      (PosetSpace.line_isSchur k B.ProjectivePoset _ hU)) = U.card := by
  rw [← B.directFactorSchurLevel_of_isSchur]
  exact B.directSchurLevel_line_eq_card_of_excess_zero hz U hU

end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
