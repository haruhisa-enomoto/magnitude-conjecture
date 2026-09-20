import MagnitudeConjecture.Algebra.RightModuleDirectHeightArrowCount
import MagnitudeConjecture.Combinatorics.DirectedDeletion

/-! # Intrinsic matrix excess in terms of the direct height -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A}
variable {K : Set (Fin S.n)} {D : S.PrimitiveMultiplicityInput K}
local instance : DecidablePred (fun p : Prop ↦ p) := Classical.propDecidable

/-- The literal matrix-defined intrinsic excess is L−(p−1), where L is the
direct sink height and p counts projective factor vertices. -/
theorem PrimitiveDirectedBoundaryData.directHeight_intrinsicExcess
    (B : S.PrimitiveDirectedBoundaryData D) :
    DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix (S.factorFiniteTauCategoryData K)) =
    (B.directFactorHeight D.sink : ℤ) -
      (ARCount.projectiveCount (S.factorFiniteTauCategoryData K).IsProjective - 1) := by
  rw [DirectedDeletion.intrinsicEulerExcess, MagnitudeConjecture.FiniteTauMatrix.meshMatrix,
    ARCount.matrixTotal_meshMatrix_eq_eulerMagnitude, ARCount.eulerMagnitude]
  have hc := ARCount.vertexCount_eq_projectiveCount_add_meshCount
    (S.factorFiniteTauCategoryData K).IsProjective
  have ha := B.directHeight_arrow_count
  unfold ARCount.vertexCount ARCount.arrowCount at *
  omega

/-- The remaining numerical inequality is exactly the projective-count
bound on the direct sink height. -/
theorem PrimitiveDirectedBoundaryData.directHeight_intrinsicExcess_nonnegative_iff
    (B : S.PrimitiveDirectedBoundaryData D) :
    0 ≤ DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix (S.factorFiniteTauCategoryData K)) ↔
    ARCount.projectiveCount (S.factorFiniteTauCategoryData K).IsProjective - 1 ≤
      (B.directFactorHeight D.sink : ℤ) := by
  rw [B.directHeight_intrinsicExcess]
  omega

/-- Vanishing intrinsic excess is exactly equality in the height bound. -/
theorem PrimitiveDirectedBoundaryData.directHeight_intrinsicExcess_eq_zero_iff
    (B : S.PrimitiveDirectedBoundaryData D) :
    DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix (S.factorFiniteTauCategoryData K)) = 0 ↔
    (B.directFactorHeight D.sink : ℤ) =
      ARCount.projectiveCount (S.factorFiniteTauCategoryData K).IsProjective - 1 := by
  rw [B.directHeight_intrinsicExcess]
  omega

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
