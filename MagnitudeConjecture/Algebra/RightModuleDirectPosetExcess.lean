import MagnitudeConjecture.Algebra.RightModuleDirectPosetGrading
import MagnitudeConjecture.Algebra.RightModuleDirectHeightExcess

/-! # Nonnegative primitive-factor excess from direct heights -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] [IsAlgClosed k]
variable {S : FiniteIndecomposableSkeleton k A} {e : A} {D : PrimitiveIdempotentData e}
namespace PrimitiveDirectedBoundaryData

/-- The poset chain bound applies to the directly constructed sink height. -/
theorem directFactorHeight_card_le
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D)) :
    Fintype.card B.ProjectivePoset ≤
      B.directFactorHeight (S.primitiveMultiplicityInput D).sink :=
  PosetSpace.card_le_of_schurPositiveGrading k B.ProjectivePoset B.directFactorSchurPositiveGrading

/-- The direct sink height is at least the number of factor projectives minus one. -/
theorem directFactorHeight_projectiveCount_le
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D)) :
    ARCount.projectiveCount
      (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D)).IsProjective - 1 ≤
      (B.directFactorHeight (S.primitiveMultiplicityInput D).sink : ℤ) := by
  have hc := B.projectivePosetData.card_factorProjectiveLabel
  have hb := B.directFactorHeight_card_le
  change (Fintype.card (S.FactorProjectiveLabel (S.primitiveKilledLabels D)) : ℤ) - 1 ≤ _
  rw [hc]
  have hbZ : (Fintype.card B.ProjectivePoset : ℤ) ≤
      (B.directFactorHeight (S.primitiveMultiplicityInput D).sink : ℤ) := by exact_mod_cast hb
  omega

/-- Primitive-factor excess is nonnegative by the new arrow count and the
generated-relations poset realization. -/
theorem directHeight_intrinsicExcess_nonnegative
    (B : S.PrimitiveDirectedBoundaryData (S.primitiveMultiplicityInput D)) :
    0 ≤ DirectedDeletion.intrinsicEulerExcess
      (MagnitudeConjecture.FiniteTauMatrix.meshMatrix
        (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D))) :=
  B.directHeight_intrinsicExcess_nonnegative_iff.mpr B.directFactorHeight_projectiveCount_le

end PrimitiveDirectedBoundaryData
end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
