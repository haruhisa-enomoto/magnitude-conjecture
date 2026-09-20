import MagnitudeConjecture.Algebra.RightModuleStandardHomogeneousCorners
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSkeleton
import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalSimpleCount

/-! # The exact simple-module count of the standard-form interval algebra -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance standardIntervalSimpleBaseFinite :
    FiniteDimensional k (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite
local instance standardIntervalSimpleFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance standardIntervalSimpleNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- Every degree contributes one simple for each original simple class. -/
theorem standardFormInterval_simpleCount (m : ℕ)
    (T : RightModule.FiniteIndecomposableSkeleton k (S.standardFormIntervalAlgebra m)) :
    T.simpleCount = S.simpleCount * (m + 1) := by
  classical
  have h := Graded.FiniteGradedModule.principalIntervalAlgebra_simpleCount
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent
    S.standardFormHomogeneousCorner_diagonal S.standardFormOppositeAlgebra_negative
    S.standardFormHomogeneousCorner_off_diagonal m T
  have hc : Fintype.card S.StandardFormProjectiveMeshCategory = S.simpleCount := by
    rw [S.simpleCount_eq_card_projectiveLabel]
    simp only [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr S.projectiveLabelEquivSubtype).symm
  exact h.trans (congrArg (fun n ↦ n * (m + 1)) hc)

/-- The constructed interval skeleton realizes the exact simple-count formula. -/
theorem standardFormIntervalSkeleton_simpleCount (m : ℕ) :
    (S.standardFormIntervalSkeleton m).simpleCount = S.simpleCount * (m + 1) :=
  S.standardFormInterval_simpleCount m (S.standardFormIntervalSkeleton m)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
