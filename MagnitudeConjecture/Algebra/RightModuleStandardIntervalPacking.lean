import MagnitudeConjecture.Algebra.RightModuleStandardIntervalCategorySurplus
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSimpleCount
import MagnitudeConjecture.Algebra.RightModuleIntervalInequality
import MagnitudeConjecture.CategoryTheory.GradedPrincipalPackedSurplus
import MagnitudeConjecture.Combinatorics.SeparatedIntervalSurplus

/-! # Separated packing and equality for actual standard-form interval surpluses -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)
attribute [local irreducible] standardFormIntervalSkeleton
  standardFormIntervalCategoryAlgebraEquivalence CoveringHom.finiteCategorySurplus
local instance intervalPackingBaseFinite :
    FiniteDimensional k (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite
local instance intervalPackingAlgebraFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) := S.standardFormIntervalAlgebra_finiteDimensional m
local instance intervalPackingAlgebraNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

/-- Separated copies of the actual small interval cannot have greater surplus
than the ambient interval containing them. -/
theorem standardFormInterval_surplus_packing (r q : ℕ) :
    (q : ℤ) * (S.standardFormIntervalSkeleton r).ambientARSurplus ≤
      (S.standardFormIntervalSkeleton
        (GradedInterval.packingEnd r S.standardFormIntervalControlHeight q)).ambientARSurplus := by
  have hp := Graded.FiniteGradedModule.principalInterval_surplus_packing
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)
    S.standardFormOppositeAlgebra_mul_mem S.standardFormHomogeneousIdempotent
    S.standardFormHomogeneousIdempotent_mem_zero S.standardFormHomogeneousIdempotent_idempotent
    S.standardFormHomogeneousCorner_diagonal S.standardFormOppositeAlgebra_negative
    S.standardFormHomogeneousCorner_off_diagonal S.standardFormIntervalControlHeight
    S.standardFormOppositeAlgebra_above_control r q
    (S.standardFormIntervalCategory_repFinite _)
    (S.standardFormIntervalCategory_repFinite r)
    (S.standardFormIntervalCategory_directed _)
  exact le_of_eq_of_le
    (congrArg (fun z : ℤ ↦ (q : ℤ) * z) (S.standardFormIntervalCategory_surplus_eq r).symm)
    (le_of_le_of_eq hp (S.standardFormIntervalCategory_surplus_eq _))

/-- Packing and the uniform interval error bound give the manuscript's upper surplus bound. -/
theorem standardFormInterval_surplus_le_length_mul (r : ℕ) :
    (S.standardFormIntervalSkeleton r).ambientARSurplus ≤
      ((r : ℤ) + S.standardFormIntervalControlHeight + 1) * S.ambientARSurplus :=
  GradedInterval.interval_le_length_mul_of_separated_packing S.ambientARSurplus
    (fun m ↦ (S.standardFormIntervalSkeleton m).ambientARSurplus)
    S.standardFormIntervalSurplusErrorBound S.standardFormIntervalControlHeight
    S.standardFormInterval_surplus_error_uniform S.standardFormInterval_surplus_packing r

/-- At zero ambient surplus, every actual finite interval has zero surplus. -/
theorem standardFormInterval_surplus_eq_zero_of_ambient_eq_zero
    (hz : S.ambientARSurplus = 0) (r : ℕ) :
    (S.standardFormIntervalSkeleton r).ambientARSurplus = 0 := by
  apply le_antisymm
  · simpa only [hz, mul_zero] using S.standardFormInterval_surplus_le_length_mul r
  · exact S.standardFormInterval_surplus_nonnegative r

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
