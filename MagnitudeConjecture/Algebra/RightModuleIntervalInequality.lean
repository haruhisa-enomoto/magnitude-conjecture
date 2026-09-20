import MagnitudeConjecture.Algebra.RightModuleDirectedSurplus
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSurplusSlope
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSkeletonDirected

/-! # The magnitude surplus inequality from finite graded intervals -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)

local instance intervalInequalityFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance intervalInequalityNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- Every finite interval has nonnegative surplus by directed deletion. -/
theorem standardFormInterval_surplus_nonnegative (m : ℕ) :
    0 ≤ (S.standardFormIntervalSkeleton m).ambientARSurplus :=
  (S.standardFormIntervalSkeleton m).ambientARSurplus_nonnegative_of_directed
    (S.standardFormIntervalSkeleton_acyclic m)

/-- The uniform interval estimate proves the ambient inequality, without
a covering average. -/
theorem ambientARSurplus_nonnegative_by_intervals : 0 ≤ S.ambientARSurplus :=
  S.ambientARSurplus_nonnegative_of_interval_nonnegative
    S.standardFormInterval_surplus_nonnegative

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
