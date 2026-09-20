import MagnitudeConjecture.Algebra.RightModuleStandardBoundaryCount
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalIndegreeBound
import MagnitudeConjecture.Combinatorics.ReindexedBoundarySum

/-! # Uniform total arrow contribution at interval boundaries -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped BigOperators
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- A constant bounding the entire exceptional-target arrow contribution. -/
def standardFormBoundaryArrowBound : ℕ :=
  (S.n * (3 * S.standardFormIntervalControlHeight)) * S.standardFormIntervalIndegreeBound

/-- The sum of actual interval arrow multiplicities into all boundary targets
is bounded by a constant independent of the interval length. -/
def standardFormInterval_boundaryArrowSum_le (m : ℕ) :=
  reindexed_subtype_sum_le (S.standardFormIntervalLabelEquiv m)
    (fun b ↦ ¬ (0 ≤ b.2.val ∧ b.2.val ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight))
    _ S.standardFormIntervalIndegreeBound (S.n * (3 * S.standardFormIntervalControlHeight))
    (S.standardFormSupportedBoundaryLabel_card_le m)
    (S.standardFormIntervalSkeleton_indegree_le m)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
