import MagnitudeConjecture.Algebra.RightModuleStandardIntervalInteriorArrowSum
import MagnitudeConjecture.Algebra.RightModuleStandardBoundaryArrowSum
import MagnitudeConjecture.Combinatorics.IntervalArrowError

/-! # Uniform arrow-count error for the actual finite interval algebras -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The actual interval arrow count differs from (m+1) times the ordinary
arrow count by a constant independent of m. -/
def standardFormInterval_arrow_error_bound (m : ℕ)
    (hm : 2 * S.standardFormIntervalControlHeight ≤ m) :=
  GradedInterval.arrow_error_bound_from_partition _
    (FiniteTauMatrix.arrowMultiplicity S.finiteTauCategoryData.toFiniteRightTauCategoryData)
    (fun j : Fin (S.standardFormIntervalSkeleton m).n ↦
      0 ≤ (S.standardFormIntervalLabelEquiv m j).2.val ∧
        (S.standardFormIntervalLabelEquiv m j).2.val ≤
          (m : ℤ) - 2 * S.standardFormIntervalControlHeight)
    m S.standardFormIntervalControlHeight S.standardFormBoundaryArrowBound hm
    (S.standardFormIntervalSkeleton_interior_arrowSum m hm)
    (S.standardFormInterval_boundaryArrowSum_le m)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
