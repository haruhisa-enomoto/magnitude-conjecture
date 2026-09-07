import MagnitudeConjecture.Algebra.RightModuleStandardFormARIncomingFactors
import MagnitudeConjecture.Algebra.RightModuleStandardFormARIncomingNonsplit
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteAlmostSplit

/-!
# The recovered incoming map is right almost split
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The complete recovered incoming mesh is right almost split. -/
theorem standardFormRecoveredIncomingMap_rightAlmostSplit
    (z : Fin S.n) :
    IsRightAlmostSplit (S.standardFormRecoveredIncomingMap (k := k) z) := by
  let sigma := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
    (k := k)
  apply sigma.isRightAlmostSplit_of_factors_obj
  · exact S.standardFormRecoveredIncomingMap_not_splitEpi (k := k) z
  · intro x q hq
    exact S.standardFormRecoveredIncomingMap_factors_obj (k := k) x z q hq

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
