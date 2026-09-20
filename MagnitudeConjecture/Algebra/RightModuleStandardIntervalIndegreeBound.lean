import MagnitudeConjecture.Algebra.RightModuleStandardIntervalNumberedArrows
import MagnitudeConjecture.Algebra.RightModuleStandardSupportedIndegreeBound
import MagnitudeConjecture.Combinatorics.ReindexedIncomingSum

/-! # Uniform indegree bounds for the actual interval algebra -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra BigOperators
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
attribute [local irreducible] standardFormIntervalAlgebraEquivalence
local instance intervalIndegreeFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance intervalIndegreeNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- A single bound for all interval lengths and all targets. -/
def standardFormIntervalIndegreeBound : ℕ :=
  S.standardFormSupported_uniform_indegree_bound.choose

/-- Total official arrow multiplicity into each interval vertex is uniformly
bounded, including at the two boundaries. -/
def standardFormIntervalSkeleton_indegree_le (m : ℕ)
    (j : Fin (S.standardFormIntervalSkeleton m).n) :=
  incoming_sum_le_of_equiv (S.standardFormIntervalLabelEquiv m)
    _ _
    (S.standardFormIntervalSkeleton_arrowMultiplicity_eq m)
    S.standardFormIntervalIndegreeBound
    (S.standardFormSupported_uniform_indegree_bound.choose_spec m) j

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
