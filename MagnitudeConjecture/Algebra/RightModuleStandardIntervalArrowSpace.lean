import MagnitudeConjecture.Algebra.RightModuleStandardIntervalIrreducible
import MagnitudeConjecture.Algebra.RightModuleArrowMultiplicityEquivalence

/-! # Interval arrow multiplicities in the supported graded category -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
attribute [local irreducible] standardFormIntervalAlgebraEquivalence
local instance intervalArrowFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance intervalArrowNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- For any complete interval-algebra skeleton, the official arrow count is
the intrinsic quotient dimension of its images in supported graded modules. -/
def standardFormInterval_arrowMultiplicity_eq_irreducible_finrank (m : ℕ)
    (T : RightModule.FiniteIndecomposableSkeleton k (S.standardFormIntervalAlgebra m))
    (source target : Fin T.n) :=
  T.arrowMultiplicity_eq_irreducible_finrank_of_equivalence
    (S.standardFormIntervalAlgebraEquivalence m) source target

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
