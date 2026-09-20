import MagnitudeConjecture.Algebra.RightModuleStandardIntervalArrowError
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSimpleCount
import MagnitudeConjecture.Algebra.RightModuleSurplusCounts

/-! # Uniform surplus error for the actual finite interval algebras -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
attribute [local irreducible] standardFormIntervalAlgebraEquivalence
local instance surplusIntervalFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance surplusIntervalNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

/-- The official interval surplus has the ambient surplus as its linear slope,
with an error bounded independently of interval length. -/
def standardFormInterval_surplus_error_bound (m : ℕ)
    (hm : 2 * S.standardFormIntervalControlHeight ≤ m) :=
  S.ambientARSurplus_error_of_counts (S.standardFormIntervalSkeleton m) m _ _
    (S.standardFormIntervalSkeleton_card m (by
      have h : S.standardFormSupportHeight ≤ S.standardFormIntervalControlHeight :=
        le_max_left _ _
      omega))
    (S.standardFormInterval_arrow_error_bound m hm)
    (S.standardFormIntervalSkeleton_simpleCount m)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
