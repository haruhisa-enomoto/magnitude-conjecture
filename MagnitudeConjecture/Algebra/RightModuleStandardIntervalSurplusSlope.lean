import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSurplusError
import MagnitudeConjecture.Combinatorics.SurplusSlope

/-! # The interval surplus constant and its nonnegative-slope consequence -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance surplusSlopeIntervalFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance surplusSlopeIntervalNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

/-- A fixed bound for all sufficiently long interval surplus errors. -/
def standardFormIntervalSurplusErrorBound : ℤ :=
  2 * |∑ i : Fin S.n, (((S.standardFormSupportWindow i).upper : ℤ) -
    (S.standardFormSupportWindow i).lower)| +
    ((S.standardFormBoundaryArrowBound : ℤ) + 2 * S.standardFormIntervalControlHeight *
      ARCount.arrowCount (FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData))

/-- The error bound is independent of the interval length. -/
theorem standardFormInterval_surplus_error_uniform (m : ℕ)
    (hm : 2 * S.standardFormIntervalControlHeight ≤ m) :
    |(S.standardFormIntervalSkeleton m).ambientARSurplus -
      ((m : ℤ) + 1) * S.ambientARSurplus| ≤ S.standardFormIntervalSurplusErrorBound :=
  S.standardFormInterval_surplus_error_bound m hm

/-- Once the directed interval nonnegativity input is supplied, the interval
slope argument proves the ambient surplus nonnegative. -/
theorem ambientARSurplus_nonnegative_of_interval_nonnegative
    (hpos : ∀ m : ℕ, 0 ≤ (S.standardFormIntervalSkeleton m).ambientARSurplus) :
    0 ≤ S.ambientARSurplus :=
  GradedInterval.ambient_nonnegative_of_interval_absolute_error S.ambientARSurplus
    (fun m ↦ (S.standardFormIntervalSkeleton m).ambientARSurplus)
    S.standardFormIntervalSurplusErrorBound (2 * S.standardFormIntervalControlHeight)
    hpos S.standardFormInterval_surplus_error_uniform

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
