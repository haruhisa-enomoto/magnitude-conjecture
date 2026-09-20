import MagnitudeConjecture.Algebra.RightModuleStandardIntervalBetaTransfer
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalBiserial
import MagnitudeConjecture.Algebra.RepresentationFiniteSpecialBiserialBeta

/-! # The global equality implication through a single graded interval -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : FiniteIndecomposableSkeleton k A)

/-- Zero ambient surplus bounds the original nonprojective middle count by
two through the interval of length given by the control height plus two. -/
theorem beta_le_two_of_ambientARSurplus_eq_zero_by_intervals
    (hz : S.ambientARSurplus = 0) :
    FiniteTauMatrix.beta S.finiteTauCategoryData.toFiniteRightTauCategoryData ≤ 2 := by
  let m := S.standardFormIntervalControlHeight + 2
  letI : FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
    S.standardFormIntervalAlgebra_finiteDimensional m
  letI : IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  exact le_trans S.beta_le_standardFormInterval_beta
    (specialBiserial_beta_le_two (S.standardFormIntervalSkeleton m)
      (S.standardFormIntervalAlgebra_isSpecialBiserial_of_ambient_eq_zero hz m))

/-- The manuscript's global equality implication, using finite intervals,
separated packing, and the one-sided almost-split transfer. -/
theorem isSpecialBiserial_of_ambientARSurplus_eq_zero_by_intervals
    (hz : S.ambientARSurplus = 0) : BoundQuiver.IsSpecialBiserial k A :=
  S.isSpecialBiserial_of_beta_le_two
    (S.beta_le_two_of_ambientARSurplus_eq_zero_by_intervals hz)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
