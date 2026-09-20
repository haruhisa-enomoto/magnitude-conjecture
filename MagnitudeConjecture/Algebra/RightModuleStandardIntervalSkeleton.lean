import MagnitudeConjecture.Algebra.RightModuleStandardIntervalClassification
import MagnitudeConjecture.Algebra.RightModuleSkeletonOfFGFamily

/-! # The exact indecomposable count for the actual finite interval algebra -/
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

local instance standardIntervalSkeletonFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) := S.standardFormIntervalAlgebra_finiteDimensional m
local instance standardIntervalSkeletonNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

/-- The exact finite right-module skeleton of the interval algebra. -/
def standardFormIntervalSkeleton (m : ℕ) :
    RightModule.FiniteIndecomposableSkeleton k (S.standardFormIntervalAlgebra m) :=
  ofFGFamily (S.standardFormIntervalFamily m)
    (S.standardFormIntervalFamily_indecomposable m)
    (S.standardFormIntervalFamily_complete m)
    (fun a b h ↦ h.elim (S.standardFormIntervalFamily_skeletal m a b))

/-- The count of actual interval indecomposables has the fixed support-width correction. -/
theorem standardFormIntervalSkeleton_card (m : ℕ) (hm : S.standardFormSupportHeight ≤ m) :
    ((S.standardFormIntervalSkeleton m).n : ℤ) =
      (S.n : ℤ) * ((m : ℤ) + 1) -
        ∑ i : Fin S.n, (((S.standardFormSupportWindow i).upper : ℤ) -
          (S.standardFormSupportWindow i).lower) :=
  S.standardFormSupportedLabel_card m hm

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
