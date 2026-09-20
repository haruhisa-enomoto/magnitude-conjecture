import MagnitudeConjecture.Algebra.RightModuleStandardInteriorArrowDimension
import MagnitudeConjecture.Combinatorics.SupportedShiftSum

/-! # Interior incoming sums equal the ordinary indegree -/
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

/-- The incoming irreducible sum at an interior supported target is exactly
its ordinary skeleton indegree. -/
def standardFormSupported_interior_indegree {m : ℕ}
    (b : S.standardFormSupportedLabel m) (ht0 : 0 ≤ b.2.val)
    (htm : b.2.val ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight) :=
  sum_eq_of_supported_single_shift
    (fun i : Fin S.n ↦ GradedInterval.allowedShifts m
      (S.standardFormSupportWindow i).lower (S.standardFormSupportWindow i).upper)
    (b.2.val + 1) (S.standardFormSupported_interior_nextShift b ht0 htm)
    (fun i ↦ FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData i b.1)
    (fun a ↦ Module.finrank k (CategoricalIrreducible.Space k
      (S.standardFormSupportedFamily m a) (S.standardFormSupportedFamily m b)))
    (fun a ↦ S.standardFormSupported_interior_arrowDimension a b ht0 htm)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
