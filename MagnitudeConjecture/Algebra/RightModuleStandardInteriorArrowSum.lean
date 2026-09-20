import MagnitudeConjecture.Algebra.RightModuleStandardInteriorIndegree
import MagnitudeConjecture.Combinatorics.GradedIntervalInteriorSum

/-! # Exact total interior arrow contribution in the supported family -/
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

/-- The supported-family interior arrow sum repeats the ordinary total arrow
multiplicity once for each interior shift. -/
def standardFormSupported_interior_arrowSum (m : ℕ)
    (hm : 2 * S.standardFormIntervalControlHeight ≤ m) :=
  (Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun (b : {b : S.standardFormSupportedLabel m //
      0 ≤ b.2.val ∧ b.2.val ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight}) _ ↦
      S.standardFormSupported_interior_indegree b.val b.property.1 b.property.2)).trans
    (GradedInterval.interior_weighted_sum m S.standardFormIntervalControlHeight
      (fun i ↦ (S.standardFormSupportWindow i).lower)
      (fun i ↦ (S.standardFormSupportWindow i).upper)
      S.standardFormSupportWindow_upper_le_control hm
      (fun j ↦ ∑ i : Fin S.n, FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData i j))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
