import MagnitudeConjecture.Algebra.RightModuleStandardIntervalControlHeight
import MagnitudeConjecture.Algebra.RightModuleStandardSupportedCategory
import MagnitudeConjecture.Combinatorics.GradedIntervalBoundaryCount

/-! # A uniform count of boundary targets in supported intervals -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Targets outside the common interior range for radical-square comparison. -/
def standardFormSupportedBoundaryLabel (m : ℕ) :=
  {b : S.standardFormSupportedLabel m //
    ¬ (0 ≤ b.2.val ∧ b.2.val ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight)}

/-- The number of actual boundary targets is bounded independently of interval length. -/
theorem standardFormSupportedBoundaryLabel_card_le (m : ℕ) :
    Nat.card (S.standardFormSupportedBoundaryLabel m) ≤
      S.n * (3 * S.standardFormIntervalControlHeight) := by
  simpa only [standardFormSupportedBoundaryLabel, Fintype.card_fin] using
    (GradedInterval.total_exceptional_allowedShifts_card_le m S.standardFormIntervalControlHeight
      (fun i ↦ (S.standardFormSupportWindow i).lower)
      (fun i ↦ (S.standardFormSupportWindow i).upper)
      (fun i ↦ (S.standardFormSupportWindow i).lower_le_upper.trans
        (S.standardFormSupportWindow_upper_le_control i)))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
