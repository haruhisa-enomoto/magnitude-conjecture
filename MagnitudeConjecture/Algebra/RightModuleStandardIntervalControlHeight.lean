import MagnitudeConjecture.Algebra.RightModuleStandardIntervalShifts

/-! # One height controlling both support and Hom degrees -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- A common height for the interval's support and incoming-Hom estimates. -/
def standardFormIntervalControlHeight : ℕ :=
  max S.standardFormSupportHeight S.standardFormGraded_uniform_bound.choose

theorem standardFormIntervalControlHeight_pos : 1 ≤ S.standardFormIntervalControlHeight :=
  S.standardFormGraded_uniform_bound.choose_spec.1.trans (le_max_right _ _)

theorem standardFormSupportWindow_upper_le_control (i : Fin S.n) :
    (S.standardFormSupportWindow i).upper ≤ S.standardFormIntervalControlHeight :=
  (S.standardFormSupportWindow_upper_le i).trans (le_max_left _ _)

/-- Degrees outside the common height vanish in every mesh Hom space. -/
theorem standardFormIntervalControlHeight_hom_bound
    (X Y : S.StandardFormMeshCategory) (d : ℤ)
    (hd : d < 0 ∨ (S.standardFormIntervalControlHeight : ℤ) < d) :
    S.standardFormIntegerHomGrading.component X Y d = ⊥ := by
  apply S.standardFormGraded_uniform_bound.choose_spec.2 X Y d
  have h : S.standardFormGraded_uniform_bound.choose ≤ S.standardFormIntervalControlHeight :=
    le_max_right _ _
  rcases hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr (by omega)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
