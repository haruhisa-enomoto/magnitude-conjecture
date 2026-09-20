import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Lean.Elab.Tactic.Omega

/-!
# Extending a nonnegative internal grading to integer degrees

Mesh path lengths are natural numbers, whereas module shifts use integers.
Extending the homogeneous components by zero preserves their internal sum.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.Graded

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M]

/-- The integer-indexed family obtained by inserting zero in negative degrees. -/
def integerComponent (A : ℕ → Submodule k M) (d : ℤ) : Submodule k M :=
  if 0 ≤ d then A d.toNat else ⊥

@[simp]
theorem integerComponent_nat (A : ℕ → Submodule k M) (n : ℕ) :
    integerComponent A (n : ℤ) = A n := by
  simp [integerComponent]

theorem integerComponent_negative (A : ℕ → Submodule k M) (d : ℤ) (hd : d < 0) :
    integerComponent A d = ⊥ := by
  simp [integerComponent, show ¬ 0 ≤ d by omega]

theorem integerComponent_isInternal (A : ℕ → Submodule k M)
    (hA : DirectSum.IsInternal A) : DirectSum.IsInternal (integerComponent A) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro d
    by_cases hd : 0 ≤ d
    · rw [integerComponent, if_pos hd]
      have hi := hA.submodule_iSupIndep
      rw [iSupIndep_def] at hi
      apply (hi d.toNat).mono_right
      apply iSup_le
      intro e
      apply iSup_le
      intro hed
      by_cases he : 0 ≤ e
      · rw [integerComponent, if_pos he]
        exact le_iSup_of_le e.toNat (le_iSup_of_le (by omega : e.toNat ≠ d.toNat) le_rfl)
      · simp [integerComponent, he]
    · simp [integerComponent, hd]
  · apply le_antisymm le_top
    rw [← hA.submodule_iSup_eq_top]
    apply iSup_le
    intro n
    exact le_iSup_of_le (n : ℤ) (by simp)

end MagnitudeConjecture.Graded
