import Mathlib.LinearAlgebra.Pi

/-! # Summing a single coordinate in a family of submodules -/

set_option autoImplicit false

namespace Submodule

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [Fintype ι] [DecidableEq ι]

/-- The ambient sum of a family supported in one submodule is its nonzero
coordinate. -/
theorem sum_coe_single (p : ι → Submodule R M) (i : ι) (x : p i) :
    (∑ j, ((Pi.single i x : ∀ j, p j) j : M)) = (x : M) := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji]
    rfl
  · simp

end Submodule
