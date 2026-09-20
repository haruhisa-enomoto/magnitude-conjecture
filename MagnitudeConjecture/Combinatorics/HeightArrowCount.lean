import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! # Counting arrows by weighted height differences -/
set_option autoImplicit false
namespace MagnitudeConjecture.HeightArrowCount
universe u
variable {V : Type u} [Fintype V]

/-- Each arrow contributes one to the difference of incoming and outgoing
height-weighted sums. Multiplicities are retained. -/
theorem weighted_difference (a : V → V → ℤ) (h : V → ℤ)
    (ha : ∀ x y, a x y ≠ 0 → h y = h x + 1) :
    (∑ x, ∑ y, a x y) =
      (∑ y, h y * ∑ x, a x y) - (∑ x, h x * ∑ y, a x y) := by
  have he : ∀ x y, a x y = h y * a x y - h x * a x y := by
    intro x y
    by_cases hz : a x y = 0
    · simp [hz]
    · rw [ha x y hz]
      ring
  calc
    (∑ x, ∑ y, a x y) = ∑ x, ∑ y, (h y * a x y - h x * a x y) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_congr rfl (fun y _ ↦ he x y)
    _ = (∑ x, ∑ y, h y * a x y) - (∑ x, ∑ y, h x * a x y) := by
      simp only [Finset.sum_sub_distrib]
    _ = (∑ y, h y * ∑ x, a x y) - (∑ x, h x * ∑ y, a x y) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

/-- Solving the weighted-height balance gives the arrow count and excess.
Here A is the arrow count, N the vertex count, p the projective count,
and L the sink height. -/
theorem count_of_balance (A N p L Hp Hm outside : ℤ)
    (hheight : Hm - Hp = 2 * (N - p))
    (hout : outside = A - p + 1)
    (hbalance : A = 2 * outside + Hp - Hm + L) :
    A = 2 * N - L - 2 ∧ 2 * N - A - p - 1 = L - (p - 1) := by
  constructor <;> omega

end MagnitudeConjecture.HeightArrowCount
