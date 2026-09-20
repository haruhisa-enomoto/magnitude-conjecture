import MagnitudeConjecture.Combinatorics.SeparatedIntervalCoordinates
import MagnitudeConjecture.Combinatorics.GradedIntervalSurplus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # The uniform-error consequence of separated interval packing -/
set_option autoImplicit false
namespace MagnitudeConjecture.GradedInterval

/-- A uniform linear error and separated packing bound every interval by
its separation length times the ambient surplus. -/
theorem interval_le_length_mul_of_separated_packing
    (σ : ℤ) (interval : ℕ → ℤ) (C : ℤ) (h : ℕ)
    (hupper : ∀ m, 2 * h ≤ m → |interval m - ((m : ℤ) + 1) * σ| ≤ C)
    (hpack : ∀ r q : ℕ, (q : ℤ) * interval r ≤ interval (packingEnd r h q)) (r : ℕ) :
    interval r ≤ ((r : ℤ) + h + 1) * σ := by
  have hlimit := interval_le_length_mul_of_packing σ (interval r) (r + h + 1)
    (C - (h : ℤ) * σ) (2 * h + 2) (by
      intro q hq
      have hlarge : 2 * h ≤ packingEnd r h q := by
        have hmul : q - 1 ≤ (q - 1) * (r + h + 1) := Nat.le_mul_of_pos_right _ (by omega)
        dsimp only [packingEnd]
        omega
      have hp := hpack r q
      have hu := (abs_le.mp (hupper (packingEnd r h q) hlarge)).2
      have hqm : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
      have hm : ((packingEnd r h q : ℕ) : ℤ) + 1 =
          (q : ℤ) * ((r : ℤ) + h + 1) - h := by
        simp only [packingEnd, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        rw [hqm]
        ring
      rw [hm] at hu
      push_cast
      nlinarith)
  simpa only [Nat.cast_add, Nat.cast_one] using hlimit

end MagnitudeConjecture.GradedInterval
