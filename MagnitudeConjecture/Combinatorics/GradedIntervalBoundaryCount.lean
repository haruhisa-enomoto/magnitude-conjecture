import Mathlib.Algebra.Order.BigOperators.Group.Finset
import MagnitudeConjecture.Combinatorics.GradedIntervalCount
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.Finite

/-! # Total exceptional targets in a finite family of support windows -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace MagnitudeConjecture.GradedInterval
universe u
variable {ι : Type u} [Fintype ι]

/-- Filtering a finite family of finite sets is equivalent to filtering each fibre. -/
def sigmaFinsetFilterEquiv (F : ι → Finset ℤ) (P : ι → ℤ → Prop)
    [∀ i, DecidablePred (P i)] :
    {a : Σ i, ↥(F i) // P a.1 a.2.val} ≃ Σ i, ↥((F i).filter (P i)) := by
  classical
  exact
    { toFun := fun a ↦ ⟨a.val.1, ⟨a.val.2.val, Finset.mem_filter.mpr ⟨a.val.2.property, a.property⟩⟩⟩
      invFun := fun a ↦ ⟨⟨a.1, ⟨a.2.val, (Finset.mem_filter.mp a.2.property).1⟩⟩,
        (Finset.mem_filter.mp a.2.property).2⟩
      left_inv := fun ⟨⟨i, t, ht⟩, hp⟩ ↦ rfl
      right_inv := fun ⟨i, t, ht⟩ ↦ rfl }

/-- Summing uniform fibre bounds bounds the whole exceptional label set. -/
theorem sigmaFinset_filter_card_le (F : ι → Finset ℤ) (P : ι → ℤ → Prop)
    [∀ i, DecidablePred (P i)] (B : ℕ)
    (hB : ∀ i, ((F i).filter (P i)).card ≤ B) :
    Nat.card {a : Σ i, ↥(F i) // P a.1 a.2.val} ≤ Fintype.card ι * B := by
  classical
  rw [Nat.card_congr (sigmaFinsetFilterEquiv F P), Nat.card_eq_fintype_card, Fintype.card_sigma]
  calc
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum (fun i _ ↦ by simpa using hB i)
    _ = _ := by simp

/-- At most `3h` boundary targets occur for each original label, uniformly in m. -/
theorem total_exceptional_allowedShifts_card_le (m h : ℕ) (l r : ι → ℕ)
    (hl : ∀ i, l i ≤ h) :
    Nat.card {a : Σ i, ↥(allowedShifts m (l i) (r i)) //
      ¬ (0 ≤ a.2.val ∧ a.2.val ≤ (m : ℤ) - 2 * h)} ≤ Fintype.card ι * (3 * h) :=
  sigmaFinset_filter_card_le _ _ (3 * h)
    (fun i ↦ exceptional_allowedShifts_card_le m (l i) (r i) h (hl i))

end MagnitudeConjecture.GradedInterval
