import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

/-! # Uniform weight bounds on a bounded exceptional set -/
set_option autoImplicit false
open scoped BigOperators
namespace MagnitudeConjecture
universe u v

/-- Relabelling a bounded exceptional set preserves a uniform bound on its
total weight. -/
theorem reindexed_subtype_sum_le {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : β → Prop) [DecidablePred P]
    (w : α → ℕ) (B C : ℕ) (hcard : Nat.card {b : β // P b} ≤ C)
    (hw : ∀ a, w a ≤ B) :
    (∑ a : {a : α // P (e a)}, w a.val) ≤ C * B := by
  classical
  have hc : Nat.card {a : α // P (e a)} ≤ C :=
    (Nat.card_congr (Equiv.subtypeEquivOfSubtype e)).trans_le hcard
  calc
    (∑ a : {a : α // P (e a)}, w a.val) ≤ ∑ _a : {a : α // P (e a)}, B :=
      Finset.sum_le_sum (fun a _ ↦ hw a.val)
    _ = Nat.card {a : α // P (e a)} * B := by simp [Nat.card_eq_fintype_card]
    _ ≤ C * B := Nat.mul_le_mul_right B hc

end MagnitudeConjecture
