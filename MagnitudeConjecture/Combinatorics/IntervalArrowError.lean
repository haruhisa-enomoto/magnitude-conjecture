import MagnitudeConjecture.Combinatorics.EulerSurplus

/-! # A uniform arrow error from exact interior and bounded boundary sums -/
set_option autoImplicit false
open scoped BigOperators
namespace MagnitudeConjecture.GradedInterval
universe u v

/-- The exact interior contribution and a bounded exceptional contribution
control the error from the full interval-length multiple. -/
theorem arrow_error_bound_from_partition {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] (f : α → α → ℕ) (g : β → β → ℕ)
    (P : α → Prop) [DecidablePred P] (m h B : ℕ) (hm : 2 * h ≤ m)
    (hi : (∑ b : {b : α // P b}, ∑ a : α, f a b.val) =
      (m - 2 * h + 1) * ∑ b : β, ∑ a : β, g a b)
    (hb : (∑ b : {b : α // ¬ P b}, ∑ a : α, f a b.val) ≤ B) :
    |ARCount.arrowCount f - ((m : ℤ) + 1) * ARCount.arrowCount g| ≤
      (B : ℤ) + 2 * h * ARCount.arrowCount g := by
  classical
  have hpart := Fintype.sum_subtype_add_sum_subtype P (fun b ↦ ∑ a : α, f a b)
  rw [hi] at hpart
  have hz := congrArg (fun n : ℕ ↦ (n : ℤ)) hpart
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hm, Nat.cast_ofNat,
    Nat.cast_one] at hz
  have hbz : (((∑ b : {b : α // ¬ P b}, ∑ a : α, f a b.val) : ℕ) : ℤ) ≤ B :=
    by exact_mod_cast hb
  have hbn := Nat.cast_nonneg (α := ℤ) (∑ b : {b : α // ¬ P b}, ∑ a : α, f a b.val)
  have hgn := Nat.cast_nonneg (α := ℤ) (∑ b : β, ∑ a : β, g a b)
  have hhn := Nat.cast_nonneg (α := ℤ) h
  have hBn := Nat.cast_nonneg (α := ℤ) B
  have hf : ARCount.arrowCount f = ((∑ b : α, ∑ a : α, f a b) : ℕ) := by
    simp only [ARCount.arrowCount, Nat.cast_sum]
    exact Finset.sum_comm
  have hg : ARCount.arrowCount g = ((∑ b : β, ∑ a : β, g a b) : ℕ) := by
    simp only [ARCount.arrowCount, Nat.cast_sum]
    exact Finset.sum_comm
  rw [hf, hg, abs_le]
  constructor <;> nlinarith

end MagnitudeConjecture.GradedInterval
