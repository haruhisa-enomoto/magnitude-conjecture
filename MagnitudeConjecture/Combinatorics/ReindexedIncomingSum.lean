import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-! # Incoming sums are invariant under finite relabelling -/
set_option autoImplicit false
open scoped BigOperators
namespace MagnitudeConjecture
universe u v

/-- Transport a uniform incoming-weight bound through a bijection of labels. -/
theorem incoming_sum_le_of_equiv {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → α → ℕ) (g : β → β → ℕ)
    (h : ∀ a b, f a b = g (e a) (e b)) (B : ℕ)
    (hB : ∀ b, (∑ a, g a b) ≤ B) (b : α) : (∑ a, f a b) ≤ B := by
  calc
    (∑ a, f a b) = ∑ a, g (e a) (e b) := Finset.sum_congr rfl (fun a _ ↦ h a b)
    _ = ∑ a, g a (e b) := e.sum_comp (fun a ↦ g a (e b))
    _ ≤ B := hB (e b)

end MagnitudeConjecture
