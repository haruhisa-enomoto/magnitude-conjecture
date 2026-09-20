import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-! # Counting distinct labels with shifts in a bounded window -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.GradedInterval

/-- Forgetting membership proofs preserves distinct finite-label shifts. -/
theorem sigmaFinset_label_shift_injective {ι : Type*} (F : ι → Finset ℤ) :
    Function.Injective (fun a : (i : ι) × ↥(F i) ↦ (a.1, a.2.val)) := by
  intro a b hab
  have hi := congrArg Prod.fst hab
  have hs := congrArg Prod.snd hab
  rcases a with ⟨i, s, hsi⟩
  rcases b with ⟨j, t, htj⟩
  dsimp at hi hs
  subst j
  subst t
  rfl

/-- A family uniquely determined by a finite label and an integer shift has
at most `card ι * (h + 1)` members in a window of width h. -/
theorem card_le_of_label_shift_window
    {ι α : Type*} [Fintype ι] [Fintype α]
    (label : α → ι) (shift : α → ℤ)
    (hinj : Function.Injective fun a ↦ (label a, shift a))
    (t : ℤ) (h : ℕ) (hwindow : ∀ a, t ≤ shift a ∧ shift a ≤ t + h) :
    Fintype.card α ≤ Fintype.card ι * (h + 1) := by
  let f : α → ι × Fin (h + 1) := fun a ↦
    (label a, ⟨(shift a - t).toNat, by have := hwindow a; omega⟩)
  have hf : Function.Injective f := by
    intro a b hab
    apply hinj
    apply Prod.ext
    · change label a = label b
      exact congrArg (fun x : ι × Fin (h + 1) ↦ x.1) hab
    · change shift a = shift b
      have hs := congrArg (fun x : ι × Fin (h + 1) ↦ x.2.val) hab
      change (shift a - t).toNat = (shift b - t).toNat at hs
      have ha := hwindow a
      have hb := hwindow b
      omega
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_le_of_injective f hf

end MagnitudeConjecture.GradedInterval
