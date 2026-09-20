import MagnitudeConjecture.Algebra.RightModuleStandardSupportedIncomingBounds
import MagnitudeConjecture.Combinatorics.FiniteShiftWindow

/-! # A uniform count of incoming indecomposable sources -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Labels admitting a nonzero map to a fixed supported representative. -/
abbrev standardFormSupportedIncomingLabel {m : ℕ} (b : S.standardFormSupportedLabel m) :=
  {a : S.standardFormSupportedLabel m //
    ∃ f : S.standardFormSupportedFamily m a ⟶ S.standardFormSupportedFamily m b, f ≠ 0}

/-- At most h + 1 shifts of each original indecomposable can map to a fixed
interval target. This includes targets at either boundary. -/
theorem standardFormSupportedIncomingLabel_card_le
    (h : ℕ) (hb : ∀ X Y : S.StandardFormMeshCategory, ∀ d : ℤ,
      d < 0 ∨ (h : ℤ) < d → S.standardFormIntegerHomGrading.component X Y d = ⊥)
    {m : ℕ} (b : S.standardFormSupportedLabel m) :
    Nat.card (S.standardFormSupportedIncomingLabel b) ≤ S.n * (h + 1) := by
  classical
  letI : Fintype (S.standardFormSupportedIncomingLabel b) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  have hw (a : S.standardFormSupportedIncomingLabel b) :
      b.2.val ≤ a.val.2.val ∧ a.val.2.val ≤ b.2.val + h :=
    a.property.elim (fun f hf ↦
      S.standardFormSupported_incoming_shift_bounds h hb a.val b f hf)
  have hc := GradedInterval.card_le_of_label_shift_window
    (fun a : S.standardFormSupportedIncomingLabel b ↦ a.val.1)
    (fun a : S.standardFormSupportedIncomingLabel b ↦ a.val.2.val)
    (by
      intro a c hac
      apply Subtype.ext
      exact GradedInterval.sigmaFinset_label_shift_injective
        (fun i ↦ GradedInterval.allowedShifts m (S.standardFormSupportWindow i).lower
          (S.standardFormSupportWindow i).upper) hac)
    b.2.val h hw
  simpa only [Fintype.card_fin] using hc

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
