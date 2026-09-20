import MagnitudeConjecture.Combinatorics.GradedIntervalCount
import Mathlib.Data.Finset.Max

/-! # Exact support endpoints and allowed shifts -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.GradedInterval

/-- Natural endpoints of a finite nonnegative support, attained in that support. -/
structure SupportWindow (D : Finset ℤ) where
  lower : ℕ
  upper : ℕ
  lower_mem : (lower : ℤ) ∈ D
  upper_mem : (upper : ℤ) ∈ D
  bounds : ∀ d ∈ D, (lower : ℤ) ≤ d ∧ d ≤ upper

/-- A finite nonempty nonnegative support has exact natural endpoints. -/
def SupportWindow.ofNonnegative (D : Finset ℤ) (hne : D.Nonempty)
    (hpos : ∀ d ∈ D, 0 ≤ d) : SupportWindow D := by
  let l := D.min' hne
  let u := D.max' hne
  have hl : 0 ≤ l := hpos l (Finset.min'_mem D hne)
  have hu : 0 ≤ u := hpos u (Finset.max'_mem D hne)
  have hl' : (l.toNat : ℤ) = l := by omega
  have hu' : (u.toNat : ℤ) = u := by omega
  exact
    { lower := l.toNat
      upper := u.toNat
      lower_mem := by rw [hl']; exact Finset.min'_mem D hne
      upper_mem := by rw [hu']; exact Finset.max'_mem D hne
      bounds := fun d hd ↦ by
        rw [hl', hu']
        exact ⟨Finset.min'_le D d hd, Finset.le_max' D d hd⟩ }

theorem SupportWindow.lower_le_upper {D : Finset ℤ} (W : SupportWindow D) : W.lower ≤ W.upper := by
  have h := (W.bounds W.upper W.upper_mem).1
  exact_mod_cast h

/-- Support containment after a shift is exactly the allowed-shift condition. -/
theorem SupportWindow.shift_supported_iff {D : Finset ℤ} (W : SupportWindow D) (m : ℕ) (t : ℤ) :
    (∀ d ∈ D, 0 ≤ d + t ∧ d + t ≤ m) ↔ t ∈ allowedShifts m W.lower W.upper := by
  rw [mem_allowedShifts]
  constructor
  · intro h
    exact ⟨(h W.lower W.lower_mem).1, (h W.upper W.upper_mem).2⟩
  · intro h d hd
    have hb := W.bounds d hd
    constructor <;> omega

end MagnitudeConjecture.GradedInterval
