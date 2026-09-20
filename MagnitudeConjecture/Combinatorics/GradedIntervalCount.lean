import MagnitudeConjecture.Combinatorics.GradedIntervalSurplus
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counting shifts supported in a finite interval

If an indecomposable graded module has least and greatest nonzero degrees
`l` and `u`, its shift by `t` belongs to `[0,m]` exactly when
`-l ≤ t ≤ m-u`. This file counts those shifts and bounds the exceptional
target shifts outside the interior used for the arrow count.
-/

set_option autoImplicit false

open scoped BigOperators

namespace MagnitudeConjecture.GradedInterval

/-- Shifts whose support endpoints lie in the interval `[0,m]`. -/
def allowedShifts (m l u : ℕ) : Finset ℤ :=
  Finset.Icc (-(l : ℤ)) ((m : ℤ) - u)

theorem mem_allowedShifts (m l u : ℕ) (t : ℤ) :
    t ∈ allowedShifts m l u ↔ 0 ≤ (l : ℤ) + t ∧ (u : ℤ) + t ≤ m := by
  simp only [allowedShifts, Finset.mem_Icc]
  omega

/-- Once the interval contains the unshifted support, its exact shift count
is its length minus the support width. -/
theorem card_allowedShifts (m l u : ℕ) (hum : u ≤ m) :
    ((allowedShifts m l u).card : ℤ) = (m : ℤ) + 1 - ((u : ℤ) - l) := by
  rw [allowedShifts, Int.card_Icc_of_le
    (a := -(l : ℤ)) (b := (m : ℤ) - u) (by omega)]
  omega

/-- Summing the individual counts gives a constant total width correction. -/
theorem sum_card_allowedShifts {ι : Type*} (s : Finset ι)
    (l u : ι → ℕ) (m : ℕ)
    (hum : ∀ x ∈ s, u x ≤ m) :
    ∑ x ∈ s, ((allowedShifts m (l x) (u x)).card : ℤ) =
      (s.card : ℤ) * ((m : ℤ) + 1) - ∑ x ∈ s, ((u x : ℤ) - l x) := by
  calc
    _ = ∑ x ∈ s, ((m : ℤ) + 1 - ((u x : ℤ) - l x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact card_allowedShifts m (l x) (u x) (hum x hx)
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp

/-- All allowed shifts lie in the larger interval `[-h,m]`. -/
theorem allowedShifts_subset (m l u h : ℕ) (hlh : l ≤ h) :
    allowedShifts m l u ⊆ Finset.Icc (-(h : ℤ)) (m : ℤ) := by
  intro t ht
  simp only [allowedShifts, Finset.mem_Icc] at ht ⊢
  omega

/-- Interior targets contain all incoming supports with shift difference
between zero and `h`, provided the original supports lie in `[0,h]`. -/
theorem incoming_shift_allowed (m h l u : ℕ) (huh : u ≤ h)
    (s t : ℤ) (ht0 : 0 ≤ t) (htm : t ≤ (m : ℤ) - 2 * h)
    (hst : t ≤ s) (hsth : s ≤ t + h) :
    s ∈ allowedShifts m l u := by
  rw [mem_allowedShifts]
  constructor <;> omega

/-- Exceptional target shifts occur in two strips, whose total length is
`3h`; no assertion about preservation of irreducibles at these ends is used. -/
theorem exceptional_shift_mem (m h : ℕ) (t : ℤ)
    (ht : t ∈ Finset.Icc (-(h : ℤ)) (m : ℤ))
    (hout : ¬ (0 ≤ t ∧ t ≤ (m : ℤ) - 2 * h)) :
    t ∈ Finset.Ico (-(h : ℤ)) 0 ∪
      Finset.Ioc ((m : ℤ) - 2 * h) (m : ℤ) := by
  simp only [Finset.mem_Icc] at ht
  simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioc]
  omega

/-- The two boundary strips have uniformly bounded total cardinality, even
when the interval is too short for the strips to be disjoint. -/
theorem boundary_strip_card_le (m h : ℕ) :
    (Finset.Ico (-(h : ℤ)) 0 ∪
      Finset.Ioc ((m : ℤ) - 2 * h) (m : ℤ)).card ≤ 3 * h := by
  have hcard := Finset.card_union_le
    (Finset.Ico (-(h : ℤ)) 0)
    (Finset.Ioc ((m : ℤ) - 2 * h) (m : ℤ))
  have hleft : (Finset.Ico (-(h : ℤ)) 0).card = h := by
    rw [Int.card_Ico]
    simp
  have hright : (Finset.Ioc ((m : ℤ) - 2 * h) (m : ℤ)).card = 2 * h := by
    rw [Int.card_Ioc]
    have heq : (m : ℤ) - ((m : ℤ) - 2 * h) = (2 * h : ℕ) := by omega
    rw [heq]
    exact Int.toNat_natCast (2 * h)
  rw [hleft, hright] at hcard
  omega

/-- Each indecomposable label has at most `3h` exceptional target shifts. -/
theorem exceptional_allowedShifts_card_le (m l u h : ℕ) (hlh : l ≤ h) :
    ((allowedShifts m l u).filter
      (fun t ↦ ¬ (0 ≤ t ∧ t ≤ (m : ℤ) - 2 * h))).card ≤ 3 * h := by
  apply le_trans (Finset.card_le_card ?_) (boundary_strip_card_le m h)
  intro t ht
  obtain ⟨ht, hout⟩ := Finset.mem_filter.mp ht
  exact exceptional_shift_mem m h t (allowedShifts_subset m l u h hlh ht) hout

end MagnitudeConjecture.GradedInterval
