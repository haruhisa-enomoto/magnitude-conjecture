import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Separated degree intervals -/
set_option autoImplicit false
namespace MagnitudeConjecture.GradedInterval

/-- Membership in the j-th retained interval, with h omitted degrees between
successive intervals of length r+1. -/
def InBlock (r h j : ℕ) (d : ℤ) : Prop :=
  (j : ℤ) * ((r : ℤ) + h + 1) ≤ d ∧
    d ≤ (j : ℤ) * ((r : ℤ) + h + 1) + r

/-- Degrees in different retained blocks differ by more than the Hom bound. -/
theorem block_gap (r h : ℕ) {i j : ℕ} {x y : ℤ}
    (hij : i < j) (hx : InBlock r h i x) (hy : InBlock r h j y) :
    (h : ℤ) < y - x := by
  have hi : (i : ℤ) + 1 ≤ j := by exact_mod_cast hij
  have hm := mul_le_mul_of_nonneg_right hi
    (show 0 ≤ (r : ℤ) + h + 1 by positivity)
  obtain ⟨_, hx⟩ := hx
  obtain ⟨hy, _⟩ := hy
  nlinarith

/-- A nonzero Hom degree can connect only one retained block. -/
theorem block_index_eq_of_close (r h : ℕ) {i j : ℕ} {x y : ℤ}
    (hx : InBlock r h i x) (hy : InBlock r h j y)
    (hclose : |y - x| ≤ h) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have hg := block_gap r h hij hx hy
    have hb := (abs_le.mp hclose).2
    omega
  · exact hij
  · have hg := block_gap r h hij hy hx
    have hb := (abs_le.mp hclose).1
    omega

/-- Intermediate degrees between two degrees of a retained block stay in
that block. -/
theorem inBlock_of_between (r h j : ℕ) {x y z : ℤ}
    (hx : InBlock r h j x) (hy : InBlock r h j y)
    (hxz : x ≤ z) (hzy : z ≤ y) : InBlock r h j z :=
  ⟨hx.1.trans hxz, hzy.trans hy.2⟩

/-- The retained degrees for q separated copies of [0,r]. -/
def Retained (r h q : ℕ) (d : ℤ) : Prop := ∃ j < q, InBlock r h j d

/-- A degree between close retained endpoints is retained. -/
theorem retained_of_between_close (r h q : ℕ) {x y z : ℤ}
    (hx : Retained r h q x) (hy : Retained r h q y)
    (hclose : |y - x| ≤ h) (hxz : x ≤ z) (hzy : z ≤ y) :
    Retained r h q z := by
  obtain ⟨i, hi, hx⟩ := hx
  obtain ⟨j, hj, hy⟩ := hy
  have he := block_index_eq_of_close r h hx hy hclose
  subst j
  exact ⟨i, hi, inBlock_of_between r h i hx hy hxz hzy⟩

end MagnitudeConjecture.GradedInterval
