import Mathlib.Data.Int.Basic

/-! # A dimension function supported in degree one -/
set_option autoImplicit false
namespace MagnitudeConjecture

/-- Three degree ranges determine a dimension function supported on adjacent shifts. -/
theorem degreeOne_function_formula (q : ℤ → ℤ → ℕ) (D : ℕ)
    (hone : ∀ t, q (t + 1) t = D)
    (hlow : ∀ s t, s ≤ t → q s t = 0)
    (hhigh : ∀ t (n : ℕ), 0 < n → q (t + n + 1) t = 0)
    (s t : ℤ) : q s t = if s = t + 1 then D else 0 := by
  by_cases h : s = t + 1
  · subst s
    simpa using hone t
  · rw [if_neg h]
    by_cases hst : s ≤ t
    · exact hlow s t hst
    · obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, 0 < n ∧ s = t + n + 1 := by
        refine ⟨(s - t - 1).toNat, ?_, ?_⟩ <;> omega
      exact hhigh t n hn

end MagnitudeConjecture
