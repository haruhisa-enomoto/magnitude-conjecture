import MagnitudeConjecture.Combinatorics.GradedIntervalSurplus

/-! # A nonnegative family with bounded surplus error has nonnegative slope -/
set_option autoImplicit false
namespace MagnitudeConjecture.GradedInterval

/-- An eventual uniform absolute error and interval nonnegativity force a
nonnegative ambient surplus. -/
theorem ambient_nonnegative_of_interval_absolute_error
    (s : ℤ) (f : ℕ → ℤ) (C : ℤ) (m₀ : ℕ)
    (hpos : ∀ m, 0 ≤ f m)
    (herr : ∀ m, m₀ ≤ m → |f m - ((m : ℤ) + 1) * s| ≤ C) : 0 ≤ s := by
  apply ambient_nonnegative_of_interval_bound s f C m₀ hpos
  intro m hm
  have h := (abs_le.mp (herr m hm)).2
  linarith

end MagnitudeConjecture.GradedInterval
