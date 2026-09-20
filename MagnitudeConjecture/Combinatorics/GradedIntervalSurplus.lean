import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# Surplus bounds for finite graded intervals

The integer surplus of an interval has a linear main term and a uniformly
bounded error. These lemmas implement the limiting arguments in the frozen
September 20 manuscript using integer inequalities. The categorical interval
construction and its counting estimates must supply their hypotheses.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.GradedInterval

/-- Object and arrow error bounds give the surplus error bound when the
number of simple modules scales exactly. Surplus is `2N-a-2p`. -/
theorem surplus_error_bound
    (N a p Nₘ aₘ pₘ c Cₙ Cₐ : ℤ)
    (hN : |Nₘ - c * N| ≤ Cₙ) (ha : |aₘ - c * a| ≤ Cₐ)
    (hp : pₘ = c * p) :
    |(2 * Nₘ - aₘ - 2 * pₘ) - c * (2 * N - a - 2 * p)| ≤
      2 * Cₙ + Cₐ := by
  obtain ⟨hNlo, hNhi⟩ := abs_le.mp hN
  obtain ⟨halo, hahi⟩ := abs_le.mp ha
  rw [abs_le]
  constructor <;> nlinarith

/-- An eventually bounded sequence of integer multiples has nonpositive slope. -/
theorem slope_nonpositive_of_eventually_bounded
    (s C : ℤ) (n₀ : ℕ)
    (h : ∀ n : ℕ, n₀ ≤ n → (n : ℤ) * s ≤ C) : s ≤ 0 := by
  by_contra hs
  have hs' : 1 ≤ s := by omega
  let n := n₀ + C.natAbs + 1
  have hn : n₀ ≤ n := by dsimp [n]; omega
  have habs : C ≤ (C.natAbs : ℤ) := Int.le_natAbs
  have hnC : C < (n : ℤ) := by dsimp [n]; omega
  have hmul := mul_nonneg (Int.natCast_nonneg n) (sub_nonneg.mpr hs')
  have hb := h n hn
  nlinarith

/-- Nonnegative interval surpluses with a uniform upper error force the
ambient surplus to be nonnegative. -/
theorem ambient_nonnegative_of_interval_bound
    (σ : ℤ) (interval : ℕ → ℤ) (C : ℤ) (m₀ : ℕ)
    (hnonneg : ∀ m, 0 ≤ interval m)
    (hupper : ∀ m, m₀ ≤ m → interval m ≤ ((m : ℤ) + 1) * σ + C) :
    0 ≤ σ := by
  have h : -σ ≤ 0 := slope_nonpositive_of_eventually_bounded (-σ) (σ + C) m₀
    (by
      intro m hm
      have hp := hnonneg m
      have hu := hupper m hm
      nlinarith)
  omega

/-- Packing arbitrarily many separated copies bounds each interval surplus
by the separation length times the ambient surplus. The constant absorbs
both the fixed end correction and the uniform counting error. -/
theorem interval_le_length_mul_of_packing
    (σ δ : ℤ) (ℓ : ℕ) (C : ℤ) (q₀ : ℕ)
    (hpacking : ∀ q : ℕ, q₀ ≤ q →
      (q : ℤ) * δ ≤ (q : ℤ) * (ℓ : ℤ) * σ + C) :
    δ ≤ (ℓ : ℤ) * σ := by
  have h : δ - (ℓ : ℤ) * σ ≤ 0 :=
    slope_nonpositive_of_eventually_bounded (δ - (ℓ : ℤ) * σ) C q₀
      (by
        intro q hq
        have hp := hpacking q hq
        nlinarith)
  omega

/-- At zero ambient surplus, packing and directed nonnegativity force every
finite interval surplus to vanish. -/
theorem interval_eq_zero_of_packing
    (δ : ℤ) (C : ℤ) (q₀ : ℕ) (hnonneg : 0 ≤ δ)
    (hpacking : ∀ q : ℕ, q₀ ≤ q → (q : ℤ) * δ ≤ C) : δ = 0 := by
  exact le_antisymm (slope_nonpositive_of_eventually_bounded δ C q₀ hpacking) hnonneg

end MagnitudeConjecture.GradedInterval
