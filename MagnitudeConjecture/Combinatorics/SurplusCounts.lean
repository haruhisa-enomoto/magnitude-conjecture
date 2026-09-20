import MagnitudeConjecture.Combinatorics.EulerSurplus
import MagnitudeConjecture.Combinatorics.GradedIntervalSurplus

/-! # Surplus in terms of vertex, arrow and projective counts -/
set_option autoImplicit false
namespace MagnitudeConjecture.ARCount
universe u
variable {ι : Type u} [Fintype ι]

/-- The surplus is twice the vertex count, less arrows and twice the
projective count. -/
theorem surplus_eq_counts (a : ι → ι → ℕ) (P : ι → Prop) [DecidablePred P] :
    surplus a P = 2 * vertexCount (ι := ι) - arrowCount a - 2 * projectiveCount P := by
  rw [surplus_eq_two_mul_meshCount_sub_arrowCount,
    vertexCount_eq_projectiveCount_add_meshCount P]
  ring

end MagnitudeConjecture.ARCount

namespace MagnitudeConjecture.GradedInterval

/-- Exact object and simple counts together with the arrow error give the
surplus error, with a fixed support-width correction. -/
theorem surplus_error_of_exact_counts
    (N Nm p pm m : ℕ) (a am W C : ℤ)
    (hN : (Nm : ℤ) = (N : ℤ) * ((m : ℤ) + 1) - W)
    (ha : |am - ((m : ℤ) + 1) * a| ≤ C)
    (hp : pm = p * (m + 1)) :
    |(2 * (Nm : ℤ) - am - 2 * pm) -
      ((m : ℤ) + 1) * (2 * N - a - 2 * p)| ≤ 2 * |W| + C := by
  have hNe : |(Nm : ℤ) - ((m : ℤ) + 1) * N| ≤ |W| := by
    have he : (Nm : ℤ) - ((m : ℤ) + 1) * N = -W := by nlinarith [hN]
    rw [he, abs_neg]
  have hpe : (pm : ℤ) = ((m : ℤ) + 1) * p := by
    exact_mod_cast hp.trans (Nat.mul_comm _ _)
  exact surplus_error_bound N a p Nm am pm ((m : ℤ) + 1) |W| C hNe ha hpe

end MagnitudeConjecture.GradedInterval
