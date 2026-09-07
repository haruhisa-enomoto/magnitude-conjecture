import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# The finite covering average identity

This file isolates the telescoping and averaging calculation used after a
finite covering has separated all of the local configurations relevant to a
deletion.  The geometric input is deliberately absent: later categorical
files need only produce the integral scaling identity and nonnegative local
changes to invoke this kernel.
-/

namespace MagnitudeConjecture.CoveringAverage

open scoped BigOperators

/-- The sum of all local changes in a finite family. -/
def localChangeTotal {m : ℕ} (localChange : Fin m → ℤ) : ℤ :=
  ∑ j, localChange j

/-- Consecutive differences telescope from the first value to the last. -/
theorem localChangeTotal_eq_first_sub_last {m : ℕ}
    (surplusAt : Fin (m + 1) → ℤ) (localChange : Fin m → ℤ)
    (localChange_eq : ∀ j, localChange j = surplusAt j.castSucc - surplusAt j.succ) :
    localChangeTotal localChange = surplusAt 0 - surplusAt (Fin.last m) := by
  rw [localChangeTotal]
  simp_rw [localChange_eq, Finset.sum_sub_distrib]
  have hCast := Fin.sum_univ_castSucc surplusAt
  have hSucc := Fin.sum_univ_succ surplusAt
  omega

/-- If the first and last covering values scale by the degree, their
difference is exactly the total local change upstairs. -/
theorem covering_scale_mul_difference_eq_localChangeTotal {m : ℕ}
    (initialDownstairs finalDownstairs : ℤ)
    (surplusAt : Fin (m + 1) → ℤ) (localChange : Fin m → ℤ)
    (localChange_eq : ∀ j, localChange j = surplusAt j.castSucc - surplusAt j.succ)
    (initial_scale : surplusAt 0 = (m : ℤ) * initialDownstairs)
    (final_scale : surplusAt (Fin.last m) = (m : ℤ) * finalDownstairs) :
    (m : ℤ) * (initialDownstairs - finalDownstairs) = localChangeTotal localChange := by
  rw [localChangeTotal_eq_first_sub_last surplusAt localChange localChange_eq,
    initial_scale, final_scale]
  ring

/-- The downstairs difference is the average of the local changes upstairs. -/
theorem downstairs_difference_eq_average_localChange {m : ℕ}
    (hm : 0 < m) (initialDownstairs finalDownstairs : ℤ)
    (surplusAt : Fin (m + 1) → ℤ) (localChange : Fin m → ℤ)
    (localChange_eq : ∀ j, localChange j = surplusAt j.castSucc - surplusAt j.succ)
    (initial_scale : surplusAt 0 = (m : ℤ) * initialDownstairs)
    (final_scale : surplusAt (Fin.last m) = (m : ℤ) * finalDownstairs) :
    ((initialDownstairs - finalDownstairs : ℤ) : ℚ) =
      (1 / (m : ℚ)) * ∑ j, (localChange j : ℚ) := by
  have hIntegral := covering_scale_mul_difference_eq_localChangeTotal
    initialDownstairs finalDownstairs surplusAt localChange localChange_eq
    initial_scale final_scale
  have hmQ : (m : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm
  have hCast : ((localChangeTotal localChange : ℤ) : ℚ) =
      ∑ j, (localChange j : ℚ) := by
    simp [localChangeTotal]
  calc
    ((initialDownstairs - finalDownstairs : ℤ) : ℚ) =
        (1 / (m : ℚ)) * (((m : ℤ) *
          (initialDownstairs - finalDownstairs) : ℤ) : ℚ) := by
            push_cast
            field_simp [hmQ]
    _ = (1 / (m : ℚ)) * ∑ j, (localChange j : ℚ) := by
      rw [hIntegral, hCast]

/-- Nonnegative local changes force a nonnegative difference downstairs. -/
theorem downstairs_difference_nonnegative {m : ℕ}
    (hm : 0 < m) (initialDownstairs finalDownstairs : ℤ)
    (surplusAt : Fin (m + 1) → ℤ) (localChange : Fin m → ℤ)
    (localChange_eq : ∀ j, localChange j = surplusAt j.castSucc - surplusAt j.succ)
    (initial_scale : surplusAt 0 = (m : ℤ) * initialDownstairs)
    (final_scale : surplusAt (Fin.last m) = (m : ℤ) * finalDownstairs)
    (localChange_nonnegative : ∀ j, 0 ≤ localChange j) :
    0 ≤ initialDownstairs - finalDownstairs := by
  have hTotal : 0 ≤ localChangeTotal localChange := by
    exact Finset.sum_nonneg fun j _ ↦ localChange_nonnegative j
  have hIntegral := covering_scale_mul_difference_eq_localChangeTotal
    initialDownstairs finalDownstairs surplusAt localChange localChange_eq
    initial_scale final_scale
  nlinarith

/-- Equality downstairs, together with local nonnegativity, forces every local
change upstairs to vanish. -/
theorem localChange_eq_zero_of_downstairs_eq {m : ℕ}
    (initialDownstairs finalDownstairs : ℤ)
    (surplusAt : Fin (m + 1) → ℤ) (localChange : Fin m → ℤ)
    (localChange_eq : ∀ j, localChange j = surplusAt j.castSucc - surplusAt j.succ)
    (initial_scale : surplusAt 0 = (m : ℤ) * initialDownstairs)
    (final_scale : surplusAt (Fin.last m) = (m : ℤ) * finalDownstairs)
    (localChange_nonnegative : ∀ j, 0 ≤ localChange j)
    (downstairs_eq : initialDownstairs = finalDownstairs) :
    ∀ j, localChange j = 0 := by
  have hIntegral := covering_scale_mul_difference_eq_localChangeTotal
    initialDownstairs finalDownstairs surplusAt localChange localChange_eq
    initial_scale final_scale
  rw [downstairs_eq, sub_self, mul_zero] at hIntegral
  have hTotal : localChangeTotal localChange = 0 := hIntegral.symm
  have hEach := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) ↦ localChange_nonnegative j)).mp
    (by simpa [localChangeTotal] using hTotal)
  intro j
  exact hEach j (Finset.mem_univ j)

end MagnitudeConjecture.CoveringAverage
