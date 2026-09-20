import MagnitudeConjecture.Graded.RegularModule
import Lean.Elab.Tactic.Omega

/-! # Multiplication across a finite interval of nonnegative degrees -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded.VectorGrading
variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
include hmul hneg

/-- The product coefficient between interval degrees is the sum over intermediate
interval degrees: no term can leave the interval and then return. -/
theorem interval_convolution (m : ℕ) (r t : Fin (m + 1)) (a b : A) :
    R.projection ((r.val : ℤ) - t.val) (a * b) =
      ∑ s : Fin (m + 1), R.projection ((r.val : ℤ) - s.val) a *
        R.projection ((s.val : ℤ) - t.val) b := by
  classical
  letI := R.internal.chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := R.component)
    (motive := fun a ↦ R.projection ((r.val : ℤ) - t.val) (a * b) =
      ∑ s : Fin (m + 1), R.projection ((r.val : ℤ) - s.val) a *
        R.projection ((s.val : ℤ) - t.val) b)
  · simp
  · intro i a
    apply DirectSum.Decomposition.inductionOn (ℳ := R.component)
      (motive := fun b ↦ R.projection ((r.val : ℤ) - t.val) (a.val * b) =
        ∑ s : Fin (m + 1), R.projection ((r.val : ℤ) - s.val) a.val *
          R.projection ((s.val : ℤ) - t.val) b)
    · simp
    · intro j b
      by_cases ha : a.val = 0
      · simp [ha]
      by_cases hb : b.val = 0
      · simp [hb]
      have hi : 0 ≤ i := by
        by_contra h
        exact ha ((hneg i (by omega)).le a.property)
      have hj : 0 ≤ j := by
        by_contra h
        exact hb ((hneg j (by omega)).le b.property)
      by_cases hd : i + j = (r.val : ℤ) - t.val
      · let s : Fin (m + 1) := ⟨((t.val : ℤ) + j).toNat, by
          have hr := r.isLt
          omega⟩
        have hs : (s.val : ℤ) = (t.val : ℤ) + j := by dsimp [s]; omega
        have hai : (r.val : ℤ) - s.val = i := by omega
        have hbj : (s.val : ℤ) - t.val = j := by omega
        rw [R.projection_of_mem (hd ▸ hmul a.property b.property)]
        symm
        calc
          _ = R.projection ((r.val : ℤ) - s.val) a.val *
              R.projection ((s.val : ℤ) - t.val) b.val := by
            apply Finset.sum_eq_single s
            · intro q hq hqs
              have hne : j ≠ (q.val : ℤ) - t.val := by
                intro h
                apply hqs
                apply Fin.ext
                omega
              rw [R.projection_of_mem_ne b.property hne, mul_zero]
            · simp
          _ = a.val * b.val := by
            rw [hai, hbj, R.projection_of_mem a.property, R.projection_of_mem b.property]
      · rw [R.projection_of_mem_ne (hmul a.property b.property) hd]
        symm
        apply Finset.sum_eq_zero
        intro s hs
        by_cases hai : i = (r.val : ℤ) - s.val
        · have hbj : j ≠ (s.val : ℤ) - t.val := by omega
          rw [R.projection_of_mem_ne b.property hbj, mul_zero]
        · rw [R.projection_of_mem_ne a.property hai, zero_mul]
    · intro b c hb hc
      simp only [mul_add, map_add, Finset.sum_add_distrib, hb, hc]
  · intro a c ha hc
    simp only [add_mul, map_add, Finset.sum_add_distrib, ha, hc]

end MagnitudeConjecture.Graded.VectorGrading
