import MagnitudeConjecture.Combinatorics.HeightBoundaryBalance

/-! # Boundary sums with one exceptional vertex -/
set_option autoImplicit false
namespace MagnitudeConjecture.HeightArrowCount
universe u
variable {V : Type u} [Fintype V]

/-- Boundary degrees are one except at a single distinguished vertex. -/
theorem boundary_sums [DecidableEq V] (s : V) (h d : V → ℤ)
    (hd : ∀ x, d x = if x = s then 0 else 1) :
    (∑ x, d x) = Fintype.card V - 1 ∧
    (∑ x, h x * d x) = (∑ x, h x) - h s := by
  classical
  have he : ∀ x, d x = 1 - if x = s then 1 else 0 := by
    intro x
    rw [hd x]
    split_ifs <;> norm_num
  constructor
  · simp [he, Finset.sum_sub_distrib]
  · simp [he, mul_sub, Finset.sum_sub_distrib]

/-- Complementary translation sets have equally many boundary vertices. -/
theorem boundary_card_eq (P I : V → Prop) [DecidablePred P] [DecidablePred I]
    (e : {x // ¬ P x} ≃ {x // ¬ I x}) :
    Fintype.card {x // P x} = Fintype.card {x // I x} := by
  have hp := Fintype.sum_subtype_add_sum_subtype P (fun _ : V ↦ (1 : ℤ))
  have hi := Fintype.sum_subtype_add_sum_subtype I (fun _ : V ↦ (1 : ℤ))
  have he : (Fintype.card {x // ¬ P x} : ℤ) = Fintype.card {x // ¬ I x} := by
    exact_mod_cast Fintype.card_congr e
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hp hi
  omega

end MagnitudeConjecture.HeightArrowCount
