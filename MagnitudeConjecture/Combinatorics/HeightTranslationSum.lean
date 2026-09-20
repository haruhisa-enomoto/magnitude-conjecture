import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Summing the two-step height change across translation -/
set_option autoImplicit false
namespace MagnitudeConjecture.HeightArrowCount
universe u
variable {V : Type u} [Fintype V]

/-- Translation identifies the two complementary boundary sets. Summing its
height change gives the difference of boundary height sums. -/
theorem boundary_height_difference
    (P I : V → Prop) [DecidablePred P] [DecidablePred I]
    (e : {x // ¬ P x} ≃ {x // ¬ I x}) (h : V → ℤ)
    (he : ∀ x, h x.1 = h (e x).1 + 2) :
    (∑ x : {x // I x}, h x.1) - (∑ x : {x // P x}, h x.1) =
      2 * ((Fintype.card V : ℤ) - Fintype.card {x // P x}) := by
  have hs : (∑ x : {x // ¬ P x}, h x.1) =
      (∑ x : {x // ¬ I x}, h x.1) + 2 * Fintype.card {x // ¬ P x} := by
    calc
      (∑ x : {x // ¬ P x}, h x.1) = ∑ x, (h (e x).1 + 2) :=
        Finset.sum_congr rfl (fun x _ ↦ he x)
      _ = (∑ x : {x // ¬ I x}, h x.1) + 2 * Fintype.card {x // ¬ P x} := by
        rw [Finset.sum_add_distrib, e.sum_comp (fun x ↦ h x.1)]
        simp [mul_comm]
  have hp := Fintype.sum_subtype_add_sum_subtype P h
  have hi := Fintype.sum_subtype_add_sum_subtype I h
  have hc := Fintype.sum_subtype_add_sum_subtype P (fun _ : V ↦ (1 : ℤ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hc
  omega

end MagnitudeConjecture.HeightArrowCount
