import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Weighted sums over a common part of every finite fiber -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace MagnitudeConjecture
universe u v

/-- Restricting every fiber to the same contained set gives a product. -/
def commonFiberEquiv {ι : Type u} {α : Type v} (F : ι → Finset α)
    (I : Finset α) (hI : ∀ i, I ⊆ F i) :
    {a : (i : ι) × ↥(F i) // a.2.val ∈ I} ≃ ι × ↥I where
  toFun a := ⟨a.val.1, ⟨a.val.2.val, a.property⟩⟩
  invFun a := ⟨⟨a.1, ⟨a.2.val, hI a.1 a.2.property⟩⟩, a.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A weight depending only on the label repeats once for each common shift. -/
theorem sum_common_fiber {ι : Type u} [Fintype ι] {α : Type v} [DecidableEq α]
    (F : ι → Finset α) (I : Finset α) (hI : ∀ i, I ⊆ F i) (w : ι → ℕ) :
    (∑ a : {a : (i : ι) × ↥(F i) // a.2.val ∈ I}, w a.val.1) =
      I.card * ∑ i, w i := by
  classical
  have he := (commonFiberEquiv F I hI).sum_comp (fun a ↦ w a.1)
  change (∑ a : {a : (i : ι) × ↥(F i) // a.2.val ∈ I}, w a.val.1) =
    ∑ a : ι × ↥I, w a.1 at he
  rw [he, Fintype.sum_prod_type]
  simp [Finset.mul_sum]

end MagnitudeConjecture
