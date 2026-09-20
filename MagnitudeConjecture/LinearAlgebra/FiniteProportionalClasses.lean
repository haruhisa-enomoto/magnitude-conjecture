import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

/-! # Finitely many proportionality classes force dimension at most one -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.FiniteKernel
universe u v w
variable {k : Type u} [Field k] [Infinite k]
variable {V : Type v} [AddCommGroup V] [Module k V]

/-- Over an infinite field, a finite labelling of nonzero vectors whose equal
labels imply proportionality forces dimension at most one. -/
theorem finrank_le_one_of_finite_proportional_classes {ι : Type w} [Finite ι]
    (label : {v : V // v ≠ 0} → ι)
    (hlabel : ∀ v w, label v = label w → ∃ c : k, c • v.val = w.val) :
    Module.finrank k V ≤ 1 := by
  classical
  by_contra hn
  have hn2 : 2 ≤ Module.finrank k V := by omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := k) (M := V) hn2
  have hp : LinearIndependent k ![v 0, v 1] := by
    convert hv using 1
    ext i
    fin_cases i <;> rfl
  have hne (t : k) : v 0 + t • v 1 ≠ 0 := by
    intro ht
    have h := (LinearIndependent.pair_iff.mp hp) 1 t (by simpa using ht)
    exact one_ne_zero h.1
  let L (t : k) : ι := label ⟨v 0 + t • v 1, hne t⟩
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite L
  obtain ⟨c, hc⟩ := hlabel ⟨v 0 + a • v 1, hne a⟩ ⟨v 0 + b • v 1, hne b⟩ heq
  have hzero : (c - 1) • v 0 + (c * a - b) • v 1 = 0 := by
    calc
      _ = c • (v 0 + a • v 1) - (v 0 + b • v 1) := by module
      _ = 0 := sub_eq_zero.mpr hc
  have hcoeff := (LinearIndependent.pair_iff.mp hp) _ _ hzero
  have hc1 : c = 1 := sub_eq_zero.mp hcoeff.1
  apply hab
  exact sub_eq_zero.mp (by simpa [hc1] using hcoeff.2)

end MagnitudeConjecture.FiniteKernel
