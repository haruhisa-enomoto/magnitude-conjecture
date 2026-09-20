import MagnitudeConjecture.Combinatorics.RankedReachability
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! # Reachability of the unique sink in a finite ranked relation -/
set_option autoImplicit false
namespace MagnitudeConjecture.RankedReachability
universe u
variable {V : Type u} [Fintype V]

/-- Reversing a bounded rank reduces sink reachability to source reachability. -/
theorem reaches_sink (rank : V → ℕ) (E : V → V → Prop)
    (hE : ∀ x y, E x y → rank x < rank y)
    (sink : V) (hsink : ∀ x, (¬ ∃ y, E x y) → x = sink) :
    ∀ x, Relation.ReflTransGen E x sink := by
  classical
  let N := Finset.univ.sup rank
  have hb : ∀ x, rank x ≤ N := fun x ↦ Finset.le_sup (Finset.mem_univ x)
  have hr : ∀ x y, E y x → N - rank x < N - rank y := by
    intro x y h
    have ht := hE y x h
    have hx := hb x
    omega
  intro x
  have h := source_reaches (fun x ↦ N - rank x) (Function.swap E) hr sink hsink x
  exact Relation.reflTransGen_swap.mp h

end MagnitudeConjecture.RankedReachability
