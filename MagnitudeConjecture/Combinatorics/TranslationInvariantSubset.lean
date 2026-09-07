import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Translation-invariant subsets of a group

The regular translation action is transitive, so a subset invariant under
every left translation is empty or universal.  This is the final set-theoretic
step in Gabriel's proof of Lemma 3.5.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.CoveringAction

universe u

/-- A subset of an additive group which is invariant under every left
translation is empty or the whole group. -/
theorem eq_empty_or_univ_of_add_left_invariant
    {A : Type u} [AddGroup A] (H : Set A)
    (hinv : ∀ a b : A, b ∈ H ↔ a + b ∈ H) :
    H = ∅ ∨ H = Set.univ := by
  by_cases hH : H = ∅
  · exact Or.inl hH
  · right
    obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.mpr hH
    apply Set.eq_univ_of_forall
    intro a
    have hab := (hinv (a + -b) b).mp hb
    simpa [add_assoc] using hab

/-- Multiplicative form of translation transitivity. -/
theorem eq_empty_or_univ_of_mul_left_invariant
    {G : Type u} [Group G] (H : Set G)
    (hinv : ∀ g h : G, h ∈ H ↔ g * h ∈ H) :
    H = ∅ ∨ H = Set.univ := by
  by_cases hH : H = ∅
  · exact Or.inl hH
  · right
    obtain ⟨h, hh⟩ := Set.nonempty_iff_ne_empty.mpr hH
    apply Set.eq_univ_of_forall
    intro g
    have hgh := (hinv (g * h⁻¹) h).mp hh
    simpa [mul_assoc] using hgh

end MagnitudeConjecture.CoveringAction
