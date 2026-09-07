import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Rooted parent trees

A parent map together with a natural-number rank which drops by one away from
the root presents an undirected tree. This elementary graph lemma is used for
the prefix tree of mesh-sectional paths.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture

universe u

namespace ParentTree

variable {V : Type u}

/-- The undirected graph obtained by joining every nonroot vertex to its
chosen parent. -/
def graph (root : V) (parent : V → V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦ x ≠ root ∧ parent x = y

theorem adj_iff (root : V) (parent : V → V) {x y : V} :
    (graph root parent).Adj x y ↔
      x ≠ y ∧ ((x ≠ root ∧ parent x = y) ∨
        (y ≠ root ∧ parent y = x)) :=
  Iff.rfl

theorem reachable_root
    (root : V) (parent : V → V) (rank : V → ℕ)
    (hparent : ∀ x, x ≠ root → rank (parent x) + 1 = rank x)
    (x : V) :
    (graph root parent).Reachable x root := by
  induction h : rank x using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hx : x = root
      · subst x
        exact SimpleGraph.Reachable.refl root
      · have hrank : rank (parent x) < rank x := by
          rw [← hparent x hx]
          omega
        have hreach := ih (rank (parent x)) (h ▸ hrank)
          (parent x) rfl
        have hadj : (graph root parent).Adj x (parent x) := by
          rw [adj_iff]
          refine ⟨?_, Or.inl ⟨hx, rfl⟩⟩
          intro hxp
          have hr := hparent x hx
          have heq := congrArg rank hxp
          omega
        exact hadj.reachable.trans hreach

/-- A parent graph whose rank decreases exactly once toward the root is a
tree. -/
theorem graph_isTree
    (root : V) (parent : V → V) (rank : V → ℕ)
    (hparent : ∀ x, x ≠ root → rank (parent x) + 1 = rank x) :
    (graph root parent).IsTree := by
  classical
  constructor
  · letI : Nonempty V := ⟨root⟩
    apply SimpleGraph.Connected.mk
    intro x y
    exact (reachable_root root parent rank hparent x).trans
      (reachable_root root parent rank hparent y).symm
  · intro v c hc
    have hsupport : c.support.toFinset.Nonempty := by
      exact ⟨v, by simp⟩
    obtain ⟨x, hx, hmax⟩ :=
      Finset.exists_max_image c.support.toFinset rank hsupport
    have hxc : x ∈ c.support := List.mem_toFinset.mp hx
    let d := c.rotate x hxc
    have hd : d.IsCycle := hc.rotate hxc
    have hsnd_d : d.snd ∈ d.support :=
      List.mem_of_mem_tail (d.snd_mem_tail_support hd.not_nil)
    have hpen_d : d.penultimate ∈ d.support :=
      List.mem_of_mem_dropLast (d.penultimate_mem_dropLast_support hd.not_nil)
    have hsnd_c : d.snd ∈ c.support := by
      change (c.rotate x hxc).snd ∈ (c.rotate x hxc).support at hsnd_d
      exact (c.mem_support_rotate_iff x hxc).mp hsnd_d
    have hpen_c : d.penultimate ∈ c.support := by
      change (c.rotate x hxc).penultimate ∈
        (c.rotate x hxc).support at hpen_d
      exact (c.mem_support_rotate_iff x hxc).mp hpen_d
    have hsnd_le : rank d.snd ≤ rank x :=
      hmax d.snd (List.mem_toFinset.mpr hsnd_c)
    have hpen_le : rank d.penultimate ≤ rank x :=
      hmax d.penultimate (List.mem_toFinset.mpr hpen_c)
    have hsnd_parent : parent x = d.snd := by
      have hadj := d.adj_snd hd.not_nil
      rw [adj_iff] at hadj
      rcases hadj.2 with h | h
      · exact h.2
      · have hr := hparent d.snd h.1
        rw [h.2] at hr
        omega
    have hpen_parent : parent x = d.penultimate := by
      have hadj := (d.adj_penultimate hd.not_nil).symm
      rw [adj_iff] at hadj
      rcases hadj.2 with h | h
      · exact h.2
      · have hr := hparent d.penultimate h.1
        rw [h.2] at hr
        omega
    exact hd.snd_ne_penultimate (hsnd_parent ▸ hpen_parent)

end ParentTree

end MagnitudeConjecture
