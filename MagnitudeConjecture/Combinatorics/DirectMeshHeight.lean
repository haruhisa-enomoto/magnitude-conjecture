import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Combinatorics.Quiver.Path

/-! # Heights by direct induction on an ordered translation quiver -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.DirectMeshHeight
local instance : DecidablePred (fun p : Prop ↦ p) := Classical.propDecidable
universe u
variable {V : Type u} (rank : V → ℕ) (E : V → V → Prop)
variable (hE : ∀ x y, E x y → rank x < rank y)

/-- Choose one predecessor at each nonsource vertex and count backwards. -/
def height (rank : V → ℕ) (E : V → V → Prop)
    (hE : ∀ x y, E x y → rank x < rank y) (x : V) : ℕ :=
  if hx : ∃ y, E y x then height rank E hE hx.choose + 1 else 0
termination_by rank x
decreasing_by exact hE _ _ hx.choose_spec

/-- An empty incoming neighborhood has height zero. -/
theorem height_eq_zero (x : V) (hx : ¬ ∃ y, E y x) :
    height rank E hE x = 0 := by
  rw [height]
  simp only [dif_neg hx]

/-- A boundary vertex has at most one predecessor; at an interior vertex all
predecessors receive an arrow from its translate. These local conditions force
every arrow to increase height by exactly one. -/
theorem height_arrow
    (hmesh : ∀ x, (∀ a b, E a x → E b x → a = b) ∨
      ∃ t, ∀ y, E y x → E t y) :
    ∀ x y, E x y → height rank E hE y = height rank E hE x + 1 := by
  have aux : ∀ y, ∀ x, E x y → height rank E hE y = height rank E hE x + 1 := by
    intro y
    induction y using (measure rank).wf.induction with
    | h y ih =>
      intro x hxy
      have hy : ∃ a, E a y := ⟨x, hxy⟩
      have hp := hy.choose_spec
      have heq : height rank E hE hy.choose = height rank E hE x := by
        rcases hmesh y with hb | ⟨t, ht⟩
        · rw [hb hy.choose x hp hxy]
        · have ha := ih hy.choose (hE _ _ hp) t (ht _ hp)
          have hx := ih x (hE _ _ hxy) t (ht _ hxy)
          exact ha.trans hx.symm
      rw [height, dif_pos hy, heq]
  exact fun x y ↦ aux y x

/-- Every nonempty mesh places its target two levels above its translate. -/
theorem height_mesh
    (hmesh : ∀ x, (∀ a b, E a x → E b x → a = b) ∨
      ∃ t, ∀ y, E y x → E t y)
    (t x : V) (hx : ∃ y, E y x)
    (ht : ∀ y, E y x → E t y) :
    height rank E hE x = height rank E hE t + 2 := by
  obtain ⟨y, hy⟩ := hx
  rw [height_arrow rank E hE hmesh y x hy,
    height_arrow rank E hE hmesh t y (ht y hy)]

/-- Along any path, height increases by its length. -/
theorem height_path [Quiver V]
    (hmesh : ∀ x, (∀ a b, E a x → E b x → a = b) ∨
      ∃ t, ∀ y, E y x → E t y)
    (hedge : ∀ {x y : V}, (x ⟶ y) → E x y)
    {x y : V} (p : Quiver.Path x y) :
    height rank E hE y = height rank E hE x + p.length := by
  induction p with
  | nil => simp
  | @cons y z p e ih =>
    rw [height_arrow rank E hE hmesh y z (hedge e), ih]
    simp only [Quiver.Path.length_cons]
    omega

include rank hE in
/-- Any two paths with the same endpoints have equal length. -/
theorem path_length_eq [Quiver V]
    (hmesh : ∀ x, (∀ a b, E a x → E b x → a = b) ∨
      ∃ t, ∀ y, E y x → E t y)
    (hedge : ∀ {x y : V}, (x ⟶ y) → E x y)
    {x y : V} (p q : Quiver.Path x y) : p.length = q.length := by
  have hp := height_path rank E hE hmesh hedge p
  have hq := height_path rank E hE hmesh hedge q
  omega

end MagnitudeConjecture.DirectMeshHeight
