import Mathlib.LinearAlgebra.Pi

/-! # A single coordinate as a subspace of a dependent product -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture
variable {k ι : Type*} [Field k]
variable (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- Vectors vanishing at every coordinate except p. -/
def singleCoordinate (p : ι) : Submodule k (∀ i, V i) where
  carrier := {x | ∀ q, q ≠ p → x q = 0}
  zero_mem' := fun _ _ ↦ rfl
  add_mem' := by intro x y hx hy q hq; change x q + y q = 0; rw [hx q hq, hy q hq, add_zero]
  smul_mem' := by intro c x hx q hq; change c • x q = 0; rw [hx q hq, smul_zero]

/-- Evaluation at p identifies its coordinate subspace with the original vector space. -/
def singleCoordinateEquiv (p : ι) : singleCoordinate (k := k) V p ≃ₗ[k] V p := by
  classical
  exact
    { toFun := fun x ↦ x.val p
      invFun := fun x ↦ ⟨Pi.single p x, fun q hq ↦ Pi.single_eq_of_ne hq x⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        funext q
        change Pi.single p (x.val p) q = x.val q
        by_cases hq : q = p
        · subst q; exact Pi.single_eq_same p (x.val p)
        · rw [Pi.single_eq_of_ne hq]
          exact (x.property q hq).symm
      right_inv := fun x ↦ Pi.single_eq_same p x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

end MagnitudeConjecture
