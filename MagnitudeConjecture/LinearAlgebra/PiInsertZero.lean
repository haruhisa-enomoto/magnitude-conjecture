import Mathlib.LinearAlgebra.Pi

/-! # Inserting a zero coordinate in a dependent family of modules -/

set_option autoImplicit false
noncomputable section

namespace LinearMap

variable (R : Type*) [Semiring R] {ι : Type*} (M : ι → Type*)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Extend a family on the complement of one index by zero at that index. -/
def insertZeroCoordinate (a : ι) :
    (∀ i : {i : ι // i ≠ a}, M i.1) →ₗ[R] (∀ i, M i) := by
  classical
  exact LinearMap.pi fun i ↦
    if hi : i = a then 0 else
      LinearMap.proj (R := R) (φ := fun b : {i : ι // i ≠ a} ↦ M b.1) ⟨i, hi⟩

theorem insertZeroCoordinate_self (a : ι)
    (g : ∀ i : {i : ι // i ≠ a}, M i.1) :
    insertZeroCoordinate R M a g a = 0 := by
  classical
  simp [insertZeroCoordinate]

theorem insertZeroCoordinate_other (a : ι)
    (g : ∀ i : {i : ι // i ≠ a}, M i.1) (b : {i : ι // i ≠ a}) :
    insertZeroCoordinate R M a g b.1 = g b := by
  classical
  simp [insertZeroCoordinate, b.2]

end LinearMap
