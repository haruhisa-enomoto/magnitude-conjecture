import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Surjectivity on a component of a dependent direct sum
-/

set_option autoImplicit false

namespace DFinsupp

universe u₁ u₂ u₃

variable {R : Type u₁} [Semiring R]
variable {I : Type u₂} [DecidableEq I]
variable {M N : I → Type u₃}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

/-- If a componentwise map of dependent direct sums is surjective, then each
component map is surjective. -/
theorem linearMap_component_surjective
    (f : ∀ i, M i →ₗ[R] N i)
    (h : Function.Surjective (mapRange.linearMap f))
    (i : I) :
    Function.Surjective (f i) := by
  intro y
  obtain ⟨x, hx⟩ := h (DirectSum.lof R I N i y)
  refine ⟨x i, ?_⟩
  have hi := congrArg (fun z ↦ z i) hx
  simpa [mapRange.linearMap_apply, mapRange_apply,
    DirectSum.lof_eq_of, DirectSum.of_apply] using hi

end DFinsupp
