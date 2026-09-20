import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.BilinearMap

/-! # Coordinates of a generated submodule at a scalar corner -/
set_option autoImplicit false
namespace MagnitudeConjecture.ScalarCorner
universe u v w
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module k M]
variable [IsScalarTower k R M]

/-- Multiplying a generated relation back into the corner stays in the
original vector-space relation subspace. -/
theorem smul_mem_of_mem_span (p : R) (W : Submodule k M)
    (hfix : ∀ x ∈ W, p • x = x)
    (hcorner : ∀ a : R, ∃ c : k, p * a * p = algebraMap k R c * p)
    {x : M} (hx : x ∈ Submodule.span R (W : Set M)) : p • x ∈ W := by
  have hs : ∀ a : R, p • (a • x) ∈ W := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro a
      obtain ⟨c, hc⟩ := hcorner a
      have heq : p • (a • x) = c • x := by
        calc
          p • (a • x) = (p * a * p) • x := by rw [mul_smul, mul_smul, hfix x hx]
          _ = (algebraMap k R c * p) • x := by rw [hc]
          _ = c • x := by rw [mul_smul, hfix x hx, algebraMap_smul]
      rw [heq]
      exact W.smul_mem c hx
    | zero => intro a; simp
    | add x y hx hy ihx ihy =>
      intro a
      simpa only [smul_add] using W.add_mem (ihx a) (ihy a)
    | smul b x hx ih =>
      intro a
      simpa only [mul_smul] using ih (a * b)
  simpa using hs 1

/-- The p-fixed vectors in the generated module are exactly the original
relations, viewed inside the ambient module. -/
theorem mem_span_and_fixed_iff (p : R) (W : Submodule k M)
    (hfix : ∀ x ∈ W, p • x = x)
    (hcorner : ∀ a : R, ∃ c : k, p * a * p = algebraMap k R c * p)
    (x : M) :
    (x ∈ Submodule.span R (W : Set M) ∧ p • x = x) ↔ x ∈ W := by
  constructor
  · rintro ⟨hx, he⟩
    rw [← he]
    exact smul_mem_of_mem_span p W hfix hcorner hx
  · intro hx
    exact ⟨Submodule.subset_span hx, hfix x hx⟩

end MagnitudeConjecture.ScalarCorner
