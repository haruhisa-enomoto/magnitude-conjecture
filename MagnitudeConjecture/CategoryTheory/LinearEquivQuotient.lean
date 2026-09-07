import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Transporting a quotient along a linear equivalence

This small helper packages the quotient equivalence induced when a linear
equivalence carries one submodule exactly onto another.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture

universe u v w

variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear equivalence carrying `p` onto `q` descends to the corresponding
quotient modules. -/
def LinearEquiv.quotientOfMapEq (e : M ≃ₗ[R] N)
    (p : Submodule R M) (q : Submodule R N)
    (h : p.map e.toLinearMap = q) :
    (M ⧸ p) ≃ₗ[R] (N ⧸ q) := by
  let f : (M ⧸ p) →ₗ[R] (N ⧸ q) :=
    p.mapQ q e.toLinearMap (by
      intro x hx
      rw [← h]
      exact ⟨x, hx, rfl⟩)
  let g : (N ⧸ q) →ₗ[R] (M ⧸ p) :=
    q.mapQ p e.symm.toLinearMap (by
      intro y hy
      rw [← h] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      simpa [← hxy] using hx)
  exact LinearEquiv.ofLinearMap f g
    (by
      apply q.linearMap_qext
      apply LinearMap.ext
      intro y
      simp [f, g])
    (by
      apply p.linearMap_qext
      apply LinearMap.ext
      intro x
      simp [f, g])

@[simp]
theorem LinearEquiv.quotientOfMapEq_mk (e : M ≃ₗ[R] N)
    (p : Submodule R M) (q : Submodule R N)
    (h : p.map e.toLinearMap = q) (x : M) :
    LinearEquiv.quotientOfMapEq e p q h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) :=
  rfl

end MagnitudeConjecture
