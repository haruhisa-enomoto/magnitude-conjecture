import MagnitudeConjecture.Graded.IdempotentProjections

/-! # Homogeneous maps commute with shifted projections -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded.ModuleGrading
variable {k A M N : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable {R : VectorGrading k A}
variable (G : ModuleGrading (M := M) R) (H : ModuleGrading (M := N) R)

theorem projection_map_homogeneous (f : M →ₗ[A] N) (t : ℤ) (hf : G.Homogeneous H t f)
    (d : ℤ) (x : M) : H.projection (d + t) (f x) = f (G.projection d x) := by
  classical
  letI := G.internal.chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := G.component)
    (motive := fun x ↦ H.projection (d + t) (f x) = f (G.projection d x))
  · simp
  · intro r x
    by_cases hr : r = d
    · subst r
      rw [G.toVectorGrading.projection_of_mem x.property,
        H.toVectorGrading.projection_of_mem (hf d x x.property)]
    · rw [G.toVectorGrading.projection_of_mem_ne x.property hr,
        H.toVectorGrading.projection_of_mem_ne (hf r x x.property) (by omega), map_zero]
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem idempotentProjection_map (f : M →ₗ[A] N) (t : ℤ) (hf : G.Homogeneous H t f)
    (e : A) (d : ℤ) (x : M) :
    H.idempotentProjection e (d + t) (f x) = f (G.idempotentProjection e d x) := by
  change e • H.projection (d + t) (f x) = f (e • G.projection d x)
  rw [G.projection_map_homogeneous H f t hf, f.map_smul]

end MagnitudeConjecture.Graded.ModuleGrading
