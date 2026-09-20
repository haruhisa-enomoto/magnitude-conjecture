import MagnitudeConjecture.Graded.GradedSubspace
import MagnitudeConjecture.Graded.ModuleMapComponents

/-! # Graded submodules and homogeneous kernels and images -/

set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded.ModuleGrading

variable {k A M N : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable {R : VectorGrading k A} (G : ModuleGrading (M := M) R)
variable (H : ModuleGrading (M := N) R)

/-- Degree-zero module maps commute with every homogeneous projection. -/
theorem projection_map (f : M →ₗ[A] N) (hf : G.Homogeneous H 0 f)
    (d : ℤ) (x : M) : H.projection d (f x) = f (G.projection d x) := by
  letI := G.internal.chooseDecomposition
  apply DirectSum.Decomposition.inductionOn (ℳ := G.component)
    (motive := fun x ↦ H.projection d (f x) = f (G.projection d x))
  · simp
  · intro i x
    have hh : f x.val ∈ H.component i := by simpa using hf i x.val x.property
    by_cases hid : i = d
    · subst i
      rw [H.toVectorGrading.projection_of_mem hh,
        G.toVectorGrading.projection_of_mem x.property]
    · rw [H.toVectorGrading.projection_of_mem_ne hh hid,
        G.toVectorGrading.projection_of_mem_ne x.property hid, map_zero]
  · intro x y hx hy
    simp only [map_add, hx, hy]

variable [FiniteDimensional k M]

/-- A submodule stable under all projections inherits the module grading. -/
def restrict (P : Submodule A M) (hP : G.toVectorGrading.Stable (P.restrictScalars k)) :
    ModuleGrading (M := P) R where
  toVectorGrading := G.toVectorGrading.restrict (P.restrictScalars k) hP
  smul_mem := by
    intro i j a x ha hx
    exact G.smul_mem ha hx

theorem kernel_stable (f : M →ₗ[A] N) (hf : G.Homogeneous H 0 f) :
    G.toVectorGrading.Stable (f.ker.restrictScalars k) := by
  intro d x hx
  change f (G.projection d x) = 0
  rw [← G.projection_map H f hf]
  change f x = 0 at hx
  rw [hx, map_zero]

variable [FiniteDimensional k N]

theorem range_stable (f : M →ₗ[A] N) (hf : G.Homogeneous H 0 f) :
    H.toVectorGrading.Stable (f.range.restrictScalars k) := by
  intro d y hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨G.projection d x, (G.projection_map H f hf d x).symm⟩

/-- The actual kernel carries the induced grading. -/
def kernelGrading (f : M →ₗ[A] N) (hf : G.Homogeneous H 0 f) :
    ModuleGrading (M := f.ker) R := G.restrict f.ker (G.kernel_stable H f hf)

/-- The actual image carries the induced grading. -/
def rangeGrading (f : M →ₗ[A] N) (hf : G.Homogeneous H 0 f) :
    ModuleGrading (M := f.range) R := H.restrict f.range (G.range_stable H f hf)

end MagnitudeConjecture.Graded.ModuleGrading
