import MagnitudeConjecture.Graded.FiniteVectorGrading

/-! # Restriction of a grading to a homogeneous subspace

A subspace stable under every degree projection inherits an internal grading.
This supplies the graded images and kernels used in splitting idempotents.
-/

set_option autoImplicit false
noncomputable section

namespace MagnitudeConjecture.Graded.VectorGrading

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
variable [FiniteDimensional k M] (G : VectorGrading k M) (P : Submodule k M)

/-- A subspace is homogeneous if it contains every component of each of its vectors. -/
def Stable : Prop := ∀ d x, x ∈ P → G.projection d x ∈ P

/-- The grading induced on a homogeneous subspace. -/
def restrict (hP : G.Stable P) : VectorGrading k P where
  component d := (G.component d).comap P.subtype
  internal := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_def]
      intro d
      let p : P →ₗ[k] M := (G.projection d).comp P.subtype
      have hker : (⨆ e, ⨆ (_ : e ≠ d), (G.component e).comap P.subtype) ≤
          LinearMap.ker p := by
        apply iSup_le
        intro e
        apply iSup_le
        intro hed x hx
        exact G.projection_of_mem_ne hx hed
      apply Submodule.disjoint_def.mpr
      intro x hx hy
      have hz := hker hy
      change G.projection d x.val = 0 at hz
      change x.val ∈ G.component d at hx
      rw [G.projection_of_mem hx] at hz
      exact Subtype.ext hz
    · apply top_unique
      intro x hx
      let y (d : ℤ) : P := ⟨G.projection d x.val, hP d x.val x.property⟩
      have hs : ∑ d ∈ G.degreeSupport, y d = x := by
        apply Subtype.ext
        simpa only [Submodule.coe_sum, y] using G.sum_projection x.val
      rw [← hs]
      apply Submodule.sum_mem
      intro d hd
      exact (le_iSup (fun e ↦ (G.component e).comap P.subtype) d) (G.projection_mem d x.val)

end MagnitudeConjecture.Graded.VectorGrading
