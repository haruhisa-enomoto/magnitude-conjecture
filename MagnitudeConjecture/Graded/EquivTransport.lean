import MagnitudeConjecture.Graded.FiniteVectorGrading
import MagnitudeConjecture.Graded.QuotientDecomposition

/-! # Transporting an internal grading through linear coordinates -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded.VectorGrading
variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M]
variable [AddCommGroup N] [Module k N]

/-- Pull back an internal grading along a linear equivalence. -/
def comap (G : VectorGrading k N) (e : M ≃ₗ[k] N) : VectorGrading k M where
  component d := (G.component d).comap e.toLinearMap
  internal := by
    have heq : (fun d ↦ (G.component d).comap e.toLinearMap) =
        (fun d ↦ (G.component d).map e.symm.toLinearMap) := by
      funext d
      ext x
      constructor
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [heq]
    exact image_isInternal_of_equiv _ G.internal e.symm

end MagnitudeConjecture.Graded.VectorGrading
