import MagnitudeConjecture.Algebra.RightModuleStandardGradedDegreeBounds

/-! # Uniform incoming Hom bounds for the graded standard form -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- A common bound on homogeneous degrees bounds the source shift of every
nonzero incoming map, including maps between equal vertex labels. -/
theorem standardFormGraded_incoming_shift_bounds
    (h : ℕ) (hb : ∀ X Y : S.StandardFormMeshCategory, ∀ d : ℤ,
      d < 0 ∨ (h : ℤ) < d → S.standardFormIntegerHomGrading.component X Y d = ⊥)
    (X Y : S.StandardFormMeshCategory) (s t : ℤ)
    (f : (⟨S.standardFormGradedVertexFunctor.obj X, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩) (hf : f ≠ 0) :
    t ≤ s ∧ s ≤ t + h := by
  let E := S.standardFormGradedHomEquiv X Y s t
  by_contra hn
  have hz := hb X Y (s - t) (by omega)
  have hg : E.symm f = 0 := by
    apply Subtype.ext
    exact hz.le (E.symm f).property
  exact hf (E.symm.injective (hg.trans (map_zero E.symm).symm))

/-- Hom dimensions of shifted vertex modules are bounded by the fixed
ungraded mesh Hom dimension, independently of both shifts. -/
theorem standardFormGraded_hom_finrank_le
    (X Y : S.StandardFormMeshCategory) (s t : ℤ) :
    Module.finrank k
      ((⟨S.standardFormGradedVertexFunctor.obj X, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
        ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩) ≤ Module.finrank k (X ⟶ Y) := by
  letI : FiniteDimensional k (X ⟶ Y) := S.standardFormMeshHomFinite X Y
  rw [← (S.standardFormGradedHomEquiv X Y s t).finrank_eq]
  exact Submodule.finrank_le _

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
