import MagnitudeConjecture.CategoryTheory.GradedIntervalReconstructionFunctor
import MagnitudeConjecture.Graded.ProjectionAction

/-! # Coordinates of actual supported graded modules -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

variable (hsum : ∑ i, e i = 1) (horth : Pairwise fun i j ↦ e i * e j = 0)
variable (m : ℕ) (X : SupportedCategory (R := R) m)

/-- The interval labels cover every nonzero degree of a supported shifted module. -/
theorem supportedModule_degree_cover (d : ℤ) (hd : X.obj.obj.grading.component d ≠ ⊥) :
    ∃ r : Fin (m + 1), (r.val : ℤ) - X.obj.degree = d := by
  have hs : d + X.obj.degree ∈ shiftedSupport X.obj :=
    Finset.mem_image.mpr ⟨d, (X.obj.obj.grading.toVectorGrading.mem_support_iff d).mpr hd, rfl⟩
  have hb := X.property _ hs
  refine ⟨⟨(d + X.obj.degree).toNat, by omega⟩, ?_⟩
  dsimp
  omega

/-- Evaluate all interval projectives to express the actual underlying vector space in reconstruction coordinates. -/
def supportedModuleCoordinateEquiv : X.obj.obj.module ≃ₗ[k]
    intervalCoordinateSpace R hmul e he0
      (CoveringHom.restrictedLinearYoneda (k := k) (principalDegreeInclusion R hmul e he0) X.obj) m :=
  (X.obj.obj.grading.idempotentCoordinateEquiv e he he0 hsum horth
    (fun r : Fin (m + 1) ↦ (r.val : ℤ) - X.obj.degree)
    (by
      intro r s h
      change (r.val : ℤ) - X.obj.degree = (s.val : ℤ) - X.obj.degree at h
      apply Fin.ext
      omega)
    (supportedModule_degree_cover R m X)).trans
      (LinearEquiv.piCongrRight fun p : ι × Fin (m + 1) ↦
        (principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val X.obj).symm)

/-- Reading a reconstructed coordinate recovers the corresponding homogeneous idempotent projection. -/
theorem supportedModuleCoordinateEquiv_evaluation (x : X.obj.obj.module) (p : ι × Fin (m + 1)) :
    principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val X.obj
      (supportedModuleCoordinateEquiv R hmul e he0 he hsum horth m X x p) =
      ⟨X.obj.obj.grading.idempotentProjection (e p.1) ((p.2.val : ℤ) - X.obj.degree) x,
        X.obj.obj.grading.idempotentProjection_mem (e p.1) (he p.1) (he0 p.1)
          ((p.2.val : ℤ) - X.obj.degree) x⟩ := by
  exact (principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val X.obj).apply_symm_apply _

end MagnitudeConjecture.Graded.FiniteGradedModule
