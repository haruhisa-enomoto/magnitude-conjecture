import MagnitudeConjecture.CategoryTheory.GradedIntervalCoordinateComparison
import MagnitudeConjecture.Graded.BundledIdempotentComponent

/-! # Evaluation after reconstruction recovers every interval coordinate -/
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
variable (F : (PrincipalDegreeCategory R hmul e he0)ᵒᵖ ⥤ ModuleCat.{u} k)
variable [F.Additive] [F.Linear k]
variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
variable (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
variable (horth : Pairwise fun i j ↦ e i * e j = 0)
variable (hfinite : ∀ p, FiniteDimensional k (F.obj p)) (m : ℕ)

/-- The actual projective evaluation of the reconstructed module is the original coordinate. -/
def intervalEvaluationCoordinateEquiv (p : ι × Fin (m + 1)) :
    ((principalDegreeInclusion R hmul e he0).obj (intervalProjectiveLabel R hmul e he0 m p) ⟶
      (intervalReconstructedSupportedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).obj) ≃ₗ[k]
        F.obj (op (intervalProjectiveLabel R hmul e he0 m p)) := by
  letI := intervalReconstructedModule R hmul e he0 he F hneg h1 hsum horth m
  letI := intervalReconstructedScalarTower R hmul e he0 he F hneg h1 hsum horth m
  letI : ∀ q : ι × Fin (m + 1), FiniteDimensional k
      (F.obj (op (intervalProjectiveLabel R hmul e he0 m q))) := fun q ↦ hfinite _
  let G := intervalReconstructedGrading R hmul e he0 he F hneg h1 hsum horth m
  let E := principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val
    (intervalReconstructedSupportedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).obj
  have E' : ((principalDegreeInclusion R hmul e he0).obj
      (intervalProjectiveLabel R hmul e he0 m p) ⟶
      (intervalReconstructedSupportedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).obj) ≃ₗ[k]
        idempotentComponent R G.toBundled.grading (e p.1) p.2.val := by
    change _ ≃ₗ[k] idempotentComponent R G.toBundled.grading (e p.1) ((p.2.val : ℤ) - 0) at E
    exact E.trans (LinearEquiv.ofEq _ _
      (congrArg (idempotentComponent R G.toBundled.grading (e p.1)) (sub_zero (p.2.val : ℤ))))
  exact E'.trans ((G.bundledIdempotentComponentEquiv (e p.1) p.2.val).trans
    (reconstructedCoordinateEquiv R hmul e he0 he F hneg h1 hsum horth m p))

/-- The coordinate comparison evaluates the projective map at its generator and reads one entry. -/
theorem intervalEvaluationCoordinateEquiv_apply (p : ι × Fin (m + 1))
    (f : (principalDegreeInclusion R hmul e he0).obj (intervalProjectiveLabel R hmul e he0 m p) ⟶
      (intervalReconstructedSupportedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).obj) :
    intervalEvaluationCoordinateEquiv R hmul e he0 he F hneg h1 hsum horth hfinite m p f =
      (show intervalCoordinateSpace R hmul e he0 F m from
        (f.val : (principalObject R hmul (e p.1) (he0 p.1)).module →ₗ[A]
          (intervalReconstructedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).module).toFun
            (principalGenerator (e p.1))) p := rfl

end MagnitudeConjecture.Graded.FiniteGradedModule
