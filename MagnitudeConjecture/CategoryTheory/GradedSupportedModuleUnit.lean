import MagnitudeConjecture.CategoryTheory.GradedSupportedModuleRecovery
import MagnitudeConjecture.Graded.ProjectionNaturality

/-! # The module-side inverse natural isomorphism -/
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

variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥) (h1 : (1 : A) ∈ R.component 0)

/-- Evaluation followed by reconstruction recovers the actual supported graded module naturally. -/
def supportedModuleRecoveryUnit : 𝟭 (SupportedCategory (R := R) m) ≅
    principalSupportedEvaluationFunctor R hmul e he0 he m ⋙
      supportedIntervalReconstructionFunctor R hmul e he0 he hneg h1 hsum horth m :=
  NatIso.ofComponents
    (fun X ↦ supportedModuleRecoveryIso R hmul e he0 he hsum horth m X hneg h1)
    (by
      intro X Y f
      apply ObjectProperty.hom_ext
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      funext p
      apply (principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val Y.obj).injective
      apply Subtype.ext
      change (principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val Y.obj
        (supportedModuleCoordinateEquiv R hmul e he0 he hsum horth m Y
          ((f.hom.val : X.obj.obj.module →ₗ[A] Y.obj.obj.module).toFun x) p)).val =
        (f.hom.val : X.obj.obj.module →ₗ[A] Y.obj.obj.module).toFun
          (principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val X.obj
            (supportedModuleCoordinateEquiv R hmul e he0 he hsum horth m X x p)).val
      rw [supportedModuleCoordinateEquiv_evaluation, supportedModuleCoordinateEquiv_evaluation]
      have h := X.obj.obj.grading.idempotentProjection_map Y.obj.obj.grading
        (f.hom.val : X.obj.obj.module →ₗ[A] Y.obj.obj.module)
        (X.obj.degree - Y.obj.degree) f.hom.property (e p.1)
        ((p.2.val : ℤ) - X.obj.degree) x
      have hd : (p.2.val : ℤ) - X.obj.degree + (X.obj.degree - Y.obj.degree) =
          p.2.val - Y.obj.degree := by omega
      rw [hd] at h
      exact h)

end MagnitudeConjecture.Graded.FiniteGradedModule
