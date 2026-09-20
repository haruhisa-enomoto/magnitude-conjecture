import MagnitudeConjecture.CategoryTheory.GradedSupportedModuleUnit
import MagnitudeConjecture.CategoryTheory.GradedSupportedEvaluationCounit

/-! # Supported graded modules and supported projective representations -/
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
variable (m : ℕ)

variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥) (h1 : (1 : A) ∈ R.component 0)

/-- Actual graded modules supported in [0,m] are equivalent to supported projective representations. -/
def supportedProjectiveRepresentationEquivalence : SupportedCategory (R := R) m ≌
    ObjectDeletion.VanishingFiniteModuleCategory (k := k)
      (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m) :=
  CategoryTheory.Equivalence.mk
    (principalSupportedEvaluationFunctor R hmul e he0 he m)
    (supportedIntervalReconstructionFunctor R hmul e he0 he hneg h1 hsum horth m)
    (supportedModuleRecoveryUnit R hmul e he0 he hsum horth m hneg h1)
    (supportedEvaluationReconstructionCounit R hmul e he0 he hneg h1 hsum horth m)

instance supportedProjectiveRepresentationEquivalence_additive :
    (supportedProjectiveRepresentationEquivalence R hmul e he0 he hsum horth m hneg h1).functor.Additive := by
  change (principalSupportedEvaluationFunctor R hmul e he0 he m).Additive
  infer_instance

instance supportedProjectiveRepresentationEquivalence_linear :
    (supportedProjectiveRepresentationEquivalence R hmul e he0 he hsum horth m hneg h1).functor.Linear k := by
  change (principalSupportedEvaluationFunctor R hmul e he0 he m).Linear k
  infer_instance

end MagnitudeConjecture.Graded.FiniteGradedModule
