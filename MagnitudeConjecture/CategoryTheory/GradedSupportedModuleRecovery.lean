import MagnitudeConjecture.CategoryTheory.GradedSupportedModuleCoordinateAction
import MagnitudeConjecture.CategoryTheory.GradedHomInverse

/-! # Recovering the actual supported graded module -/
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

/-- The coordinate equivalence is an equivalence of actual algebra modules. -/
def supportedModuleRecoveryLinearEquiv : X.obj.obj.module ≃ₗ[A]
    ((supportedIntervalReconstructionFunctor R hmul e he0 he hneg h1 hsum horth m).obj
      ((principalSupportedEvaluationFunctor R hmul e he0 he m).obj X)).obj.obj.module :=
  { supportedModuleCoordinateEquiv R hmul e he0 he hsum horth m X with
    map_smul' := fun a x ↦ supportedModuleCoordinateEquiv_smul R hmul e he0 he hsum horth m X a x }

/-- The recovery map preserves physical degrees, including the external shift on the original module. -/
def supportedModuleRecoveryMap : X ⟶
    (principalSupportedEvaluationFunctor R hmul e he0 he m ⋙
      supportedIntervalReconstructionFunctor R hmul e he0 he hneg h1 hsum horth m).obj X := by
  apply ObjectProperty.homMk
  refine ⟨(supportedModuleRecoveryLinearEquiv R hmul e he0 he hsum horth m X hneg h1).toLinearMap, ?_⟩
  intro d x hx p hp
  change (p.2.val : ℤ) ≠ d + (X.obj.degree - 0) at hp
  change supportedModuleCoordinateEquiv R hmul e he0 he hsum horth m X x p = 0
  apply (principalShiftHomEquiv R hmul (e p.1) (he p.1) (he0 p.1) p.2.val X.obj).injective
  apply Subtype.ext
  rw [supportedModuleCoordinateEquiv_evaluation, map_zero]
  exact X.obj.obj.grading.idempotentProjection_of_degree_ne (e p.1) (by omega) x hx

/-- Recovery is an isomorphism in the supported graded category. -/
def supportedModuleRecoveryIso : X ≅
    (principalSupportedEvaluationFunctor R hmul e he0 he m ⋙
      supportedIntervalReconstructionFunctor R hmul e he0 he hneg h1 hsum horth m).obj X := by
  let f := supportedModuleRecoveryMap R hmul e he0 he hsum horth m X hneg h1
  let E := supportedModuleRecoveryLinearEquiv R hmul e he0 he hsum horth m X hneg h1
  letI : IsIso f.hom.val := ⟨⟨E.symm.toLinearMap,
    LinearMap.ext E.symm_apply_apply, LinearMap.ext E.apply_symm_apply⟩⟩
  letI : IsIso f.hom := (homGrading (R := R)).isIso_of_underlying_isIso f.hom
  letI : IsIso f := (ObjectProperty.isIso_hom_iff f).mp inferInstance
  exact asIso f

end MagnitudeConjecture.Graded.FiniteGradedModule
