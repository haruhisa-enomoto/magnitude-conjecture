import MagnitudeConjecture.CategoryTheory.GradedIntervalEvaluationIso
import MagnitudeConjecture.CategoryTheory.GradedIntervalReconstructionFunctor
import MagnitudeConjecture.CategoryTheory.ExtendSupportedIso

/-! # Evaluation of reconstruction on all degrees -/
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

/-- The interval inclusion is injective on objects. -/
theorem principalIntervalInclusion_op_injective (m : ℕ) :
    Function.Injective (principalIntervalInclusion R hmul e he0 m).op.obj := by
  intro p q h
  apply Opposite.unop_injective
  apply Prod.ext
  · exact congrArg (fun z ↦ z.unop.1) h
  · apply Fin.ext
    have hh := congrArg (fun z ↦ z.unop.2) h
    change (p.unop.2.val : ℤ) = q.unop.2.val at hh
    omega

/-- An object omitted by the interval inclusion has degree outside [0,m]. -/
theorem principalIntervalInclusion_outside (m : ℕ)
    (p : (PrincipalDegreeCategory R hmul e he0)ᵒᵖ)
    (hp : p ∉ Set.range (principalIntervalInclusion R hmul e he0 m).op.obj) :
    p.unop.2 < 0 ∨ (m : ℤ) < p.unop.2 := by
  by_contra hn
  have h0 : 0 ≤ p.unop.2 := by omega
  have hm : p.unop.2 ≤ m := by omega
  apply hp
  refine ⟨op (p.unop.1, ⟨p.unop.2.toNat, by omega⟩), ?_⟩
  apply Opposite.unop_injective
  apply Prod.ext
  · rfl
  · change (p.unop.2.toNat : ℤ) = p.unop.2
    omega

variable (F : (PrincipalDegreeCategory R hmul e he0)ᵒᵖ ⥤ ModuleCat.{u} k)
variable [F.Additive] [F.Linear k]
variable (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
variable (h1 : (1 : A) ∈ R.component 0) (hsum : ∑ i, e i = 1)
variable (horth : Pairwise fun i j ↦ e i * e j = 0)
variable (hfinite : ∀ p, FiniteDimensional k (F.obj p)) (m : ℕ)
variable (hzero : ∀ p, p ∈ principalOutsideInterval R hmul e he0 m → Limits.IsZero (F.obj p))

/-- Evaluation after reconstruction recovers the whole supported representation. -/
def supportedEvaluationReconstructionIso :
    CoveringHom.restrictedLinearYoneda (k := k) (principalDegreeInclusion R hmul e he0)
      (intervalReconstructedSupportedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).obj ≅ F := by
  let I := (principalIntervalInclusion R hmul e he0 m).op
  letI : I.Full := by dsimp [I, principalIntervalInclusion]; infer_instance
  apply extendSupportedIso I (principalIntervalInclusion_op_injective R hmul e he0 m) _ F
    (intervalEvaluationReconstructionIso R hmul e he0 he F hneg h1 hsum horth hfinite m)
  · intro p hp
    exact principalEvaluation_zero_outside R hmul e he0 he _
      (intervalReconstructedSupportedObject R hmul e he0 he F hneg h1 hsum horth hfinite m).property
      p.unop (principalIntervalInclusion_outside R hmul e he0 m p hp)
  · intro p hp
    exact hzero p (principalIntervalInclusion_outside R hmul e he0 m p hp)

/-- On an interval object the extended comparison is the original coordinate comparison. -/
theorem supportedEvaluationReconstructionIso_app_interval (p : ι × Fin (m + 1)) :
    (supportedEvaluationReconstructionIso R hmul e he0 he F hneg h1 hsum horth hfinite m hzero).app
      (op (intervalProjectiveLabel R hmul e he0 m p)) =
      (intervalEvaluationCoordinateEquiv R hmul e he0 he F hneg h1 hsum horth hfinite m p).toModuleIso := by
  change supportedExtensionIsoAt _ _ _ _ _ _
    ((principalIntervalInclusion R hmul e he0 m).op.obj (op p)) = _
  rw [supportedExtensionIsoAt_image _ (principalIntervalInclusion_op_injective R hmul e he0 m)]
  rfl

end MagnitudeConjecture.Graded.FiniteGradedModule
