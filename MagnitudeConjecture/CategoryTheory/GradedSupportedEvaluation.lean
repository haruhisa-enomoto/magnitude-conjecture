import MagnitudeConjecture.CategoryTheory.GradedProjectiveDetection
import MagnitudeConjecture.CategoryTheory.GradedSupportedCategory
import MagnitudeConjecture.CategoryTheory.ObjectDeletionModuleAdjoints

/-! # Evaluation from supported graded modules to supported projective representations -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type v} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)

/-- Projective degrees deleted when retaining [0,m]. -/
def principalOutsideInterval (m : ℕ) : Set (PrincipalDegreeCategory R hmul e he0)ᵒᵖ :=
  {p | p.unop.2 < 0 ∨ (m : ℤ) < p.unop.2}

/-- The forward representation functor with both interval-support conditions bundled. -/
def principalSupportedEvaluationFunctor (m : ℕ) : SupportedCategory (R := R) m ⥤
    ObjectDeletion.VanishingFiniteModuleCategory (k := k)
      (PrincipalDegreeCategory R hmul e he0)ᵒᵖ (principalOutsideInterval R hmul e he0 m) :=
  (ObjectDeletion.finiteModuleVanishesOnDeleted (k := k) _
    (principalOutsideInterval R hmul e he0 m)).lift
    ((intervalSupport (R := R) m).ι ⋙ principalEvaluationFunctor R hmul e he0 he)
    (fun X p hp ↦ principalEvaluation_zero_outside R hmul e he0 he X.obj X.property p.unop hp)

instance principalSupportedEvaluationFunctor_additive (m : ℕ) :
    (principalSupportedEvaluationFunctor R hmul e he0 he m).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    exact (principalEvaluationFunctor R hmul e he0 he).map_add

instance principalSupportedEvaluationFunctor_linear (m : ℕ) :
    (principalSupportedEvaluationFunctor R hmul e he0 he m).Linear k where
  map_smul := by
    intro X Y f c
    apply ObjectProperty.hom_ext
    exact (principalEvaluationFunctor R hmul e he0 he).map_smul c f.hom

/-- A complete idempotent family still detects maps after imposing interval support. -/
theorem principalSupportedEvaluation_faithful (hsum : ∑ i, e i = 1) (m : ℕ) :
    (principalSupportedEvaluationFunctor R hmul e he0 he m).Faithful where
  map_injective := by
    intro X Y f g hfg
    apply ObjectProperty.hom_ext
    apply (principalEvaluation_faithful R hmul e he0 he hsum).map_injective
    exact congrArg (fun f ↦ f.hom) hfg

end MagnitudeConjecture.Graded.FiniteGradedModule
