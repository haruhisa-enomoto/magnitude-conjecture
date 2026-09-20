import MagnitudeConjecture.CategoryTheory.GradedProjectiveEvaluation
import MagnitudeConjecture.CategoryTheory.RestrictedYoneda

/-! # Finite contravariant representations obtained from graded projective evaluation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Opposite
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type v} (e : ι → A) (he0 : ∀ i, e i ∈ R.component 0)

/-- All shifts of the selected homogeneous principal projectives. -/
def principalDegreeObject (p : ι × ℤ) : ShiftedModule.{u,u} (R := R) :=
  ⟨principalObject R hmul (e p.1) (he0 p.1), p.2⟩

abbrev PrincipalDegreeCategory :=
  InducedCategory (ShiftedModule.{u,u} (R := R)) (principalDegreeObject R hmul e he0)

/-- The full inclusion of the degree-labelled projective family. -/
def principalDegreeInclusion : PrincipalDegreeCategory R hmul e he0 ⥤
    ShiftedModule.{u,u} (R := R) := inducedFunctor (principalDegreeObject R hmul e he0)

instance principalDegreeInclusion_additive : (principalDegreeInclusion R hmul e he0).Additive := by
  unfold principalDegreeInclusion
  infer_instance
instance principalDegreeInclusion_linear : (principalDegreeInclusion R hmul e he0).Linear k := by
  unfold principalDegreeInclusion
  infer_instance

variable [Fintype ι] (he : ∀ i, e i * e i = e i)
include he

/-- Only finitely many shifted projectives see any fixed finite graded module. -/
theorem principalEvaluation_finiteSupport (X : ShiftedModule.{u,u} (R := R)) :
    {p : (PrincipalDegreeCategory R hmul e he0)ᵒᵖ |
      Nontrivial ((principalDegreeInclusion R hmul e he0).obj p.unop ⟶ X)}.Finite := by
  classical
  let D : Finset (PrincipalDegreeCategory R hmul e he0)ᵒᵖ :=
    (Finset.univ.product (shiftedSupport X)).image fun p ↦ op p
  apply D.finite_toSet.subset
  intro p hp
  have hr : p.unop.2 ∈ shiftedSupport X := by
    by_contra hn
    letI : Nontrivial ((principalDegreeInclusion R hmul e he0).obj p.unop ⟶ X) := hp
    obtain ⟨f, hf⟩ := exists_ne (0 : (principalDegreeInclusion R hmul e he0).obj p.unop ⟶ X)
    exact hf (principalHom_eq_zero_of_not_mem R hmul (e p.unop.1) (he p.unop.1)
      (he0 p.unop.1) X p.unop.2 hn f)
  exact Finset.mem_image.mpr ⟨p.unop, Finset.mem_product.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩

theorem principalEvaluation_finite (X : ShiftedModule.{u,u} (R := R)) :
    CoveringHom.IsFiniteDimensionalModule k
      (CoveringHom.restrictedLinearYonedaLinearModule (k := k)
        (principalDegreeInclusion R hmul e he0) X) :=
  CoveringHom.restrictedLinearYoneda_isFiniteDimensional_of_finite_support
    (principalDegreeInclusion R hmul e he0) X (fun _ ↦ inferInstance)
    (principalEvaluation_finiteSupport R hmul e he0 he X)

/-- A graded module gives a finite-dimensional contravariant representation on shifted projectives. -/
def principalEvaluationFunctor : ShiftedModule.{u,u} (R := R) ⥤
    CoveringHom.FiniteDimensionalModuleCategory
      (C := (PrincipalDegreeCategory R hmul e he0)ᵒᵖ) k :=
  CoveringHom.finiteSupportRestrictedLinearYonedaFunctor
    (principalDegreeInclusion R hmul e he0) (principalEvaluation_finite R hmul e he0 he)

instance principalEvaluationFunctor_additive :
    (principalEvaluationFunctor R hmul e he0 he).Additive := by
  unfold principalEvaluationFunctor
  infer_instance

instance principalEvaluationFunctor_linear :
    (principalEvaluationFunctor R hmul e he0 he).Linear k := by
  unfold principalEvaluationFunctor
  infer_instance

/-- A supported module evaluates to zero on projective degrees outside the interval. -/
theorem principalEvaluation_zero_outside {m : ℕ} (X : ShiftedModule.{u,u} (R := R))
    (hX : SupportedIn m X) (p : PrincipalDegreeCategory R hmul e he0)
    (hp : p.2 < 0 ∨ (m : ℤ) < p.2) :
    Limits.IsZero (((principalEvaluationFunctor R hmul e he0 he).obj X).obj.obj.obj (op p)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro f g
  exact (principalHom_eq_zero_outside R hmul (e p.1) (he p.1) (he0 p.1) X hX p.2 hp f).trans
    (principalHom_eq_zero_outside R hmul (e p.1) (he p.1) (he0 p.1) X hX p.2 hp g).symm

end MagnitudeConjecture.Graded.FiniteGradedModule
