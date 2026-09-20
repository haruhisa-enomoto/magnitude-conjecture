import MagnitudeConjecture.CategoryTheory.GradedProjectiveRepresentation

/-! # A complete homogeneous idempotent family detects graded maps -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.Graded.FiniteGradedModule
universe u v
variable {k A : Type u} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))
variable {ι : Type v} [Fintype ι] (e : ι → A)
variable (he0 : ∀ i, e i ∈ R.component 0) (he : ∀ i, e i * e i = e i)
variable (hsum : ∑ i, e i = 1)
include hsum he

/-- A nonzero graded map remains nonzero after precomposition by some shifted projective. -/
theorem principalEvaluation_detect {X Y : ShiftedModule.{u,u} (R := R)}
    (f : X ⟶ Y) (hf : f ≠ 0) :
    ∃ (p : PrincipalDegreeCategory R hmul e he0)
      (g : (principalDegreeInclusion R hmul e he0).obj p ⟶ X), g ≫ f ≠ 0 := by
  classical
  let l : X.obj.module →ₗ[A] Y.obj.module := f.val
  have hx : ∃ d : ℤ, ∃ x : X.obj.module, x ∈ X.obj.grading.component d ∧ l x ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hf
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rw [← X.obj.grading.toVectorGrading.sum_projection x, map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    exact hn d _ (X.obj.grading.toVectorGrading.projection_mem d x)
  obtain ⟨d, x, hx, hfx⟩ := hx
  have hi : ∃ i, l (e i • x) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hfx
    have h : ∑ i, e i • x = x := by rw [← Finset.sum_smul, hsum, one_smul]
    rw [← h, map_sum]
    exact Finset.sum_eq_zero (fun i _ ↦ hn i)
  obtain ⟨i, hi⟩ := hi
  let r := d + X.degree
  let v : idempotentComponent R X.obj.grading (e i) (r - X.degree) :=
    ⟨e i • x, ⟨by
      have h := X.obj.grading.smul_mem (he0 i) hx
      simpa only [zero_add, r, add_sub_cancel_right] using h,
      by rw [← mul_smul, he i]⟩⟩
  let E := principalShiftHomEquiv R hmul (e i) (he i) (he0 i) r X
  let g := E.symm v
  refine ⟨(i, r), g, ?_⟩
  intro hz
  have hg : (g.val : (principalObject R hmul (e i) (he0 i)).module →ₗ[A] X.obj.module).toFun (principalGenerator (e i)) = e i • x :=
    congrArg Subtype.val (E.apply_symm_apply v)
  have hh := LinearMap.congr_fun (congrArg Subtype.val hz) (principalGenerator (e i))
  change l ((g.val : (principalObject R hmul (e i) (he0 i)).module →ₗ[A] X.obj.module).toFun (principalGenerator (e i))) = 0 at hh
  rw [hg] at hh
  exact hi hh

/-- The resulting finite contravariant representation remembers every graded module map. -/
theorem principalEvaluation_faithful : (principalEvaluationFunctor R hmul e he0 he).Faithful :=
  CoveringHom.finiteSupportRestrictedLinearYonedaFunctor_faithful_of_sourceDetection
    (principalDegreeInclusion R hmul e he0) (principalEvaluation_finite R hmul e he0 he)
    (fun f hf ↦ principalEvaluation_detect R hmul e he0 he hsum f hf)

end MagnitudeConjecture.Graded.FiniteGradedModule
