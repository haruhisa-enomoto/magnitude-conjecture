import MagnitudeConjecture.Graded.IntervalCornerCoefficients
import MagnitudeConjecture.CategoryTheory.GradedProjectiveCornerCategory

/-! # Algebra elements as matrices of interval projective morphisms -/
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

/-- An interval coordinate as a degree-labelled projective. -/
def intervalProjectiveLabel (m : ℕ) (p : ι × Fin (m + 1)) :
    PrincipalDegreeCategory R hmul e he0 := (p.1, p.2.val)

/-- The homogeneous corner coefficient regarded as a projective morphism. -/
def intervalActionCoefficient (m : ℕ) (p q : ι × Fin (m + 1)) :
    A →ₗ[k] (intervalProjectiveLabel R hmul e he0 m p ⟶ intervalProjectiveLabel R hmul e he0 m q) := by
  let C : A →ₗ[k] cornerComponent R (e p.1) (e q.1) ((p.2.val : ℤ) - q.2.val) :=
    { toFun := fun a ↦ ⟨intervalCorner R e m p q a, intervalCorner_mem R e hmul he0 he m p q a⟩
      map_add' := fun a b ↦ Subtype.ext (intervalCorner_add R e m p q a b)
      map_smul' := fun c a ↦ Subtype.ext (intervalCorner_smul R e m p q c a) }
  exact (principalDegreeHomEquiv R hmul e he0 he _ _).symm.toLinearMap.comp C

@[simp]
theorem intervalActionCoefficient_coord (m : ℕ) (p q : ι × Fin (m + 1)) (a : A) :
    (principalDegreeHomEquiv R hmul e he0 he _ _
      (intervalActionCoefficient R hmul e he0 he m p q a)).val = intervalCorner R e m p q a := by
  simp only [intervalActionCoefficient, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rfl

/-- Matrix multiplication is represented by composition through the interval projectives. -/
theorem intervalActionCoefficient_mul (hneg : ∀ d : ℤ, d < 0 → R.component d = ⊥)
    (hsum : ∑ i, e i = 1) (m : ℕ) (p q : ι × Fin (m + 1)) (a b : A) :
    intervalActionCoefficient R hmul e he0 he m p q (a * b) =
      ∑ z : ι × Fin (m + 1), intervalActionCoefficient R hmul e he0 he m p z a ≫
        intervalActionCoefficient R hmul e he0 he m z q b := by
  apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
  rw [map_sum]
  apply Subtype.ext
  simp only [Submodule.coe_sum, intervalActionCoefficient_coord, principalDegreeHomEquiv_comp]
  exact intervalCorner_mul R e hmul he hneg hsum m p q a b

/-- The diagonal coefficient of 1 is the identity. -/
theorem intervalActionCoefficient_one_self (h1 : (1 : A) ∈ R.component 0)
    (horth : Pairwise fun i j ↦ e i * e j = 0) (m : ℕ) (p : ι × Fin (m + 1)) :
    intervalActionCoefficient R hmul e he0 he m p p 1 = 𝟙 _ := by
  apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
  apply Subtype.ext
  rw [intervalActionCoefficient_coord, principalDegreeHomEquiv_id]
  simpa [intervalProjectiveLabel] using intervalCorner_one R e he h1 horth m p p

/-- The off-diagonal coefficients of 1 vanish. -/
theorem intervalActionCoefficient_one_ne (h1 : (1 : A) ∈ R.component 0)
    (horth : Pairwise fun i j ↦ e i * e j = 0) (m : ℕ) (p q : ι × Fin (m + 1))
    (hpq : p ≠ q) : intervalActionCoefficient R hmul e he0 he m p q 1 = 0 := by
  apply (principalDegreeHomEquiv R hmul e he0 he _ _).injective
  rw [map_zero]
  apply Subtype.ext
  rw [intervalActionCoefficient_coord]
  change intervalCorner R e m p q 1 = 0
  simpa only [if_neg hpq] using intervalCorner_one R e he h1 horth m p q

end MagnitudeConjecture.Graded.FiniteGradedModule
