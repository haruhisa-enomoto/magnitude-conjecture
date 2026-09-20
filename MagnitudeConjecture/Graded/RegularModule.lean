import MagnitudeConjecture.Graded.ModuleHomGrading
import MagnitudeConjecture.Graded.GradedSubmodule

/-! # Evaluation on the graded regular module -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded.VectorGrading
variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable (R : VectorGrading k A)
variable (hmul : ∀ {i j : ℤ} {a b : A}, a ∈ R.component i → b ∈ R.component j →
  a * b ∈ R.component (i + j))

/-- The algebra grading regarded as the grading of the left regular module. -/
def regularModuleGrading : ModuleGrading (M := A) R where
  toVectorGrading := R
  smul_mem := hmul

variable {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable (G : ModuleGrading (M := M) R)

/-- Evaluation at one detects the degree of a map out of the regular module. -/
theorem regular_homogeneous_iff (h1 : (1 : A) ∈ R.component 0) (d : ℤ) (f : A →ₗ[A] M) :
    (R.regularModuleGrading hmul).Homogeneous G d f ↔ f 1 ∈ G.component d := by
  constructor
  · intro h
    simpa only [zero_add] using h 0 1 h1
  · intro h i a ha
    have hx := G.smul_mem ha h
    simpa only [← f.map_smul, smul_eq_mul, mul_one] using hx

/-- Homogeneous maps out of the regular module are exactly homogeneous vectors. -/
def regularHomEquiv (h1 : (1 : A) ∈ R.component 0) (d : ℤ) :
    (R.regularModuleGrading hmul).homComponent G d ≃ₗ[k] G.component d where
  toFun f := ⟨f.val 1, (R.regular_homogeneous_iff hmul G h1 d f.val).mp f.property⟩
  invFun x := ⟨LinearMap.toSpanSingleton A M x.val,
    (R.regular_homogeneous_iff hmul G h1 d _).mpr (by simpa using x.property)⟩
  left_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    change a • f.val 1 = f.val a
    rw [← f.val.map_smul, smul_eq_mul, mul_one]
  right_inv x := by apply Subtype.ext; exact one_smul A x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end MagnitudeConjecture.Graded.VectorGrading
