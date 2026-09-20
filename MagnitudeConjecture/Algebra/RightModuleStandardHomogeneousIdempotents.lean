import MagnitudeConjecture.Algebra.RightModuleStandardGradedSupport
import MagnitudeConjecture.CategoryTheory.GradedGeneratorIdempotents

/-! # Homogeneous complete idempotents in the actual standard form -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardIntervalMeshHomFinite (X Y : S.StandardFormMeshCategory) :
    FiniteDimensional k (X ⟶ Y) := S.standardFormMeshHomFinite X Y

/-- The standard-form grading is multiplicative. -/
theorem standardFormOppositeAlgebra_mul_mem {i j : ℤ}
    {a b : (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ}
    (ha : a ∈ (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite).component i)
    (hb : b ∈ (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite).component j) :
    a * b ∈ (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite).component (i + j) := by
  change (S.standardFormOppositeGeneratorAlgEquiv S.standardFormMeshHomFinite) (a * b) ∈
    (S.standardGradedGeneratorAlgebraGrading S.standardFormMeshHomFinite).component (i + j)
  rw [map_mul]
  exact (S.standardFormAdditiveHomGrading S.standardFormMeshHomFinite).generatorAlgebra_mul_mem
    S.standardGradedProjectiveFamily ha hb

/-- The unit of the standard-form algebra is homogeneous of degree zero. -/
theorem standardFormOppositeAlgebra_one_mem :
    (1 : (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ) ∈
      (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite).component 0 := by
  change (S.standardFormOppositeGeneratorAlgEquiv S.standardFormMeshHomFinite) 1 ∈
    (S.standardGradedGeneratorAlgebraGrading S.standardFormMeshHomFinite).component 0
  rw [map_one]
  exact (S.standardFormAdditiveHomGrading S.standardFormMeshHomFinite).generatorAlgebra_one_mem
    S.standardGradedProjectiveFamily

/-- Negative degrees vanish in the actual standard-form algebra grading. -/
theorem standardFormOppositeAlgebra_negative (d : ℤ) (hd : d < 0) :
    (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite).component d = ⊥ := by
  obtain ⟨h, hh, hb⟩ := S.standardFormGraded_uniform_bound
  have hmat (X Y : Mat_ S.StandardFormMeshCategory) :
      (S.standardFormAdditiveHomGrading S.standardFormMeshHomFinite).component X Y d = ⊥ := by
    apply bot_unique
    intro f hf
    change f = 0
    apply Mat_.hom_ext
    intro i j
    have h := hf i (Set.mem_univ i) j (Set.mem_univ j)
    change f i j ∈ S.standardFormIntegerHomGrading.component (X.X i) (Y.X j) d at h
    rw [hb _ _ d (Or.inl hd)] at h
    exact h
  have hgen := (S.standardFormAdditiveHomGrading S.standardFormMeshHomFinite).generatorAlgebra_component_eq_bot
    S.standardGradedProjectiveFamily d (fun i j ↦ hmat _ _)
  apply bot_unique
  intro a ha
  change a = 0
  apply (S.standardFormOppositeGeneratorAlgEquiv S.standardFormMeshHomFinite).injective
  rw [map_zero]
  change (S.standardFormOppositeGeneratorAlgEquiv S.standardFormMeshHomFinite) a ∈
    (S.standardGradedGeneratorAlgebraGrading S.standardFormMeshHomFinite).component d at ha
  change (S.standardGradedGeneratorAlgebraGrading S.standardFormMeshHomFinite).component d = ⊥ at hgen
  rw [hgen] at ha
  exact ha

/-- The complete projective-summand idempotents transported to the standard form. -/
def standardFormHomogeneousIdempotent (p : S.StandardFormProjectiveMeshCategory) :
    (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  (S.standardFormOppositeGeneratorAlgEquiv S.standardFormMeshHomFinite).symm
    (GradedCategory.HomGrading.generatorIdempotent S.standardGradedProjectiveFamily p)

/-- Each transported idempotent has degree zero. -/
theorem standardFormHomogeneousIdempotent_mem_zero (p : S.StandardFormProjectiveMeshCategory) :
    S.standardFormHomogeneousIdempotent p ∈
      (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite).component 0 := by
  change (S.standardFormOppositeGeneratorAlgEquiv S.standardFormMeshHomFinite)
    ((S.standardFormOppositeGeneratorAlgEquiv S.standardFormMeshHomFinite).symm
      (GradedCategory.HomGrading.generatorIdempotent S.standardGradedProjectiveFamily p)) ∈
        (S.standardGradedGeneratorAlgebraGrading S.standardFormMeshHomFinite).component 0
  rw [AlgEquiv.apply_symm_apply]
  exact (S.standardFormAdditiveHomGrading S.standardFormMeshHomFinite).generatorIdempotent_mem_zero
    S.standardGradedProjectiveFamily p

/-- The transported elements are idempotent. -/
theorem standardFormHomogeneousIdempotent_idempotent (p : S.StandardFormProjectiveMeshCategory) :
    S.standardFormHomogeneousIdempotent p * S.standardFormHomogeneousIdempotent p =
      S.standardFormHomogeneousIdempotent p := by
  unfold standardFormHomogeneousIdempotent
  rw [← map_mul, GradedCategory.HomGrading.generatorIdempotent_idempotent]

/-- The transported family is orthogonal. -/
theorem standardFormHomogeneousIdempotent_orthogonal : Pairwise fun p q ↦
    S.standardFormHomogeneousIdempotent p * S.standardFormHomogeneousIdempotent q = 0 := by
  intro p q hpq
  unfold standardFormHomogeneousIdempotent
  rw [← map_mul, GradedCategory.HomGrading.generatorIdempotent_orthogonal _ hpq, map_zero]

/-- The transported family is complete. -/
theorem sum_standardFormHomogeneousIdempotent : ∑ p, S.standardFormHomogeneousIdempotent p = 1 := by
  unfold standardFormHomogeneousIdempotent
  rw [← map_sum, GradedCategory.HomGrading.sum_generatorIdempotent (k := k), map_one]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
