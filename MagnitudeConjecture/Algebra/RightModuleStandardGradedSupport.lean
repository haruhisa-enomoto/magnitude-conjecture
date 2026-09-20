import MagnitudeConjecture.Algebra.RightModuleStandardGradedDegreeBounds
import MagnitudeConjecture.Graded.ShiftRigidity

/-! # Uniform support bounds for the actual standard-form graded modules -/
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

/-- A vanishing mesh degree also vanishes in every represented graded module. -/
theorem standardFormGradedObject_component_eq_bot
    (d : ℤ) (hd : ∀ X Y : S.StandardFormMeshCategory,
      S.standardFormIntegerHomGrading.component X Y d = ⊥)
    (X : Mat_ S.StandardFormMeshCategory) :
    (S.standardFormGradedObject S.standardFormMeshHomFinite X).grading.component d = ⊥ := by
  apply bot_unique
  intro f hf
  change f = 0
  change (f : ⨁ S.standardGradedProjectiveFamily ⟶ X) = 0
  apply biproduct.hom_ext'
  intro p
  apply Mat_.hom_ext
  intro i j
  have h := hf p (Set.mem_univ p) i (Set.mem_univ i) j (Set.mem_univ j)
  change (biproduct.ι S.standardGradedProjectiveFamily p ≫ f) i j ∈
    S.standardFormIntegerHomGrading.component ((S.standardGradedProjectiveFamily p).X i) (X.X j) d at h
  rw [hd] at h
  rw [comp_zero]
  exact h

/-- A single positive bound contains the support of every standard-form graded vertex. -/
theorem standardFormGraded_support_bound : ∃ h : ℕ, 1 ≤ h ∧
    ∀ X : S.StandardFormMeshCategory, ∀ d : ℤ,
      d ∈ (S.standardFormGradedVertex S.standardFormMeshHomFinite X).grading.toVectorGrading.support →
        0 ≤ d ∧ d ≤ h := by
  obtain ⟨h, hh, hb⟩ := S.standardFormGraded_uniform_bound
  refine ⟨h, hh, ?_⟩
  intro X d hd
  have hn := ((S.standardFormGradedVertex S.standardFormMeshHomFinite X).grading.toVectorGrading.mem_support_iff d).mp hd
  by_contra hout
  have ho : d < 0 ∨ (h : ℤ) < d := by omega
  exact hn (S.standardFormGradedObject_component_eq_bot d (fun U V ↦ hb U V d ho) _)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
