import MagnitudeConjecture.Algebra.RightModuleStandardGradedDegreeBounds

/-! # Scalar endomorphisms and directedness of the graded representatives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance rdGradedDirectedQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance rdGradedDirectedArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- Every endomorphism of a shifted vertex module is scalar. -/
theorem standardFormGraded_end_scalar (X : S.StandardFormMeshCategory) (s : ℤ)
    (f : (⟨S.standardFormGradedVertexFunctor.obj X, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
      ⟨S.standardFormGradedVertexFunctor.obj X, s⟩) :
    ∃ c : k, f = c • 𝟙 (⟨S.standardFormGradedVertexFunctor.obj X, s⟩ :
      Graded.FiniteGradedModule.ShiftedModule) := by
  apply S.standardFormIntegerHomGrading.degreeFunctor_end_scalar
    Graded.FiniteGradedModule.homGrading S.standardFormGradedVertexFunctor
    (fun hf ↦ S.standardFormGradedVertexFunctor_homogeneous hf) _ ⟨X, s⟩ f
  intro Y
  change Graded.integerComponent
    (MeshCategory.lengthComponent S.standardFormRightMeshData Y.as Y.as) 0 =
      k ∙ (𝟙 (MeshCategory.obj (k := k) S.standardFormRightMeshData Y.as))
  simpa only [Graded.integerComponent, le_refl, if_true, Int.toNat_zero] using
    MeshCategory.lengthComponent_zero_self (k := k) S.standardFormRightMeshData Y.as

/-- Nonzero endomorphisms of a shifted representative are invertible. -/
theorem standardFormGraded_end_isIso (X : S.StandardFormMeshCategory) (s : ℤ)
    (f : (⟨S.standardFormGradedVertexFunctor.obj X, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
      ⟨S.standardFormGradedVertexFunctor.obj X, s⟩) (hf : f ≠ 0) : IsIso f := by
  obtain ⟨c, rfl⟩ := S.standardFormGraded_end_scalar X s f
  have hc : c ≠ 0 := by intro h; subst c; simp at hf
  refine ⟨⟨c⁻¹ • 𝟙 _, ?_, ?_⟩⟩
  · simp [Linear.comp_smul, smul_smul, hc]
  · simp [Linear.comp_smul, smul_smul, hc]

/-- Every nonzero nonisomorphism between graded representatives lowers the shift. -/
theorem standardFormGraded_noniso_descent (X Y : S.StandardFormMeshCategory) (s t : ℤ)
    (f : (⟨S.standardFormGradedVertexFunctor.obj X, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩)
    (hf : f ≠ 0) (hi : ¬ IsIso f) : t < s := by
  apply S.standardFormGraded_strict_descent X Y s t f hf
  by_contra h
  push Not at h
  rcases h with ⟨rfl, rfl⟩
  exact hi (S.standardFormGraded_end_isIso X s f hf)

/-- Nonzero nonisomorphism edges on the classified graded representatives. -/
def standardFormGradedEdge (X Y : GradedCategory.DegreeObject S.standardFormIntegerHomGrading) : Prop :=
  ∃ f : (⟨S.standardFormGradedVertexFunctor.obj X.obj, X.degree⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
    ⟨S.standardFormGradedVertexFunctor.obj Y.obj, Y.degree⟩, f ≠ 0 ∧ ¬ IsIso f

/-- The classified graded category has no cycle of nonzero nonisomorphisms. -/
theorem standardFormGraded_acyclic (X : GradedCategory.DegreeObject S.standardFormIntegerHomGrading) :
    ¬ Relation.TransGen S.standardFormGradedEdge X X := by
  have descent {Y Z} (h : Relation.TransGen S.standardFormGradedEdge Y Z) : Z.degree < Y.degree := by
    induction h with
    | single h =>
      obtain ⟨f, hf, hi⟩ := h
      exact S.standardFormGraded_noniso_descent _ _ _ _ f hf hi
    | tail h hlast ih =>
      obtain ⟨f, hf, hi⟩ := hlast
      exact lt_trans (S.standardFormGraded_noniso_descent _ _ _ _ f hf hi) ih
  intro h
  exact (lt_irrefl X.degree) (descent h)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
