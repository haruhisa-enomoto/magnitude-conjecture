import MagnitudeConjecture.Algebra.RightModuleStandardGradedHom

/-! # Uniform degree bounds and strict descent between graded representatives -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance rdGradedDegreeBoundsQuiver : Quiver (Fin S.n) := S.standardFormQuiver
noncomputable local instance rdGradedDegreeBoundsArrowFintype (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

/-- One positive finite bound controls all nonzero homogeneous mesh maps. -/
theorem standardFormGraded_uniform_bound : ∃ h : ℕ, 1 ≤ h ∧
    ∀ X Y : S.StandardFormMeshCategory, ∀ d : ℤ,
      d < 0 ∨ (h : ℤ) < d → S.standardFormIntegerHomGrading.component X Y d = ⊥ := by
  obtain ⟨n, hn⟩ := MeshCategory.exists_uniform_lengthComponent_cutoff
    (k := k) S.standardFormRightMeshData (fun x y ↦ S.standardFormMeshHomFinite _ _)
  refine ⟨n + 1, by omega, ?_⟩
  intro X Y d hd
  change Graded.integerComponent (MeshCategory.lengthComponent S.standardFormRightMeshData X.as Y.as) d = ⊥
  by_cases h : 0 ≤ d
  · rw [Graded.integerComponent, if_pos h]
    exact hn X.as Y.as d.toNat (by omega)
  · simp [Graded.integerComponent, h]

/-- Distinct vertices have no degree-zero maps. -/
theorem standardFormGraded_zero_of_ne (X Y : S.StandardFormMeshCategory) (h : X ≠ Y) :
    S.standardFormIntegerHomGrading.component X Y 0 = ⊥ := by
  change Graded.integerComponent (MeshCategory.lengthComponent S.standardFormRightMeshData X.as Y.as) 0 = ⊥
  rw [show (0 : ℤ) = (0 : ℕ) by rfl, Graded.integerComponent_nat]
  apply MeshCategory.lengthComponent_zero_eq_bot_of_ne
  intro he
  apply h
  cases X
  cases Y
  cases he
  rfl

/-- A nonzero map between distinct shifted representatives strictly decreases shift. -/
theorem standardFormGraded_strict_descent (X Y : S.StandardFormMeshCategory) (s t : ℤ)
    (f : (⟨S.standardFormGradedVertexFunctor.obj X, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ⟶
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩)
    (hf : f ≠ 0) (hXY : X ≠ Y ∨ s ≠ t) : t < s := by
  obtain ⟨h, _, hb⟩ := S.standardFormGraded_uniform_bound
  let e := S.standardFormGradedHomEquiv X Y s t
  let g : (⟨X, s⟩ : GradedCategory.DegreeObject S.standardFormIntegerHomGrading) ⟶ ⟨Y, t⟩ :=
    e.symm f
  have hg : g ≠ 0 := by
    intro hz
    apply hf
    apply e.symm.injective
    simpa only [map_zero] using hz
  apply S.standardFormIntegerHomGrading.degree_strict_of_ne_zero_of_ne
    h hb S.standardFormGraded_zero_of_ne g hg
  intro he
  have ho := congrArg GradedCategory.DegreeObject.obj he
  have hs := congrArg GradedCategory.DegreeObject.degree he
  rcases hXY with hXY | hXY
  · exact hXY ho
  · exact hXY hs

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
