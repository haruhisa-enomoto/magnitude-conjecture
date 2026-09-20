import MagnitudeConjecture.Algebra.RightModuleStandardGradedClassification
import MagnitudeConjecture.CategoryTheory.GradedModuleDecomposition
import MagnitudeConjecture.CategoryTheory.GradedShiftFunctor

/-! # Decompositions into shifted standard-form representatives -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Classification also applies when an arbitrary external shift is already present. -/
theorem standardFormGraded_shifted_exists_iso
    (M : Graded.FiniteGradedModule.ShiftedModule
      (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite))
    (hM : Indecomposable M) :
    ∃ i : Fin S.n, ∃ s : ℤ, Nonempty (M ≅ ⟨S.standardFormGradedFamily i, s⟩) := by
  let F := (Graded.FiniteGradedModule.homGrading
    (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)).shiftFunctor M.degree
  have h0 : Indecomposable (⟨M.obj, 0⟩ : Graded.FiniteGradedModule.ShiftedModule) := by
    apply MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive F
    simpa only [F, GradedCategory.HomGrading.shiftFunctor, zero_add] using hM
  obtain ⟨i, s, ⟨e⟩⟩ := S.standardFormGraded_exists_iso_shift M.obj h0
  refine ⟨i, s + M.degree, ⟨?_⟩⟩
  simpa only [F, GradedCategory.HomGrading.shiftFunctor, zero_add] using F.mapIso e

/-- Every graded module is a finite sum of the classified shifted vertex modules. -/
theorem standardFormGraded_decomposition
    (M : Graded.FiniteGradedModule.ShiftedModule
      (R := S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite)) :
    ∃ n : ℕ, ∃ i : Fin n → Fin S.n, ∃ s : Fin n → ℤ,
      Nonempty (M ≅ ⨁ fun j ↦
        (⟨S.standardFormGradedFamily (i j), s j⟩ : Graded.FiniteGradedModule.ShiftedModule)) := by
  classical
  obtain ⟨d⟩ := Graded.FiniteGradedModule.finiteDecomposition M
  choose i s e using fun j ↦ S.standardFormGraded_shifted_exists_iso (d.summand j) (d.indecomposable j)
  exact ⟨d.n, i, s, ⟨d.isoBiproduct.trans (biproduct.mapIso fun j ↦ (e j).some)⟩⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
