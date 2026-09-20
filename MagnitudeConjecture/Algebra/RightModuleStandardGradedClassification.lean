import MagnitudeConjecture.Algebra.RightModuleStandardGradedRepresentatives
import MagnitudeConjecture.CategoryTheory.GradedModuleUnderlyingIndecomposable

/-! # Classification of the graded indecomposables of the standard form -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Every listed shift is a graded indecomposable. -/
theorem standardFormGraded_shift_indecomposable (i : Fin S.n) (s : ℤ) :
    Indecomposable (⟨S.standardFormGradedFamily i, s⟩ : Graded.FiniteGradedModule.ShiftedModule) :=
  Graded.FiniteGradedModule.indecomposable_of_underlying _ s
    (S.standardFormGradedFamily_indecomposable i)

/-- Every graded indecomposable is a shift of a standard-form vertex module. -/
theorem standardFormGraded_exists_iso_shift
    (X : Graded.FiniteGradedModule
      (S.standardFormOppositeAlgebraGrading S.standardFormMeshHomFinite))
    (hX : Indecomposable (⟨X, 0⟩ : Graded.FiniteGradedModule.ShiftedModule)) :
    ∃ i : Fin S.n, ∃ s : ℤ,
      Nonempty ((⟨X, 0⟩ : Graded.FiniteGradedModule.ShiftedModule) ≅
        ⟨S.standardFormGradedFamily i, s⟩) := by
  letI := S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite
  exact Graded.FiniteGradedModule.exists_iso_shift_of_complete_family
    S.standardFormGradedFamily S.standardFormGradedFamily_indecomposable
    S.standardFormGradedFamily_complete X hX

/-- An isomorphism between two shifted representatives determines both labels. -/
theorem standardFormGraded_label_shift_unique {i j : Fin S.n} {s t : ℤ}
    (e : (⟨S.standardFormGradedFamily i, s⟩ : Graded.FiniteGradedModule.ShiftedModule) ≅
      ⟨S.standardFormGradedFamily j, t⟩) : i = j ∧ s = t :=
  Graded.FiniteGradedModule.label_shift_eq_of_iso S.standardFormGradedFamily
    S.standardFormGradedFamily_indecomposable S.standardFormGradedFamily_skeletal e

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
