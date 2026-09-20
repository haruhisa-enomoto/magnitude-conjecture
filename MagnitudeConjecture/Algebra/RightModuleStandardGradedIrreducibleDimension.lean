import MagnitudeConjecture.Combinatorics.DegreeOneDimension
import MagnitudeConjecture.Algebra.RightModuleStandardGradedRadicalHigherDegree
import MagnitudeConjecture.Algebra.RightModuleStandardGradedRadicalDegreeOne
import MagnitudeConjecture.CategoryTheory.IrreducibleSpaceInvertible

/-! # The graded irreducible quotient dimension in every degree -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Nonpositive degree has no nonzero radical morphisms between the representatives. -/
theorem standardFormGraded_radical_bot_of_le
    (X Y : S.StandardFormMeshCategory) (s t : ℤ) (hst : s ≤ t) :
    CategoricalIrreducible.radical k
      (⟨S.standardFormGradedVertexFunctor.obj X, s⟩ : Graded.FiniteGradedModule.ShiftedModule)
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩ = ⊥ := by
  apply CategoricalIrreducible.radical_eq_bot_of_nonzero_isIso
  intro f hf
  by_contra hi
  have h := S.standardFormGraded_noniso_descent X Y s t f hf hi
  omega

/-- Only degree one contributes to the intrinsic irreducible quotient dimension. -/
def standardFormGraded_irreducible_finrank
    (X Y : S.StandardFormMeshCategory) (s t : ℤ) :=
  degreeOne_function_formula
    (fun s t ↦ Module.finrank k (CategoricalIrreducible.Space k
      (⟨S.standardFormGradedVertexFunctor.obj X, s⟩ : Graded.FiniteGradedModule.ShiftedModule)
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩))
    (Module.finrank k (S.standardFormIntegerHomGrading.component X Y 1))
    (fun t ↦ (S.standardFormGraded_degreeOne_irreducibleEquiv X Y t).finrank_eq)
    (fun s t hst ↦ CategoricalIrreducible.finrank_eq_zero_of_radical_eq_bot k _ _
      (S.standardFormGraded_radical_bot_of_le X Y s t hst))
    (fun t n hn ↦ S.standardFormGraded_higherDegree_irreducible_finrank_zero X Y t n hn) s t

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
