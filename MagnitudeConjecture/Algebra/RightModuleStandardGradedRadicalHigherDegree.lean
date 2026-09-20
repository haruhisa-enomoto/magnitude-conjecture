import MagnitudeConjecture.Algebra.RightModuleStandardGradedHigherDegree
import MagnitudeConjecture.CategoryTheory.NoBackwardRadicalSquare
import MagnitudeConjecture.CategoryTheory.IrreducibleSpaceVanishing

/-! # Higher-degree maps vanish in the intrinsic irreducible quotient -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Every graded Hom of degree at least two belongs to the actual radical square. -/
theorem standardFormGraded_higherDegree_radicalSquare_top
    (X Y : S.StandardFormMeshCategory) (t : ℤ) (n : ℕ) (hn : 0 < n) :
    CategoricalIrreducible.radicalSquare k
      (⟨S.standardFormGradedVertexFunctor.obj X, t + n + 1⟩ : Graded.FiniteGradedModule.ShiftedModule)
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩ = ⊤ := by
  apply top_unique
  intro f _
  exact MagnitudeConjecture.CategoryTheory.noBackwardFactorizations_le_radicalSquare _ _
    (S.standardFormGraded_higherDegree_factorization X Y t n hn f)

/-- Higher-degree graded irreducible quotient dimensions are zero. -/
def standardFormGraded_higherDegree_irreducible_finrank_zero
    (X Y : S.StandardFormMeshCategory) (t : ℤ) (n : ℕ) (hn : 0 < n) :=
  CategoricalIrreducible.finrank_eq_zero_of_radicalSquare_eq_top k _ _
    (S.standardFormGraded_higherDegree_radicalSquare_top X Y t n hn)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
