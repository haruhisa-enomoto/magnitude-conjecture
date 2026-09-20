import MagnitudeConjecture.Algebra.RightModuleStandardGradedDegreeOne
import MagnitudeConjecture.CategoryTheory.IrreducibleSpaceAllMaps

/-! # The degree-one irreducible quotient is the degree-one mesh Hom space -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- All maps between adjacent shifts are radical. -/
theorem standardFormGraded_degreeOne_radical_top
    (X Y : S.StandardFormMeshCategory) (t : ℤ) :
    CategoricalIrreducible.radical k
      (⟨S.standardFormGradedVertexFunctor.obj X, t + 1⟩ : Graded.FiniteGradedModule.ShiftedModule)
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩ = ⊤ := by
  apply CategoricalIrreducible.radical_eq_top_of_no_reverse
  intro g
  by_contra hg
  have h := S.standardFormGraded_strict_descent Y X t (t + 1) g hg (Or.inr (by omega))
  omega

/-- The intrinsic radical square vanishes between adjacent shifts. -/
theorem standardFormGraded_degreeOne_radicalSquare_bot
    (X Y : S.StandardFormMeshCategory) (t : ℤ) :
    CategoricalIrreducible.radicalSquare k
      (⟨S.standardFormGradedVertexFunctor.obj X, t + 1⟩ : Graded.FiniteGradedModule.ShiftedModule)
      ⟨S.standardFormGradedVertexFunctor.obj Y, t⟩ = ⊥ :=
  CategoricalIrreducible.radicalSquare_eq_bot_of_all_nonzero_irreducible k _ _
    (fun f hf ↦ S.standardFormGraded_degreeOne_irreducible X Y t f hf)

/-- The degree-one intrinsic quotient retains precisely the degree-one mesh component. -/
def standardFormGraded_degreeOne_irreducibleEquiv
    (X Y : S.StandardFormMeshCategory) (t : ℤ) :=
  ((CategoricalIrreducible.spaceEquivHom k _ _
    (S.standardFormGraded_degreeOne_radical_top X Y t)
    (S.standardFormGraded_degreeOne_radicalSquare_bot X Y t)).trans
      (S.standardFormGradedHomEquiv X Y (t + 1) t).symm).trans
        (LinearEquiv.ofEq _ _ (congrArg (S.standardFormIntegerHomGrading.component X Y)
          (show (t + 1) - t = (1 : ℤ) by omega)))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
