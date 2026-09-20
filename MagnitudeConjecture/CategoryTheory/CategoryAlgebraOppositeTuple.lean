import MagnitudeConjecture.CategoryTheory.MatrixTupleReindex
import MagnitudeConjecture.CategoryTheory.CategoryAlgebraMatrixModel

/-! # The category algebra of an opposite category as a direct tuple -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.CoveringHom
universe u v
variable {k : Type v} [Field k]
variable {C : Type} [Category.{v} C] [Preadditive C] [Linear k C] [Fintype C]
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear k D]

local instance categoryAlgebraOppositeTupleFintype : Fintype Cᵒᵖ := Fintype.ofEquiv C Opposite.equivToOpposite
local instance : (unopUnop C).Additive where
  map_add {X Y} f g := rfl
local instance : (unopUnop C).Linear k where
  map_smul _ _ := rfl

/-- For a fully faithful linear realization, the algebra of the opposite
category is the endomorphism algebra of the tuple of realized objects. -/
def categoryAlgebraOppositeTupleEquiv (F : C ⥤ D)
    [F.Additive] [F.Linear k] [F.Full] [F.Faithful] :
    End (categoryAlgebraTuple (C := Cᵒᵖ)) ≃ₐ[k]
      End (⟨C, F.obj⟩ : Mat_ D) :=
  (MagnitudeConjecture.CategoryTheory.matrixFunctorEndAlgEquiv
    (unopUnop C ⋙ F) (categoryAlgebraTuple (C := Cᵒᵖ))).trans
      (MagnitudeConjecture.CategoryTheory.matrixTupleReindexEndAlgEquiv
        Opposite.equivToOpposite.symm F.obj)

end MagnitudeConjecture.CoveringHom
