import MagnitudeConjecture.CategoryTheory.MatrixTupleReindex
import MagnitudeConjecture.CategoryTheory.CategoryAlgebraMatrixModel

/-! # Algebra equivalences from finite linear category equivalences -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.CoveringHom
universe v
variable {k : Type v} [Field k]
variable {C D : Type} [Category.{v} C] [Category.{v} D]
variable [Preadditive C] [Preadditive D] [Linear k C] [Linear k D]
variable [Fintype C] [Fintype D]

/-- A fully faithful linear functor bijective on objects identifies the
finite matrix category algebras. -/
def categoryAlgebraMatrixEquiv (F : C ⥤ D)
    [F.Additive] [F.Linear k] [F.Full] [F.Faithful]
    (hobj : Function.Bijective F.obj) :
    End (categoryAlgebraTuple (C := C)) ≃ₐ[k]
      End (categoryAlgebraTuple (C := D)) :=
  (MagnitudeConjecture.CategoryTheory.matrixFunctorEndAlgEquiv
    F.op (categoryAlgebraTuple (C := C))).trans
      (MagnitudeConjecture.CategoryTheory.matrixTupleReindexEndAlgEquiv
        (Equiv.ofBijective F.obj hobj) Opposite.op)

end MagnitudeConjecture.CoveringHom
