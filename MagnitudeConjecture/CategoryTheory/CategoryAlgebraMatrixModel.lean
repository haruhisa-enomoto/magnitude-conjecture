import MagnitudeConjecture.CategoryTheory.FiniteRepresentableLinearLift

/-! # A matrix additive model of the finite category algebra -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CoveringHom
universe v
variable {k : Type v} [Field k] {C : Type} [Category.{v} C]
variable [Preadditive C] [Linear k C] [Fintype C]
variable (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
  (linearCoyonedaLinearModule (k := k) X))

/-- The tuple representing the sum of all covariant representables. -/
def categoryAlgebraTuple : Mat_ Cᵒᵖ := ⟨C, Opposite.op⟩

/-- The existing category algebra equals the realized tuple's endomorphism algebra. -/
def categoryAlgebraTupleEquiv :
    End (categoryAlgebraTuple (C := C)) ≃ₐ[k] finiteCategoryProjectiveGenerator.algebra hP :=
  finiteRepresentableSumEndAlgEquiv hP (categoryAlgebraTuple (C := C))

end MagnitudeConjecture.CoveringHom
