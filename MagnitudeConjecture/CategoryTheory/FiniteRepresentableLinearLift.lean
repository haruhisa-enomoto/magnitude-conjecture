import MagnitudeConjecture.CategoryTheory.LinearAdditiveEnvelopeLift
import MagnitudeConjecture.CategoryTheory.OppositeLinear

/-! # Linear algebra comparison for finite representable sums -/
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace MagnitudeConjecture.CoveringHom
universe u v
variable {k : Type v} [Field k] {C : Type u} [Category.{v} C]
variable [Preadditive C] [Linear k C]
variable (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
  (linearCoyonedaLinearModule (k := k) X))

instance finiteRepresentableLinear : (finiteDimensionalLinearCoyonedaFunctor hP).Linear k where
  map_smul := by
    intro X Y f c
    apply ObjectProperty.hom_ext
    ext Z x
    exact Linear.smul_comp _ _ _ _ _ _

/-- Endomorphism algebras of finite sums agree with their actual representable realization. -/
def finiteRepresentableSumEndAlgEquiv (X : Mat_ Cᵒᵖ) :
    End X ≃ₐ[k] End ((finiteMatrixLift (finiteDimensionalLinearCoyonedaFunctor hP)).obj X) :=
  MagnitudeConjecture.CategoryTheory.finiteMatrixLiftEndAlgEquiv
    (finiteDimensionalLinearCoyonedaFunctor hP) X

end MagnitudeConjecture.CoveringHom
