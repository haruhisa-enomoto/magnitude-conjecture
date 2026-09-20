import MagnitudeConjecture.CategoryTheory.FiniteCategoryPrimitivePresentation
import MagnitudeConjecture.CategoryTheory.CategoryAlgebraMatrixModel
import MagnitudeConjecture.Algebra.RightModuleSimpleCountAlgebraEquiv

/-! # Simple-module counts for finite skeletal category algebras -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.CoveringHom
universe u
variable {k : Type u} [Field k]
variable {C : Type} [Category.{u} C] [Preadditive C] [Linear k C] [Fintype C]
variable (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
  (linearCoyonedaLinearModule (k := k) X))

local instance simpleCountCategoryAlgebraFinite :
    FiniteDimensional k (finiteCategoryProjectiveGenerator.algebra hP) :=
  finiteCategoryProjectiveGenerator.algebra_finiteDimensional hP
local instance simpleCountCategoryAlgebraNoetherian :
    IsNoetherianRing (finiteCategoryProjectiveGenerator.algebra hP)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- Local endomorphism rings and skeletal objects identify the simple classes
of the category algebra with the objects of the category. -/
theorem finiteCategoryAlgebra_simpleCount
    (hlocal : ∀ X : C, IsLocalRing (End X)) (hskel : Skeletal C)
    (S : RightModule.FiniteIndecomposableSkeleton k
      (finiteCategoryProjectiveGenerator.algebra hP)) :
    S.simpleCount = Fintype.card C := by
  rw [S.simpleCount_eq_card_projectiveLabel]
  exact (Fintype.card_congr
    (finiteCategoryProjectiveGenerator.canonicalSourceEquiv hP hlocal S hskel)).symm

/-- The count applies to any algebra identified with the representable model,
including the finite matrix model. -/
theorem finiteCategoryAlgebra_simpleCount_of_algEquiv
    {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    [IsNoetherianRing Aᵐᵒᵖ]
    (f : A ≃ₐ[k] finiteCategoryProjectiveGenerator.algebra hP)
    (hlocal : ∀ X : C, IsLocalRing (End X)) (hskel : Skeletal C)
    (S : RightModule.FiniteIndecomposableSkeleton k A) :
    S.simpleCount = Fintype.card C := by
  rw [← S.simpleCount_mapAlgEquiv f]
  exact finiteCategoryAlgebra_simpleCount hP hlocal hskel (S.mapAlgEquiv f)

end MagnitudeConjecture.CoveringHom
