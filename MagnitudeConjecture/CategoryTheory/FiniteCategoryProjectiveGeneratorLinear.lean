import MagnitudeConjecture.CategoryTheory.FiniteCategoryProjectiveGenerator

/-! # Linearity of the finite category-algebra equivalence -/
set_option autoImplicit false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.CoveringHom.finiteCategoryProjectiveGenerator
universe u v
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [Fintype C]
variable (hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
  (linearCoyonedaLinearModule (k := k) X))
instance moduleEquivalence_additive : (moduleEquivalence hP).functor.Additive :=
  representedFGFunctor_additive hP
instance moduleEquivalence_linear : (moduleEquivalence hP).functor.Linear k :=
  representedFGFunctor_linear hP
end MagnitudeConjecture.CoveringHom.finiteCategoryProjectiveGenerator
