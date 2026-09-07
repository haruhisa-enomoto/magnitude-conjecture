import MagnitudeConjecture.Algebra.RightModuleFactorCategory
import MagnitudeConjecture.CategoryTheory.AdditiveAuslanderEquivalence

/-!
# The additive Auslander equivalence of the literal factor category

The biproduct of the surviving indecomposable representatives is a finite
additive generator of the literal factor category.  Applying the generic
additive-generator equivalence therefore identifies that factor category with
the finitely generated projective modules over its Auslander algebra.

This is the finite algebraic ambient category in which the manuscript's
smaller, boundary-projective restricted Yoneda realization will be analyzed.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Preadditive

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- The literal factor category is the category of finitely generated
projective modules over the opposite endomorphism ring of its surviving
additive generator. -/
def factorAuslanderEquivalence (K : Set (Fin S.n)) :
    S.FactorCategory K ≌
      (MagnitudeConjecture.CategoryTheory.finiteProjectiveModules
        (End (S.factorAdditiveGenerator K))ᵐᵒᵖ).FullSubcategory :=
  MagnitudeConjecture.CategoryTheory.finiteAddGeneratorAuslanderEquivalence
    (S.factorAdditiveGenerator K)
    (S.factorAdditiveGenerator_isFiniteAddGenerator K)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
