import MagnitudeConjecture.Algebra.RightModuleIntrinsicArrowMultiplicity
import MagnitudeConjecture.CategoryTheory.IrreducibleSpaceEquivalence

/-! # Arrow multiplicities under linear realizations of module categories -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u v
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable {C : Type v} [CategoryTheory.Category.{u} C] [Preadditive C] [Linear k C]
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- The official arrow multiplicity is the intrinsic quotient dimension in
any linearly equivalent realization of the module category. -/
theorem arrowMultiplicity_eq_irreducible_finrank_of_equivalence
    (E : FGModuleCat.{u} Aᵐᵒᵖ ≌ C) [E.functor.Additive] [E.functor.Linear k]
    (source target : Fin S.n) :
    FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData source target =
        Module.finrank k (CategoricalIrreducible.Space k
          (E.functor.obj (S.fgObj source)) (E.functor.obj (S.fgObj target))) :=
  (S.intrinsicIrreducible_finrank_eq_arrowMultiplicity source target).symm.trans
    (CategoricalIrreducible.spaceEquivalence k E (S.fgObj source) (S.fgObj target)).finrank_eq

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
