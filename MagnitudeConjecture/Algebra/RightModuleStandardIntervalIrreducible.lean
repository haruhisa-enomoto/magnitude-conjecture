import MagnitudeConjecture.Algebra.RightModuleStandardIntervalAlgebra
import MagnitudeConjecture.Algebra.RightModuleIntrinsicArrowMultiplicity
import MagnitudeConjecture.CategoryTheory.GradedPrincipalIntervalLinear
import MagnitudeConjecture.CategoryTheory.IrreducibleSpaceEquivalence

/-! # Intrinsic irreducible quotients for the actual interval algebra -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
local instance intervalIrreducibleBaseFinite :
    FiniteDimensional k (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

instance standardFormIntervalAlgebraEquivalence_additive (m : ℕ) :
    (S.standardFormIntervalAlgebraEquivalence m).functor.Additive := by
  unfold standardFormIntervalAlgebraEquivalence
  infer_instance

instance standardFormIntervalAlgebraEquivalence_linear (m : ℕ) :
    (S.standardFormIntervalAlgebraEquivalence m).functor.Linear k := by
  unfold standardFormIntervalAlgebraEquivalence
  infer_instance

attribute [local irreducible] standardFormIntervalAlgebraEquivalence

/-- The actual interval realization preserves the intrinsic irreducible quotient. -/
def standardFormInterval_irreducibleEquiv (m : ℕ)
    (X Y : FGModuleCat.{u} (S.standardFormIntervalAlgebra m)ᵐᵒᵖ) :
    CategoricalIrreducible.Space k X Y ≃ₗ[k]
      CategoricalIrreducible.Space k
        ((S.standardFormIntervalAlgebraEquivalence m).functor.obj X)
        ((S.standardFormIntervalAlgebraEquivalence m).functor.obj Y) :=
  CategoricalIrreducible.spaceEquivalence k (S.standardFormIntervalAlgebraEquivalence m) X Y

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
