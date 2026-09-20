import MagnitudeConjecture.Algebra.RightModuleStandardIntervalIrreducible
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalClassification
import MagnitudeConjecture.CategoryTheory.IrreducibleSpaceIso

/-! # Irreducible spaces for the allowed-shift interval family -/
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
attribute [local irreducible] standardFormIntervalAlgebraEquivalence

/-- The quotient for the actual interval-module family is the quotient on
its literal allowed-shift representatives in the supported category. -/
def standardFormIntervalFamily_irreducibleEquiv (m : ℕ)
    (a b : S.standardFormSupportedLabel m) :=
  CategoricalIrreducible.spaceInverseEquivalence k (S.standardFormIntervalAlgebraEquivalence m)
    (S.standardFormSupportedFamily m a) (S.standardFormSupportedFamily m b)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
