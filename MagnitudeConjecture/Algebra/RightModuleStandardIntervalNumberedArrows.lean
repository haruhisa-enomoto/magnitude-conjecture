import MagnitudeConjecture.Algebra.RightModuleFGFamilyArrowMultiplicity
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalFamilyIrreducible
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSkeleton

/-! # Numbered interval arrows and allowed-shift quotient dimensions -/
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
local instance numberedIntervalFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance numberedIntervalNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

/-- The exact enumeration used by the actual interval skeleton. -/
def standardFormIntervalLabelEquiv (m : ℕ) :
    Fin (S.standardFormIntervalSkeleton m).n ≃ S.standardFormSupportedLabel m :=
  (Fintype.equivFin (S.standardFormSupportedLabel m)).symm

/-- Every numbered interval arrow multiplicity is the intrinsic quotient
dimension at the corresponding literal allowed shifts. -/
def standardFormIntervalSkeleton_arrowMultiplicity_eq (m : ℕ)
    (i j : Fin (S.standardFormIntervalSkeleton m).n) :=
  ofFGFamily_inverse_arrowMultiplicity_eq (k := k)
    (S.standardFormIntervalAlgebraEquivalence m) (S.standardFormSupportedFamily m)
    (S.standardFormIntervalFamily_indecomposable m)
    (S.standardFormIntervalFamily_complete m)
    (fun a b h ↦ h.elim (S.standardFormIntervalFamily_skeletal m a b)) i j

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
