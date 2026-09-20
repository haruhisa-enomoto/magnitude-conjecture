import MagnitudeConjecture.Algebra.RightModuleStandardIntervalNumberedArrows
import MagnitudeConjecture.Algebra.RightModuleFGFamilyIncomingSum
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalFamilyIrreducible
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSkeleton

/-! # Incoming sums for the actual interval skeleton -/
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
local instance incomingIntervalFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance incomingIntervalNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

/-- The actual numbered interval incoming sum equals the supported-family sum. -/
def standardFormIntervalSkeleton_incoming_sum (m : ℕ)
    (j : Fin (S.standardFormIntervalSkeleton m).n) :=
  ofFGFamily_inverse_incoming_sum_eq (k := k)
    (S.standardFormIntervalAlgebraEquivalence m) (S.standardFormSupportedFamily m)
    (S.standardFormIntervalFamily_indecomposable m)
    (S.standardFormIntervalFamily_complete m)
    (fun a b h ↦ h.elim (S.standardFormIntervalFamily_skeletal m a b)) j

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
