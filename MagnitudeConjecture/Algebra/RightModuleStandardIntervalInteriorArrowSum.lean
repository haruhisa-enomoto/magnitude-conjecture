import MagnitudeConjecture.Algebra.RightModuleStandardIntervalNumberedArrows
import MagnitudeConjecture.Algebra.RightModuleFGFamilyFilteredArrowSum
import MagnitudeConjecture.Algebra.RightModuleStandardInteriorArrowSum
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalFamilyIrreducible
import MagnitudeConjecture.Algebra.RightModuleStandardIntervalSkeleton

/-! # Total interior arrows for the actual interval skeleton -/
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
local instance interiorTotalIntervalFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) :=
  S.standardFormIntervalAlgebra_finiteDimensional m
local instance interiorTotalIntervalNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _

/-- The actual interval skeleton's interior contribution is the ordinary
arrow total repeated once for each interior shift. -/
def standardFormIntervalSkeleton_interior_arrowSum (m : ℕ)
    (hm : 2 * S.standardFormIntervalControlHeight ≤ m) :=
  ofFGFamily_inverse_filtered_arrow_sum_eq_of_sum (k := k)
    (S.standardFormIntervalAlgebraEquivalence m) (S.standardFormSupportedFamily m)
    (S.standardFormIntervalFamily_indecomposable m)
    (S.standardFormIntervalFamily_complete m)
    (fun a b h ↦ h.elim (S.standardFormIntervalFamily_skeletal m a b))
    (fun b : S.standardFormSupportedLabel m ↦
      0 ≤ b.2.val ∧ b.2.val ≤ (m : ℤ) - 2 * S.standardFormIntervalControlHeight)
    _ (S.standardFormSupported_interior_arrowSum m hm)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
