import MagnitudeConjecture.Algebra.RightModuleStandardIntervalAlgebra
import MagnitudeConjecture.CategoryTheory.IndecomposableFamilyEquivalence
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Actual indecomposable modules of the standard-form interval algebra -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
universe u
variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
attribute [local irreducible] standardFormIntervalAlgebraEquivalence

local instance standardIntervalClassificationFinite (m : ℕ) :
    FiniteDimensional k (S.standardFormIntervalAlgebra m) := S.standardFormIntervalAlgebra_finiteDimensional m
local instance standardIntervalClassificationNoetherian (m : ℕ) :
    IsNoetherianRing (S.standardFormIntervalAlgebra m)ᵐᵒᵖ := IsNoetherianRing.of_finite k _
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

instance standardFormIntervalEquivalence_additive (m : ℕ) :
    (S.standardFormIntervalAlgebraEquivalence m).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance standardFormIntervalEquivalence_inverse_additive (m : ℕ) :
    (S.standardFormIntervalAlgebraEquivalence m).inverse.Additive :=
  CategoryTheory.Equivalence.inverse_additive _

/-- The indecomposable right interval modules, indexed by the exact allowed shifts. -/
def standardFormIntervalFamily (m : ℕ) (a : S.standardFormSupportedLabel m) :
    FGModuleCat.{u} (S.standardFormIntervalAlgebra m)ᵐᵒᵖ :=
  (S.standardFormIntervalAlgebraEquivalence m).inverse.obj (S.standardFormSupportedFamily m a)

/-- Every member of the interval family is indecomposable. -/
theorem standardFormIntervalFamily_indecomposable (m : ℕ) (a : S.standardFormSupportedLabel m) :
    Indecomposable (S.standardFormIntervalFamily m a) :=
  (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
    (S.standardFormIntervalAlgebraEquivalence m).inverse _).mpr
      (S.standardFormSupportedFamily_indecomposable m a)

/-- Every indecomposable right interval module occurs in the finite family. -/
theorem standardFormIntervalFamily_complete (m : ℕ)
    (X : FGModuleCat.{u} (S.standardFormIntervalAlgebra m)ᵐᵒᵖ) (hX : Indecomposable X) :
    ∃ a : S.standardFormSupportedLabel m, Nonempty (X ≅ S.standardFormIntervalFamily m a) :=
  MagnitudeConjecture.CategoryTheory.complete_indecomposable_family_of_equivalence
    (S.standardFormIntervalAlgebraEquivalence m) (S.standardFormSupportedFamily m)
    (S.standardFormSupportedFamily_complete m) X hX

/-- The interval family has no repeated isomorphism class. -/
theorem standardFormIntervalFamily_skeletal (m : ℕ) (a b : S.standardFormSupportedLabel m)
    (e : S.standardFormIntervalFamily m a ≅ S.standardFormIntervalFamily m b) : a = b := by
  let E := S.standardFormIntervalAlgebraEquivalence m
  exact S.standardFormSupportedFamily_skeletal m a b
    ((E.counitIso.app (S.standardFormSupportedFamily m a)).symm ≪≫ E.functor.mapIso e ≪≫
      E.counitIso.app (S.standardFormSupportedFamily m b))

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
