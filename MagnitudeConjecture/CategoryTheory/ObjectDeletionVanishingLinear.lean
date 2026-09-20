import MagnitudeConjecture.CategoryTheory.ObjectDeletionAlmostSplit
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Linearity of extension by zero into vanishing modules -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.ObjectDeletion
universe u v
variable {k : Type v} [Field k]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear k C] (S : Set C)

instance finiteDimensionalModuleExtensionByZeroToVanishing_additive :
    (finiteDimensionalModuleExtensionByZeroToVanishing (k := k) C S).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact (finiteDimensionalModuleExtensionByZero (k := k) C S).map_add

instance finiteDimensionalModuleExtensionByZeroToVanishing_linear :
    (finiteDimensionalModuleExtensionByZeroToVanishing (k := k) C S).Linear k where
  map_smul := by
    intro M N f r
    ext X x h
    rfl

instance finiteDimensionalModuleExtensionByZeroVanishingEquivalence_additive :
    (finiteDimensionalModuleExtensionByZeroVanishingEquivalence (k := k) C S).functor.Additive :=
  finiteDimensionalModuleExtensionByZeroToVanishing_additive C S

instance finiteDimensionalModuleExtensionByZeroVanishingEquivalence_linear :
    (finiteDimensionalModuleExtensionByZeroVanishingEquivalence (k := k) C S).functor.Linear k :=
  finiteDimensionalModuleExtensionByZeroToVanishing_linear C S

end MagnitudeConjecture.ObjectDeletion
