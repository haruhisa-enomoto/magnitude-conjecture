import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDecomposition
import MagnitudeConjecture.CategoryTheory.InjectiveEnvelope

/-!
# Essential simple socles of finite functors

A finite-dimensional functor has a simple subfunctor whenever it is nonzero.
Consequently a simple subfunctor through which every simple subfunctor factors
is essential.  This is the finite-length bridge used in the
Auslander--Reiten Corollary 3.8 argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- A simple subfunctor of a finite functor is essential when every simple
subfunctor factors through it. -/
theorem finiteDimensionalModule_isEssentialMono_of_simple_factors
    {L F : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    [Simple L] (l : L ⟶ F) [Mono l]
    (hfactor : ∀ {T : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
      [Simple T] (t : T ⟶ F) [Mono t],
      t ≠ 0 → ∃ a : T ⟶ L, a ≫ l = t) :
    IsEssentialMono l := by
  apply isEssentialMono_of_simple_factors_of_exists_simple_subobject l ?_ hfactor
  intro K i _ hK
  obtain ⟨T, s, hT, hs⟩ := finiteDimensionalModule_exists_simple_subobject K hK
  exact ⟨T, s, hT, hs⟩

end MagnitudeConjecture.CoveringHom
