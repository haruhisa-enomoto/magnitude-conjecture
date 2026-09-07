import MagnitudeConjecture.Algebra.RightModulePrimitiveIdempotent

/-!
# A generic indecomposability wrapper for finitely generated modules
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

namespace MagnitudeConjecture

universe u

/-- Package a finite indecomposable module as an indecomposable object of its
finitely generated module category. -/
theorem fgModuleCatOf_indecomposable
    {R M : Type u} [Ring R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Foundation.IsIndecomposableModule R M) :
    Indecomposable (FGModuleCat.of R M) :=
  RightModule.fgIndecomposable_of_isIndecomposableModule _ hM

end MagnitudeConjecture
