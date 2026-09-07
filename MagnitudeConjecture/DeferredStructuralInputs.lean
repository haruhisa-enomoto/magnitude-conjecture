import MagnitudeConjecture.Algebra.RepresentationFiniteSpecialBiserialBeta

/-!
# Formerly deferred structural inputs

Both structural inputs formerly deferred by the magnitude-conjecture
formalization campaign are now proved.  This compatibility module imports
their completed development without adding any axiom boundary.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]

end MagnitudeConjecture
