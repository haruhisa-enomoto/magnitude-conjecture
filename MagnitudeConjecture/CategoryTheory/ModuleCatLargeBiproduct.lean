import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Module biproducts with a universe-polymorphic index

Mathlib's explicit `ModuleCat.biproductIsoPi` specializes its finite index to
`Type`.  This variant uses the already universe-polymorphic product cone.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.ModuleCat

universe w v u

variable {R : Type u} [Ring R]
variable {J : Type w} (f : J → _root_.ModuleCat.{max w v} R)

/-- A finite categorical biproduct of modules is the dependent function
module, with no restriction on the universe of the finite index. -/
noncomputable def biproductIsoPi [Finite J] :
    ((⨁ f) : _root_.ModuleCat.{max w v} R) ≅
      _root_.ModuleCat.of R (∀ j, f j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit f)
    (_root_.ModuleCat.HasLimit.productLimitCone f).isLimit

end MagnitudeConjecture.ModuleCat
