import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomMapsShiftNonzero

/-! # Homogeneous Hom maps of universal restricted Yoneda -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomMapsShiftQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalHomMapsShiftArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- Restricted Yoneda maps a homogeneous ambient deck morphism to the
corresponding homogeneous morphism between translated modules. -/
noncomputable def standardFormUniversalRestrictedYonedaShiftHomLinearMap
    (p : Fin S.n) (X Y : SourceCategory S p)
    (a : Additive (StandardFormProjectiveGroup S p)) :=
  standardFormUniversalRestrictedYonedaShiftHomNonzeroLinearMap S p X Y a


end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
