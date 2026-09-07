import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalYoneda

/-!
# Hom maps of universal restricted Yoneda

This file contains the ordinary, homogeneous, and shift-orbit Hom maps.  Their
injectivity and surjectivity are checked in later modules.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomMapsQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalHomMapsArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The ordinary Hom map of universal restricted Yoneda after forgetting the
finite-support property. -/
noncomputable def standardFormUniversalRestrictedYonedaUnderlyingHomLinearMap
    (p : Fin S.n) (X Y : SourceCategory S p) :
    (X ⟶ Y) →ₗ[k]
      ((standardFormUniversalRestrictedYonedaFunctor S p).obj X).obj ⟶
        ((standardFormUniversalRestrictedYonedaFunctor S p).obj Y).obj := by
  let U := standardFormUniversalRestrictedYonedaFunctor S p
  exact
    { toFun := fun f ↦ (U.map f).hom
      map_add' := fun f g ↦ by
        rw [U.map_add]
        rfl
      map_smul' := fun r f ↦ by
        rw [U.map_smul]
        rfl }


end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
