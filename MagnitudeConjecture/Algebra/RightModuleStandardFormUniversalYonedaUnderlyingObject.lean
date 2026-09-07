import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomMapsUnderlying

/-! # Underlying objects of universal restricted Yoneda -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalYonedaUnderlyingObjectQuiverInstance :
    Quiver (Fin S.n) := S.standardFormQuiver

noncomputable local instance standardFormUniversalYonedaUnderlyingObjectArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

namespace UniversalCover

/-- The underlying linear module of universal restricted Yoneda at one
universal-mesh object. -/
def standardFormUniversalRestrictedYonedaUnderlyingObject
    (p : Fin S.n) (X : SourceCategory S p) :
    CoveringHom.LinearModuleCategory
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k :=
  ((standardFormUniversalRestrictedYonedaFunctor S p).obj X).obj

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
