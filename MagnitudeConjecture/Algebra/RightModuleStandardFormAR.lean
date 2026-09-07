import MagnitudeConjecture.Algebra.RightModuleStandardFormARRightAlmostSplit

/-!
# Auslander--Reiten meshes of the standard-form algebra

This compatibility module packages the recovered incoming mesh as a minimal
right almost-split map.
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

local instance standardFormARPackageQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARPackageArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The literal recovered incoming mesh, packaged as a minimal right
almost-split map at the recovered skeleton label. -/
def standardFormRecoveredMinimalRightAlmostSplitAt
    (z : Fin S.n) :
    (S.standardFormProjectiveVertexModuleIndecomposableSkeleton (k := k))
      |>.MinimalRightAlmostSplitAt z where
  source :=
    (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).obj
      (S.standardFormRightMeshData.additiveIncomingObj (k := k) z)
  map := S.standardFormRecoveredIncomingMap (k := k) z
  rightAlmostSplit :=
    S.standardFormRecoveredIncomingMap_rightAlmostSplit (k := k) z
  rightMinimal :=
    S.standardFormRecoveredIncomingMap_rightMinimal (k := k) z

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
