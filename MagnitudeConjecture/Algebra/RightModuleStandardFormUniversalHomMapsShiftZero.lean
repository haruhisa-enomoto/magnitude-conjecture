import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomMapsShiftZeroTarget
import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomMapsShiftZeroSource

/-! # The zero-degree Hom map of universal restricted Yoneda -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomMapsShiftZeroQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalHomMapsShiftZeroArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- At degree zero, restricted Yoneda is conjugated by the two canonical
zero-degree shift-Hom coordinates. -/
noncomputable def standardFormUniversalRestrictedYonedaShiftHomZeroLinearMap
    (p : Fin S.n) (X Y : SourceCategory S p) := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := DAmbient.hasShift
  letI := D.hasShift
  letI := CoveringHom.linearModuleCategoryHasShift (k := k) D.core
  exact (standardFormUniversalShiftHomZeroTargetLinearMap S p X Y).comp
    ((standardFormUniversalRestrictedYonedaUnderlyingHomLinearMap S p X Y).comp
      (standardFormUniversalShiftHomZeroSourceLinearMap S p X Y))

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
