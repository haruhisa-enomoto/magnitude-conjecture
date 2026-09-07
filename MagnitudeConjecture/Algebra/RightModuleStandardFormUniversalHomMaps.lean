import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomMapsShift

/-! # Shift-orbit Hom maps of universal restricted Yoneda -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomMapsOrbitQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalHomMapsOrbitArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The homogeneous restricted-Yoneda maps assembled over all deck degrees. -/
noncomputable def standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap
    (p : Fin S.n) (X Y : SourceCategory S p) := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := DAmbient.hasShift
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := CoveringHom.linearModuleCategoryHasShift (k := k) D.core
  exact DFinsupp.mapRange.linearMap fun a ↦
    standardFormUniversalRestrictedYonedaShiftHomLinearMap S p X Y a


end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
