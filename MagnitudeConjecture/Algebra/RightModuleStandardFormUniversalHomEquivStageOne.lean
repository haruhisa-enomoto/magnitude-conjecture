import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomEquivDownstairs

/-! # Universal Hom comparison: first composite -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomEquivStageOneQuiverInstance :
    Quiver (Fin S.n) := S.standardFormQuiver

noncomputable local instance standardFormUniversalHomEquivStageOneArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

namespace UniversalCover

/-- The universal mesh projection followed by the downstairs Hom
identification. -/
noncomputable def standardFormUniversalHomLinearEquivStageOne
    (p : Fin S.n) (X Y : SourceCategory S p) := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  letI := DAmbient.hasShift
  letI := DAmbient.additiveShift
  letI := DAmbient.linearShift (k := k)
  exact
    (MeshCategory.RightMeshData.UniversalCover.meshShiftOrbitProjectionHomLinearEquiv
      S.standardFormRightMeshData p (k := k) X Y).trans
      (standardFormRestrictedYonedaDownstairsHomLinearEquiv S p X Y)

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
