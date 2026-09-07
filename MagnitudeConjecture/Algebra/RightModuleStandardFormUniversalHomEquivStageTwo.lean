import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomEquivStageOne

/-! # Universal Hom comparison: indexed-orbit composite -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomEquivStageTwoQuiverInstance :
    Quiver (Fin S.n) := S.standardFormQuiver

noncomputable local instance standardFormUniversalHomEquivStageTwoArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

namespace UniversalCover

/-- Add the indexed deck-orbit Hom identification to the universal comparison
chain. -/
noncomputable def standardFormUniversalHomLinearEquivStageTwo
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X Y : SourceCategory S p) :=
  (standardFormUniversalHomLinearEquivStageOne S p X Y).trans
    (standardFormIndexedDeckOrbitHomLinearEquiv S p hconnected X Y)

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
