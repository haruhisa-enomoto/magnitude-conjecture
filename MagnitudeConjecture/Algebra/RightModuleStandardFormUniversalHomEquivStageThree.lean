import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomEquivStageTwo

/-! # Universal Hom comparison: orbit-skeleton composite -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomEquivStageThreeQuiverInstance :
    Quiver (Fin S.n) := S.standardFormQuiver

noncomputable local instance standardFormUniversalHomEquivStageThreeArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

namespace UniversalCover

/-- Add the orbit-skeleton pushdown Hom identification to the universal
comparison chain. -/
noncomputable def standardFormUniversalHomLinearEquivStageThree
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X Y : SourceCategory S p) :=
  (standardFormUniversalHomLinearEquivStageTwo S p hconnected X Y).trans
    (standardFormOrbitSkeletonPushdownHomLinearEquiv S p hconnected X Y)

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
