import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomEquivStageThree
import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomEquivPushdown

/-! # Universal Hom comparison: total equivalence -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomEquivTotalQuiverInstance :
    Quiver (Fin S.n) := S.standardFormQuiver

noncomputable local instance standardFormUniversalHomEquivTotalArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

namespace UniversalCover

/-- The complete linear equivalence between the source and target orbit-Hom
spaces of universal restricted Yoneda. -/
noncomputable def standardFormUniversalHomLinearEquivTotal
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X Y : SourceCategory S p) :=
  (standardFormUniversalHomLinearEquivStageThree S p hconnected X Y).trans
    (standardFormUniversalPushdownHomLinearEquiv S p X Y)

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
