import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalInjective
import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalBijectiveCriterion

/-!
# Surjectivity of the universal restricted-Yoneda orbit Hom map
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

local instance standardFormUniversalSurjectiveQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalSurjectiveArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

set_option maxHeartbeats 800000 in
theorem standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap_surjective
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X Y : SourceCategory S p) :
    Function.Surjective
      (standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap S p X Y) := by
  exact
    (standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap_surjective_of_injective
      S p hconnected X Y).out
      (standardFormUniversalRestrictedYonedaShiftOrbitHomLinearMap_injective
        S p X Y)

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
