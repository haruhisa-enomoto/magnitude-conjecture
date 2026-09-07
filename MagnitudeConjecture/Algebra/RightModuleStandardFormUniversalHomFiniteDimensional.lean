import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomEquivStageOne

/-! # Finite-dimensional universal orbit-Hom spaces -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomFiniteDimensionalQuiverInstance :
    Quiver (Fin S.n) := S.standardFormQuiver

noncomputable local instance standardFormUniversalHomFiniteDimensionalArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

namespace UniversalCover

/-- The source orbit-Hom space is finite-dimensional, transported from the
finite mesh-Hom space. -/
noncomputable def standardFormUniversalShiftOrbitHomFiniteDimensional
    (p : Fin S.n) (X Y : SourceCategory S p) := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  letI := DAmbient.hasShift
  letI := DAmbient.additiveShift
  letI := DAmbient.linearShift (k := k)
  let eSource :=
    MeshCategory.RightMeshData.UniversalCover.meshShiftOrbitProjectionHomLinearEquiv
      S.standardFormRightMeshData p (k := k) X Y
  let F := MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor
    S.standardFormRightMeshData p (k := k)
  letI := S.standardFormMeshHomFinite (k := k) (F.obj X) (F.obj Y)
  exact eSource.symm.finiteDimensional

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
