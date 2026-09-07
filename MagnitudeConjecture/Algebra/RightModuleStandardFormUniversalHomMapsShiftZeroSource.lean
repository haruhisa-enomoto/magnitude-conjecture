import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalHomMapsUnderlying

/-! # The source zero-degree shift-Hom coordinate -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalHomMapsShiftZeroSourceQuiverInstance :
    Quiver (Fin S.n) := S.standardFormQuiver

noncomputable local instance standardFormUniversalHomMapsShiftZeroSourceArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) := S.standardFormArrowFintype x y

namespace UniversalCover

/-- Convert a degree-zero ambient shift morphism to an ordinary morphism. -/
noncomputable def standardFormUniversalShiftHomZeroSourceLinearMap
    (p : Fin S.n) (X Y : SourceCategory S p) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let DAmbient :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    letI := DAmbient.hasShift
    CoveringHom.ShiftHom X Y (0 : Additive G) →ₗ[k] (X ⟶ Y) := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  letI := DAmbient.hasShift
  exact (CoveringHom.shiftHomZeroLinearEquiv
    (k := k) (A := Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p)) X Y).symm.toLinearMap

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
