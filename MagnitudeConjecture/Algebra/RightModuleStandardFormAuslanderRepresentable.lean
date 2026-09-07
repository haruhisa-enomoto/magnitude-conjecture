import MagnitudeConjecture.Algebra.RightModuleStandardFormInjectiveResolution
import MagnitudeConjecture.CategoryTheory.LeftFreydProjectiveInjectiveCopresentation

/-!
# Projective-injective copresentations of standard-mesh representables
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormAuslanderRepresentableQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormAuslanderRepresentableArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/- The finite category of contravariant modules on the standard-form mesh. -/
abbrev StandardFormFiniteContravariantModuleCategory :=
  FiniteDimensionalModuleCategory.{0, u, u, u}
    (C := S.standardFormRightMeshData.VertexCategory (k := k)ᵒᵖ) k

set_option maxHeartbeats 800000 in
/-- The chosen injective copresentation of a standard-mesh representable has
projective-injective terms. -/
def standardFormContravariantRepresentableProjectiveInjectiveCopresentation
    (x : Fin S.n) :
    LeftFreyd.ProjectiveInjectiveCopresentation
      (S.standardFormRightMeshData.contravariantRepresentableFiniteModule
        (k := k) S.standardFormFiniteContravariantRepresentables x) := by
  let I := S.standardFormContravariantRepresentableMinimalInjectivePresentation x
  exact
    LeftFreyd.ProjectiveInjectiveCopresentation.ofTwoStepMinimalInjectivePresentation
      I
      (S.standardFormContravariantRepresentableInjectiveTermZero_projective x)
      (S.standardFormContravariantRepresentableInjectiveTermOne_projective x)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
