import MagnitudeConjecture.Algebra.RightModuleStandardFormARIncoming

/-!
# Additive-hull lift of incoming coefficient families
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

local instance standardFormARIncomingAdditiveLiftQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARIncomingAdditiveLiftArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The one-row additive-hull matrix represented by an incoming coefficient
family. -/
def standardFormIncomingCoefficientAdditiveLift
    (x z : Fin S.n)
    (coeff : MeshCategory.RightMeshData.IncomingCoefficient
      (k := k) S.standardFormRightMeshData x z) :
    S.standardFormRightMeshData.additiveVertexObj (k := k) x ⟶
      S.standardFormRightMeshData.additiveIncomingObj (k := k) z :=
  (S.standardFormRightMeshData.additiveIncomingHomLinearEquiv
    (k := k) x z).symm coeff

/-- The additive coefficient lift composed with the incoming matrix is the
singleton matrix represented by the mesh-category incoming sum. -/
theorem standardFormIncomingCoefficientAdditiveLift_comp_incomingMap
    (x z : Fin S.n)
    (coeff : MeshCategory.RightMeshData.IncomingCoefficient
      (k := k) S.standardFormRightMeshData x z) :
    S.standardFormIncomingCoefficientAdditiveLift (k := k) x z coeff ≫
        S.standardFormRightMeshData.additiveIncomingMap (k := k) z =
      (S.standardFormRightMeshData.additiveVertexHomLinearEquiv
        (k := k) x z).symm
          (S.standardFormRightMeshData.incomingSum (k := k) coeff) := by
  let T := S.standardFormRightMeshData
  apply (T.additiveVertexHomLinearEquiv (k := k) x z).injective
  rw [T.additiveVertexHomLinearEquiv_comp_incomingMap (k := k) x z]
  simp [standardFormIncomingCoefficientAdditiveLift, T]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
