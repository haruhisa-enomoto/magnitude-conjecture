import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorUnderlyingEquation

/-! # Coordinate equation for the represented mesh factor -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateFactorEquationQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateFactorEquationArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The represented lift satisfies the desired factorization on one incoming
biproduct coordinate. -/
theorem standardFormSimpleResolutionYonedaFactor_coordinate
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (t : MeshCategory.obj (k := k) S.standardFormRightMeshData z.1 ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData x)
    (ht : ∀ a : MeshCategory.RightMeshData.IncomingArrow z.1,
      (S.standardFormSimpleResolutionYonedaCoefficient hP z x h a).hom =
        S.standardFormRightMeshData.incomingArrowHom (k := k) a ≫ t)
    (a : MeshCategory.RightMeshData.IncomingArrow z.1) :
    S.standardFormRightMeshData.incomingSummandInclusionFinite
          (k := k) hP z.1 a ≫
        S.standardFormRightMeshData.incomingMapFinite (k := k) hP z.1 ≫
          S.standardFormSimpleResolutionYonedaFactor hP z.1 x t =
      S.standardFormRightMeshData.incomingSummandInclusionFinite
          (k := k) hP z.1 a ≫ h := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact S.standardFormSimpleResolutionYonedaFactor_coordinate_hom_hom
    hP z x h t ht a

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
