import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorNamedUnderlying

/-! # Underlying coordinate equation for the represented mesh factor -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateUnderlyingEquationQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateUnderlyingEquationArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The coordinate equation after forgetting both finite-dimensional module
properties. -/
theorem standardFormSimpleResolutionYonedaFactor_coordinate_hom_hom
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
    (S.standardFormRightMeshData.incomingSummandInclusionFinite
          (k := k) hP z.1 a ≫
        S.standardFormRightMeshData.incomingMapFinite (k := k) hP z.1 ≫
          S.standardFormSimpleResolutionYonedaFactor hP z.1 x t).hom.hom =
      (S.standardFormRightMeshData.incomingSummandInclusionFinite
          (k := k) hP z.1 a ≫ h).hom.hom := by
  change S.standardFormSimpleResolutionIncomingYonedaFactorComposite
      hP z.1 x t a =
    S.standardFormSimpleResolutionFiniteCoordinateComposite hP z x h a
  exact
    S.standardFormSimpleResolutionIncomingYonedaFactorComposite_eq_finiteCoordinate
      hP z x h t ht a

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
