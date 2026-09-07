import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorEquation

/-! # Coordinate factorization for the standard mesh-simple resolution -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateFactorQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateFactorArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Construct the factor morphism and verify its equation on every incoming
biproduct coordinate. -/
theorem standardFormSimpleResolution_hom_coordinate_factor
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (hh : S.standardFormRightMeshData.translationMapFinite (k := k) hP z ≫ h = 0) :
    ∃ b : S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x,
      ∀ a : MeshCategory.RightMeshData.IncomingArrow z.1,
        S.standardFormRightMeshData.incomingSummandInclusionFinite
            (k := k) hP z.1 a ≫
            S.standardFormRightMeshData.incomingMapFinite (k := k) hP z.1 ≫ b =
          S.standardFormRightMeshData.incomingSummandInclusionFinite
            (k := k) hP z.1 a ≫ h := by
  classical
  obtain ⟨t, ht⟩ :=
    S.standardFormSimpleResolution_yoneda_lift hP z x h hh
  exact ⟨S.standardFormSimpleResolutionYonedaFactor hP z.1 x t,
    S.standardFormSimpleResolutionYonedaFactor_coordinate hP z x h t ht⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
