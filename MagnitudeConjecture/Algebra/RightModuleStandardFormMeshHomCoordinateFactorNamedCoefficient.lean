import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorNamedIncoming
import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorCoefficientMap

/-! # The named factor-to-coefficient equality -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateNamedCoefficientQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateNamedCoefficientArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- The named Yoneda factor composite is the named coefficient map. -/
theorem standardFormSimpleResolutionYonedaFactorComposite_eq_coefficientMap
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
    S.standardFormSimpleResolutionYonedaFactorComposite z.1 x t a =
      S.standardFormSimpleResolutionYonedaCoefficientMap hP z x h a :=
  S.standardFormSimpleResolutionYonedaCoefficient_map_eq_factor
    hP z x h t ht a

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
