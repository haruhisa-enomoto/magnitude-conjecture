import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorNamedEvaluation

/-! # The named underlying coordinate equation -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateNamedUnderlyingQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateNamedUnderlyingArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The named incoming composite equals the underlying finite-module
coordinate. -/
theorem standardFormSimpleResolutionIncomingYonedaFactorComposite_eq_finiteCoordinate
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
    S.standardFormSimpleResolutionIncomingYonedaFactorComposite
        hP z.1 x t a =
      S.standardFormSimpleResolutionFiniteCoordinateComposite hP z x h a := by
  rw [S.standardFormSimpleResolutionIncomingYonedaFactorComposite_eq_coefficientMap
    hP z x h t ht a]
  exact S.standardFormSimpleResolutionYonedaCoefficientMap_eq_finiteCoordinate
    hP z x h a

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
