import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorNamedCoefficient

/-! # The named coordinate-factor equation -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateNamedEquationQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateNamedEquationArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The named incoming composite equals the named coefficient map. -/
theorem standardFormSimpleResolutionIncomingYonedaFactorComposite_eq_coefficientMap
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
      S.standardFormSimpleResolutionYonedaCoefficientMap hP z x h a := by
  rw [S.standardFormSimpleResolutionIncomingYonedaFactorComposite_eq]
  exact S.standardFormSimpleResolutionYonedaFactorComposite_eq_coefficientMap
    hP z x h t ht a

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
