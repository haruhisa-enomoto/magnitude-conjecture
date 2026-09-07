import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorNamedEquation

/-! # Evaluation of the named Yoneda coefficient -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateNamedEvaluationQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateNamedEvaluationArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- The named coefficient map is the underlying finite-module coordinate. -/
theorem standardFormSimpleResolutionYonedaCoefficientMap_eq_finiteCoordinate
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (a : MeshCategory.RightMeshData.IncomingArrow z.1) :
    S.standardFormSimpleResolutionYonedaCoefficientMap hP z x h a =
      S.standardFormSimpleResolutionFiniteCoordinateComposite hP z x h a :=
  S.linearYoneda_map_standardFormSimpleResolutionYonedaCoefficient hP z x h a

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
