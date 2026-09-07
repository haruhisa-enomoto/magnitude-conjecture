import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorMorphisms

/-! # The named incoming-to-factor equality -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateNamedIncomingQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateNamedIncomingArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- The named incoming composite is the named Yoneda factor composite. -/
theorem standardFormSimpleResolutionIncomingYonedaFactorComposite_eq
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z x : Fin S.n)
    (t : MeshCategory.obj (k := k) S.standardFormRightMeshData z ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData x)
    (a : MeshCategory.RightMeshData.IncomingArrow z) :
    S.standardFormSimpleResolutionIncomingYonedaFactorComposite hP z x t a =
      S.standardFormSimpleResolutionYonedaFactorComposite z x t a :=
  S.standardFormIncoming_comp_yonedaFactor z x a t

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
