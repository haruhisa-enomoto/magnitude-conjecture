import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorMap

/-! # Yoneda image of the lifted coordinate identity -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateCoefficientMapQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateCoefficientMapArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- Applying linear Yoneda to the lifted coordinate identity. -/
theorem standardFormSimpleResolutionYonedaCoefficient_map_eq_factor
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
    let T := S.standardFormRightMeshData
    let Y := CategoryTheory.linearYoneda k (T.VertexCategory (k := k))
    Y.map (InducedCategory.homMk (T.incomingArrowHom (k := k) a) ≫
          InducedCategory.homMk t) =
      Y.map (S.standardFormSimpleResolutionYonedaCoefficient hP z x h a) := by
  let T := S.standardFormRightMeshData
  let Y := CategoryTheory.linearYoneda k (T.VertexCategory (k := k))
  dsimp only
  exact congrArg Y.map
    (S.standardFormSimpleResolutionYonedaCoefficient_eq_comp_factor
      hP z x h t ht a).symm

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
