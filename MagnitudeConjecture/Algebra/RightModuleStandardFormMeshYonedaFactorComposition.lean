import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshYonedaLift

/-! # Composition of an incoming mesh coordinate with a Yoneda factor -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshYonedaFactorCompositionQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshYonedaFactorCompositionArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- Composition with an incoming mesh coordinate is carried by linear Yoneda
to composition in the induced vertex category. -/
theorem standardFormIncoming_comp_yonedaFactor
    (z x : Fin S.n)
    (a : MeshCategory.RightMeshData.IncomingArrow z)
    (t : MeshCategory.obj (k := k) S.standardFormRightMeshData z ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData x) :
    let T := S.standardFormRightMeshData
    let Y := CategoryTheory.linearYoneda k (T.VertexCategory (k := k))
    T.incomingSummandInclusion (k := k) z a ≫
        T.incomingMap (k := k) z ≫ Y.map (InducedCategory.homMk t) =
      Y.map (InducedCategory.homMk (T.incomingArrowHom (k := k) a) ≫
        InducedCategory.homMk t) := by
  let T := S.standardFormRightMeshData
  let Y := CategoryTheory.linearYoneda k (T.VertexCategory (k := k))
  dsimp only
  rw [← Category.assoc, T.incomingSummandInclusion_comp_incomingMap]
  rw [← Y.map_comp]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
