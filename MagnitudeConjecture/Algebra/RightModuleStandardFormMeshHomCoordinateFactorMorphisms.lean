import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactorMap

/-! # Named morphisms in the mesh coordinate-factor calculation -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateFactorMorphismsQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateFactorMorphismsArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The incoming mesh coordinate followed by the represented factor. -/
noncomputable def standardFormSimpleResolutionIncomingYonedaFactorComposite
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z x : Fin S.n)
    (t : MeshCategory.obj (k := k) S.standardFormRightMeshData z ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData x)
    (a : MeshCategory.RightMeshData.IncomingArrow z) :=
  let T := S.standardFormRightMeshData
  let Y := CategoryTheory.linearYoneda k (T.VertexCategory (k := k))
  T.incomingSummandInclusion (k := k) z a ≫
    T.incomingMap (k := k) z ≫ Y.map (InducedCategory.homMk t)

/-- The Yoneda image of the composite defining one lifted coordinate. -/
noncomputable def standardFormSimpleResolutionYonedaFactorComposite
    (z x : Fin S.n)
    (t : MeshCategory.obj (k := k) S.standardFormRightMeshData z ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData x)
    (a : MeshCategory.RightMeshData.IncomingArrow z) :=
  let T := S.standardFormRightMeshData
  let Y := CategoryTheory.linearYoneda k (T.VertexCategory (k := k))
  Y.map (InducedCategory.homMk (T.incomingArrowHom (k := k) a) ≫
    InducedCategory.homMk t)

/-- The Yoneda image of the coordinate extracted from the finite-module
morphism. -/
noncomputable def standardFormSimpleResolutionYonedaCoefficientMap
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (a : MeshCategory.RightMeshData.IncomingArrow z.1) :=
  let T := S.standardFormRightMeshData
  let Y := CategoryTheory.linearYoneda k (T.VertexCategory (k := k))
  Y.map (S.standardFormSimpleResolutionYonedaCoefficient hP z x h a)

/-- The underlying natural transformation of the original finite-module
coordinate composite. -/
noncomputable def standardFormSimpleResolutionFiniteCoordinateComposite
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (a : MeshCategory.RightMeshData.IncomingArrow z.1) :=
  (S.standardFormRightMeshData.incomingSummandInclusionFinite
    (k := k) hP z.1 a ≫ h).hom.hom

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
