import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshYonedaFactorComposition

/-! # The represented factor in the standard mesh-simple resolution -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateFactorMapQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateFactorMapArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The finite representable morphism induced by a morphism between the
corresponding vertices of the mesh category. -/
noncomputable def standardFormSimpleResolutionYonedaFactor
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z x : Fin S.n)
    (t : MeshCategory.obj (k := k) S.standardFormRightMeshData z ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData x) :
    S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP z ⟶
      S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x :=
  ObjectProperty.homMk (ObjectProperty.homMk
    ((CategoryTheory.linearYoneda k
      (S.standardFormRightMeshData.VertexCategory (k := k))).map
        (InducedCategory.homMk t)))

/-- The underlying natural transformation of the represented factor is the
Yoneda image of its mesh-category morphism. -/
theorem standardFormSimpleResolutionYonedaFactor_hom_hom
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z x : Fin S.n)
    (t : MeshCategory.obj (k := k) S.standardFormRightMeshData z ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData x) :
    (S.standardFormSimpleResolutionYonedaFactor hP z x t).hom.hom =
      (CategoryTheory.linearYoneda k
        (S.standardFormRightMeshData.VertexCategory (k := k))).map
          (InducedCategory.homMk t) :=
  rfl

/-- A lifted raw mesh factor gives the corresponding equality in the induced
vertex category. -/
theorem standardFormSimpleResolutionYonedaCoefficient_eq_comp_factor
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
    S.standardFormSimpleResolutionYonedaCoefficient hP z x h a =
      InducedCategory.homMk
          (S.standardFormRightMeshData.incomingArrowHom (k := k) a) ≫
        InducedCategory.homMk t := by
  apply InducedCategory.hom_ext
  exact ht a

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
