import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshExact

/-! # Yoneda coefficient data for the standard-form mesh resolution -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshYonedaDataQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshYonedaDataArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The mesh-category morphism represented by one coordinate of a morphism
out of the incoming coefficient module. -/
noncomputable def standardFormSimpleResolutionYonedaCoefficient
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (a : MeshCategory.RightMeshData.IncomingArrow z.1) :
    (show S.standardFormRightMeshData.VertexCategory (k := k) from a.1) ⟶
      (show S.standardFormRightMeshData.VertexCategory (k := k) from x) :=
  (CategoryTheory.linearYoneda k
    (S.standardFormRightMeshData.VertexCategory (k := k))).preimage
      ((S.standardFormRightMeshData.incomingSummandInclusionFinite
        (k := k) hP z.1 a ≫ h).hom.hom)

/-- The polarized partner of an incoming arrow in the induced vertex
category. -/
noncomputable def standardFormSimpleResolutionPairedIncoming
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (a : MeshCategory.RightMeshData.IncomingArrow z.1) :
    (show S.standardFormRightMeshData.VertexCategory (k := k) from
        S.standardFormRightMeshData.tau z) ⟶
      (show S.standardFormRightMeshData.VertexCategory (k := k) from a.1) :=
  InducedCategory.homMk
    (S.standardFormRightMeshData.incomingArrowHom (k := k)
      (⟨S.standardFormRightMeshData.tau z,
        S.standardFormRightMeshData.arrowEquiv z a.1 a.2⟩ :
        MeshCategory.RightMeshData.IncomingArrow a.1))

@[simp]
theorem linearYoneda_map_standardFormSimpleResolutionYonedaCoefficient
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (a : MeshCategory.RightMeshData.IncomingArrow z.1) :
    (CategoryTheory.linearYoneda k
      (S.standardFormRightMeshData.VertexCategory (k := k))).map
        (S.standardFormSimpleResolutionYonedaCoefficient hP z x h a) =
      (S.standardFormRightMeshData.incomingSummandInclusionFinite
        (k := k) hP z.1 a ≫ h).hom.hom :=
  (CategoryTheory.linearYoneda k
    (S.standardFormRightMeshData.VertexCategory (k := k))).map_preimage _

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
