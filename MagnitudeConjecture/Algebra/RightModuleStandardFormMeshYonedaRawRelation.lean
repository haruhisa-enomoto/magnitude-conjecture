import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshYonedaReflectedRelation

/-! # The raw standard-form mesh relation -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshYonedaRawRelationQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshYonedaRawRelationArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- The reflected relation after passing from the induced category to raw
mesh-category morphisms. -/
theorem standardFormSimpleResolution_yoneda_raw_relation
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (hh : S.standardFormRightMeshData.translationMapFinite (k := k) hP z ≫ h = 0) :
    (∑ a : MeshCategory.RightMeshData.IncomingArrow z.1,
      S.standardFormRightMeshData.incomingArrowHom (k := k)
          (⟨S.standardFormRightMeshData.tau z,
            S.standardFormRightMeshData.arrowEquiv z a.1 a.2⟩ :
            MeshCategory.RightMeshData.IncomingArrow a.1) ≫
        (S.standardFormSimpleResolutionYonedaCoefficient hP z x h a).hom) = 0 := by
  have hc := S.standardFormSimpleResolution_yoneda_reflected_relation hP z x h hh
  have hraw := congrArg (InducedCategory.homLinearEquiv (R := k)) hc
  change (InducedCategory.homLinearEquiv (R := k))
      (∑ a : MeshCategory.RightMeshData.IncomingArrow z.1,
        S.standardFormSimpleResolutionPairedIncoming z a ≫
          S.standardFormSimpleResolutionYonedaCoefficient hP z x h a) =
    (InducedCategory.homLinearEquiv (R := k)) 0 at hraw
  rw [map_sum, map_zero] at hraw
  simpa only [InducedCategory.homLinearEquiv_apply,
    InducedCategory.comp_hom, standardFormSimpleResolutionPairedIncoming,
    InducedCategory.homMk_hom] using hraw

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
