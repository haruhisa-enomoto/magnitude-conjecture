import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshYonedaRawRelation

/-!
# Yoneda lifting for the standard-form mesh resolution

The reflected raw relation is lifted through mesh exactness.  This final stage
is kept separate from the expensive Yoneda calculation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshYonedaLiftQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshYonedaLiftArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- A morphism out of the incoming coefficient module which kills the
translation map is induced by a single morphism in the mesh category. -/
theorem standardFormSimpleResolution_yoneda_lift
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (hh : S.standardFormRightMeshData.translationMapFinite (k := k) hP z ≫ h = 0) :
    ∃ t : MeshCategory.obj (k := k) S.standardFormRightMeshData z.1 ⟶
        MeshCategory.obj (k := k) S.standardFormRightMeshData x,
      ∀ a : MeshCategory.RightMeshData.IncomingArrow z.1,
        (S.standardFormSimpleResolutionYonedaCoefficient hP z x h a).hom =
          S.standardFormRightMeshData.incomingArrowHom (k := k) a ≫ t := by
  have hcRaw :=
    S.standardFormSimpleResolution_yoneda_raw_relation hP z x h hh
  exact S.standardFormMesh_nonprojective_outgoing_exact
    z x
      (fun a ↦ (S.standardFormSimpleResolutionYonedaCoefficient hP z x h a).hom)
      hcRaw

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
