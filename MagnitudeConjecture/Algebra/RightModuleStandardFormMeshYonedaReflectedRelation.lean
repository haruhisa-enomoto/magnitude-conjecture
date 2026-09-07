import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshYonedaData
import MagnitudeConjecture.CategoryTheory.MeshYonedaRelation

/-!
# The reflected Yoneda mesh relation

The generic linear-Yoneda relation lemma reflects the translation relation
without repeating the finite-sum calculation for standard-form objects.
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

local instance standardFormMeshYonedaReflectedRelationQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshYonedaReflectedRelationArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The relation killed by the translation map reflects through the linear
Yoneda embedding. -/
theorem standardFormSimpleResolution_yoneda_reflected_relation
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
      S.standardFormSimpleResolutionPairedIncoming z a ≫
        S.standardFormSimpleResolutionYonedaCoefficient hP z x h a) = 0 := by
  exact S.standardFormRightMeshData.yoneda_reflected_relation hP z x h hh

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
