import MagnitudeConjecture.Algebra.RightModuleStandardFormMeshHomCoordinateFactor

/-! # Reassembly from incoming biproduct coordinates -/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMeshHomCoordinateAssemblyQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMeshHomCoordinateAssemblyArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Equality on every incoming biproduct coordinate determines the whole
morphism. -/
theorem standardFormSimpleResolution_hom_eq_of_coordinates
    (hP : S.standardFormRightMeshData.FiniteContravariantRepresentables
      (k := k))
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    (x : Fin S.n)
    (h : S.standardFormRightMeshData.incomingCoefficientFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (b : S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP z.1 ⟶
        S.standardFormRightMeshData.contravariantRepresentableFiniteModule
          (k := k) hP x)
    (hcoordinate : ∀ a : MeshCategory.RightMeshData.IncomingArrow z.1,
      S.standardFormRightMeshData.incomingSummandInclusionFinite
          (k := k) hP z.1 a ≫
          S.standardFormRightMeshData.incomingMapFinite (k := k) hP z.1 ≫ b =
        S.standardFormRightMeshData.incomingSummandInclusionFinite
          (k := k) hP z.1 a ≫ h) :
    S.standardFormRightMeshData.incomingMapFinite (k := k) hP z.1 ≫ b = h := by
  classical
  let T := S.standardFormRightMeshData
  calc
    T.incomingMapFinite (k := k) hP z.1 ≫ b =
        (∑ a : MeshCategory.RightMeshData.IncomingArrow z.1,
          T.incomingSummandProjectionFinite (k := k) hP z.1 a ≫
            T.incomingSummandInclusionFinite (k := k) hP z.1 a) ≫
          (T.incomingMapFinite (k := k) hP z.1 ≫ b) := by
      rw [T.sum_incomingSummandProjectionFinite_comp_inclusion, Category.id_comp]
    _ = ∑ a : MeshCategory.RightMeshData.IncomingArrow z.1,
        T.incomingSummandProjectionFinite (k := k) hP z.1 a ≫
          (T.incomingSummandInclusionFinite (k := k) hP z.1 a ≫
            T.incomingMapFinite (k := k) hP z.1 ≫ b) := by
      rw [Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro a _
      simp only [Category.assoc]
    _ = ∑ a : MeshCategory.RightMeshData.IncomingArrow z.1,
        T.incomingSummandProjectionFinite (k := k) hP z.1 a ≫
          (T.incomingSummandInclusionFinite (k := k) hP z.1 a ≫ h) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hcoordinate a]
    _ = (∑ a : MeshCategory.RightMeshData.IncomingArrow z.1,
          T.incomingSummandProjectionFinite (k := k) hP z.1 a ≫
            T.incomingSummandInclusionFinite (k := k) hP z.1 a) ≫ h := by
      rw [Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro a _
      simp only [Category.assoc]
    _ = h := by
      rw [T.sum_incomingSummandProjectionFinite_comp_inclusion, Category.id_comp]

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
