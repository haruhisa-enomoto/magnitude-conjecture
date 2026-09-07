import MagnitudeConjecture.Algebra.RightModuleMagnitudeEquality
import MagnitudeConjecture.CategoryTheory.FiniteConvexModuleThin
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleThin

/-!
# Universal and finite-stage thinness at equality

This file packages the fibrewise equality theorem as the frozen manuscript's
multiplicity-free statement and transports it through the full
extension-by-zero embedding from an object-deletion stage.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormMagnitudeEqualityThinQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormMagnitudeEqualityThinArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- At zero ambient surplus, every indecomposable finite-dimensional module
on the standard-form universal cover is pointwise thin. -/
theorem standardFormCovering_isPointwiseThin_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (M : CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) k)
    (hM : Indecomposable M) :
    CoveringHom.IsPointwiseThin M.obj.obj := by
  apply
    (CoveringHom.isPointwiseThin_iff_finrank_eq_one_of_not_isZero
      M.obj.obj M.property.1).2
  intro x hx
  exact
    standardFormCovering_finrank_obj_eq_one_of_ambientARSurplus_eq_zero
      S x₀ hconnected x hzero M hM hx

/-- Thinness also holds for every indecomposable finite-dimensional module on
an arbitrary object-deletion stage of the universal cover.  This is the
quotient-stage form needed for the finite-convex comparison in the frozen
proof. -/
theorem standardFormCoveringDeletion_isPointwiseThin_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (D : Set ((StandardFormProjectiveSourceCategory S x₀)ᵒᵖ))
    (M : CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := ObjectDeletion.DeletionCategory (k := k)
        ((StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) D) k)
    (hM : Indecomposable M) :
    CoveringHom.IsPointwiseThin M.obj.obj := by
  let C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
  let E := ObjectDeletion.finiteDimensionalModuleExtensionByZero
    (k := k) C D
  have hEM : Indecomposable (E.obj M) :=
    ObjectDeletion.finiteDimensionalModuleExtensionByZero_indec
      (k := k) C D M hM
  have hthin : CoveringHom.IsPointwiseThin (E.obj M).obj.obj :=
    standardFormCovering_isPointwiseThin_of_ambientARSurplus_eq_zero
      S x₀ hconnected hzero (E.obj M) hEM
  exact ObjectDeletion.isPointwiseThin_of_extensionByZero
    (k := k) C D M.obj hthin

/-- At equality, every indecomposable finite-dimensional module on a finite
convex full subcategory of the standard-form universal cover is pointwise
thin.  This is the literal finite-convex formulation used in the manuscript's
multiplicity-free-to-biserial step. -/
theorem
    standardFormCoveringFiniteConvex_isPointwiseThin_of_ambientARSurplus_eq_zero
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (hzero : S.ambientARSurplus = 0)
    (U : Set ((StandardFormProjectiveSourceCategory S x₀)ᵒᵖ))
    (hUfinite : U.Finite)
    (hUconvex : CoveringHom.IsConvexObjectSet
      (C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) U)
    (M : CoveringHom.FiniteDimensionalModuleCategory.{0, u, u, u}
      (C := ObjectDeletion.FullSubcategoryOn
        ((StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) U) k)
    (hM : Indecomposable M) :
    CoveringHom.IsPointwiseThin M.obj.obj := by
  let C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
  let H := standardFormOppositeProjectiveSourceCategoryIsLocallyBounded S x₀
  apply ObjectDeletion.fullSubcategory_isPointwiseThin_of_deletion
    (k := k) C H.skeletal U hUfinite hUconvex
  · intro N hN
    exact
      standardFormCoveringDeletion_isPointwiseThin_of_ambientARSurplus_eq_zero
        S x₀ hconnected hzero Uᶜ N hN
  · exact hM

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
