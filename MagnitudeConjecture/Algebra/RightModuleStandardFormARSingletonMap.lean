import MagnitudeConjecture.Algebra.RightModuleStandardFormARIncoming

/-!
# Restricted Yoneda on singleton additive-hull morphisms
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormARSingletonMapQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARSingletonMapArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

set_option backward.isDefEq.respectTransparency false in
/-- Mapping a singleton additive-hull matrix and transporting across the two
singleton identifications recovers the original restricted-Yoneda map. -/
theorem standardFormAdditiveRestrictedYoneda_singleton_map
    (x z : Fin S.n)
    (f : MeshCategory.obj (k := k) S.standardFormRightMeshData x ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData z) :
    (S.standardFormAdditiveRestrictedYonedaSingletonIso (k := k) x).inv ≫
        (S.standardFormAdditiveRestrictedYonedaFunctor (k := k)).map
          ((S.standardFormRightMeshData.additiveVertexHomLinearEquiv
            (k := k) x z).symm f) ≫
      (S.standardFormAdditiveRestrictedYonedaSingletonIso (k := k) z).hom =
    (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).map f := by
  dsimp only [standardFormAdditiveRestrictedYonedaSingletonIso,
    standardFormAdditiveRestrictedYonedaFunctor,
    standardFormVertexRestrictedYonedaFunctor,
    standardFormMeshRawFunctor, finiteMatrixLift,
    MeshCategory.RightMeshData.additiveVertexHomLinearEquiv,
    MeshCategory.RightMeshData.additiveVertexObj, Mat_.embedding]
  simp only [id_eq, biproductUniqueIso_inv, biproductUniqueIso_hom]
  rw [biproduct.lift_matrix_assoc, biproduct.lift_desc]
  simp

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
