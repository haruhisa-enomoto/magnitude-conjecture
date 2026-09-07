import MagnitudeConjecture.Algebra.RightModuleStandardFormARIncoming
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteAlmostSplit
import MagnitudeConjecture.CategoryTheory.FiniteMeshEndLocal

/-!
# Positive-length form of a nonsplit recovered morphism

A nonsplit morphism between recovered standard-form vertices has no nonzero
degree-zero scalar term, so its mesh-category preimage is an incoming sum.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormARIncomingPreimageQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormARIncomingPreimageArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- A nonsplit recovered morphism has an incoming-sum preimage in the mesh
category. -/
theorem exists_standardFormIncomingCoefficient_preimage_eq_incomingSum
    (x z : Fin S.n)
    (q : (S.standardFormProjectiveVertexModuleIndecomposableSkeleton
          (k := k)).obj x ⟶
        (S.standardFormProjectiveVertexModuleIndecomposableSkeleton
          (k := k)).obj z)
    (hq : ¬ IsSplitEpi q) :
    ∃ coeff : MeshCategory.RightMeshData.IncomingCoefficient
        (k := k) S.standardFormRightMeshData x z,
      (S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite).preimage q =
        S.standardFormRightMeshData.incomingSum (k := k) coeff := by
  let T := S.standardFormRightMeshData
  let Y := S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite
  let r : MeshCategory.obj (k := k) T x ⟶
      MeshCategory.obj (k := k) T z := Y.preimage q
  obtain ⟨c, coeff, hr⟩ :=
    T.exists_eq_diagonalScalar_add_incomingSum r
  have hrFactor : r = T.incomingSum (k := k) coeff := by
    by_cases hx : x = z
    · subst x
      have hc : c = 0 := by
        by_contra hc
        letI : FiniteDimensional k
            (End (MeshCategory.obj (k := k) T z)) :=
          S.standardFormMeshHomFinite _ _
        have htail : T.incomingSum (k := k) coeff ∈
            MeshCategory.lengthTail (k := k) T z z 1 :=
          T.incomingSum_mem_lengthTail_one (k := k) coeff
        have hIso : IsIso
            (c • 𝟙 (MeshCategory.obj (k := k) T z) +
              T.incomingSum (k := k) coeff) :=
          MeshCategory.isIso_smul_id_add_of_mem_lengthTail_one
            (k := k) T z c hc (T.incomingSum (k := k) coeff) htail
        have hRIso : IsIso r := by
          rw [hr, T.diagonalScalar_self]
          exact hIso
        letI : IsIso r := hRIso
        apply hq
        haveI : IsIso (Y.map r) := Y.map_isIso r
        have hMap : Y.map r = q := by
          dsimp only [r]
          exact Y.map_preimage q
        have hsplitMap : IsSplitEpi (Y.map r) :=
          IsSplitEpi.mk'
            { section_ := inv (Y.map r)
              id := IsIso.inv_hom_id (Y.map r) }
        rw [hMap] at hsplitMap
        exact hsplitMap
      rw [hr, T.diagonalScalar_self, hc, zero_smul, zero_add]
    · rw [hr]
      simp [MeshCategory.RightMeshData.diagonalScalar, hx]
  exact ⟨coeff, hrFactor⟩

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
