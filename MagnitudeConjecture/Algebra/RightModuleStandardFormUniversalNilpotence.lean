import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalCovering
import MagnitudeConjecture.CategoryTheory.LinearPathIdealPower

/-!
# Uniform path nilpotence on the standard-form universal mesh

Path evaluation sends a string of arrows in a Hom ideal into the corresponding
ideal power. Applied to the normalized universal-cover realization and the
nilpotent categorical radical of a representation-finite module category,
this gives one uniform length bound above which all universal mesh paths
vanish.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

open QuotientSubmoduleEquidistribution.CategoricalIdeal

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalNilpotenceQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalNilpotenceArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormUniversalNilpotenceStarFintype
    (x₀ : Fin S.n) :
    ∀ W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀, Fintype (Quiver.Star W) :=
  (MeshCategory.RightMeshData.UniversalCover.cover
    S.standardFormRightMeshData x₀).sourceStarFintype

/-- Paths in the normalized universal-cover mesh category vanish above one
uniform length bound. -/
theorem exists_standardFormUniversal_pathHom_eq_zero
    (x₀ : Fin S.n) :
    ∃ N : ℕ,
      ∀ {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
          S.standardFormRightMeshData x₀}
        (p : Quiver.Path Y Z), N ≤ p.length →
        (MeshCategory.quotientFunctor (k := k)
          (MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData x₀)).map
          (LinearPathCategory.pathHom (k := k) p) = 0 := by
  obtain ⟨N, hN⟩ := S.fgNilpotentRadicalData.nilpotent
  refine ⟨N, ?_⟩
  intro Y Z p hp
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  let F := S.standardFormUniversalIndecMeshFunctor x₀
  apply (S.standardFormUniversalIndecMeshFunctor_isCovering x₀).map_injective
  rw [F.map_zero]
  apply InducedCategory.hom_ext
  change (S.standardFormUniversalMeshFunctor x₀).map
      ((MeshCategory.quotientFunctor (k := k) T).map
        (LinearPathCategory.pathHom (k := k) p)) = 0
  rw [(S.standardFormUniversalRealization x₀).functor_map_quotient_map]
  rw [LinearPathCategory.lift_map_pathHom]
  change LinearPathCategory.pathMap (S.standardFormUniversalObj x₀)
      (S.standardFormUniversalNormalizedArrowMap x₀) p = 0
  have hpath := LinearPathCategory.pathMap_mem_ideal_pow
    (S.standardFormUniversalObj x₀)
    (S.standardFormUniversalNormalizedArrowMap x₀)
    S.fgNilpotentRadicalData.ideal
    (fun {Y Z} a ↦ by
      change S.standardFormUniversalNormalizedArrowMap x₀ a ∈
        S.fgNilpotentRadicalData.ideal.hom
          (S.fgObj Z.1) (S.fgObj Y.1)
      apply (S.fgNilpotentRadicalData.mem_ideal_iff _).2
      apply (S.finiteTauCategoryData.isRadicalMorphism_iff_not_isSplitEpi_to_obj
        _).2
      exact (S.standardFormUniversalNormalizedArrowMap_isIrreducible x₀ a)
        |>.not_isSplitEpi)
    p
  have hpathN : LinearPathCategory.pathMap
      (S.standardFormUniversalObj x₀)
      (S.standardFormUniversalNormalizedArrowMap x₀) p ∈
        (S.fgNilpotentRadicalData.ideal.pow N).hom
          (S.standardFormUniversalObj x₀ Z)
          (S.standardFormUniversalObj x₀ Y) :=
    (HomIdeal.pow_le_pow_of_le S.fgNilpotentRadicalData.ideal hp)
      _ _ hpath
  rw [hN] at hpathN
  exact hpathN

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
