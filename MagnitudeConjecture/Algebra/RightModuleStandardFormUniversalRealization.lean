import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalDualNormalization
import MagnitudeConjecture.CategoryTheory.MeshRealization

/-!
# Realization of the normalized standard-form universal cover

The two-sided Bongartz--Gabriel normalization assigns an irreducible module
morphism to every reversed universal-cover arrow and makes every realized
mesh composite literally zero.  Here that assignment is extended to the free
linear path category and descended through the ordinary mesh ideal.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalRealizationQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalRealizationArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormUniversalRealizationBaseStarFintype
    (x : Fin S.n) : Fintype (Quiver.Star x) := by
  infer_instance

noncomputable local instance standardFormUniversalRealizationStarFintype
    (x₀ : Fin S.n) :
    ∀ W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀, Fintype (Quiver.Star W) :=
  (MeshCategory.RightMeshData.UniversalCover.cover
    S.standardFormRightMeshData x₀).sourceStarFintype

set_option backward.isDefEq.respectTransparency false in
/-- The free linear path realization sends a lifted mesh relation to the
composite of its reassembled normalized source and sink. -/
theorem standardFormUniversalNormalized_lift_map_meshRelation
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    (LinearPathCategory.lift (k := k)
      (S.standardFormUniversalObj x₀)
      (S.standardFormUniversalNormalizedArrowMap x₀)).map
        ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀).meshRelation (k := k) W) =
      S.standardFormUniversalRealizedSource x₀
          (S.standardFormUniversalNormalizedArrowMap x₀) W ≫
        S.standardFormUniversalRealizedSink x₀
          (S.standardFormUniversalNormalizedArrowMap x₀) W.1 := by
  classical
  rw [MeshCategory.RightMeshData.meshRelation, Functor.map_sum]
  simp_rw [LinearPathCategory.lift_map_pathHom]
  simp only [MeshCategory.RightMeshData.meshPath]
  simp_rw [LinearPathCategory.pathMap_comp]
  simp only [Quiver.Hom.toPath, LinearPathCategory.pathMap_cons,
    LinearPathCategory.pathMap_nil, Category.comp_id]
  change (∑ a : Quiver.Star W.1,
      S.standardFormUniversalNormalizedArrowMap x₀
          (MeshCategory.RightMeshData.UniversalCover.pairedArrow
            S.standardFormRightMeshData x₀ W a.1 a.2) ≫
        S.standardFormUniversalNormalizedArrowMap x₀ a.2) = _
  unfold standardFormUniversalRealizedSource
    standardFormUniversalRealizedSink
  rw [Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_desc]
  let e := S.standardFormUniversalMiddleStarEquiv x₀ W.1
  have hreindex := e.sum_comp (fun a : Quiver.Star W.1 ↦
    S.standardFormUniversalNormalizedArrowMap x₀
        (MeshCategory.RightMeshData.UniversalCover.pairedArrow
          S.standardFormRightMeshData x₀ W a.1 a.2) ≫
      S.standardFormUniversalNormalizedArrowMap x₀ a.2)
  rw [← hreindex]
  apply Finset.sum_congr rfl
  intro i _
  rw [S.standardFormUniversalMiddleStarEquiv_apply]
  rfl

/-- The normalized free realization kills every lifted mesh relation. -/
theorem standardFormUniversalNormalized_lift_map_meshRelation_zero
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    (LinearPathCategory.lift (k := k)
      (S.standardFormUniversalObj x₀)
      (S.standardFormUniversalNormalizedArrowMap x₀)).map
        ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀).meshRelation (k := k) W) = 0 := by
  rw [S.standardFormUniversalNormalized_lift_map_meshRelation x₀ W]
  exact S.standardFormUniversalNormalized_mesh_zero x₀ W

set_option backward.isDefEq.respectTransparency false in
/-- The normalized arrow assignment as a realization of the ordinary mesh
category of the standard-form universal cover. -/
def standardFormUniversalRealization (x₀ : Fin S.n) :
    MeshCategory.Realization (k := k)
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀)
      (S.standardFormUniversalObj x₀) where
  arrowMap := S.standardFormUniversalNormalizedArrowMap x₀
  map_meshRelation := by
    intro W
    exact S.standardFormUniversalNormalized_lift_map_meshRelation_zero x₀ W

/-- The induced linear functor from the raw universal-cover mesh category to
finitely generated right modules. -/
abbrev standardFormUniversalMeshFunctor (x₀ : Fin S.n) :=
  (S.standardFormUniversalRealization x₀).functor

/-- The free realization sends a one-arrow path to its chosen normalized
irreducible representative. -/
@[simp]
theorem standardFormUniversalRealization_freeFunctor_map_arrow
    (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z) :
    (S.standardFormUniversalRealization x₀).freeFunctor.map
        (LinearPathCategory.pathHom (k := k) a.toPath) =
      S.standardFormUniversalNormalizedArrowMap x₀ a := by
  rw [LinearPathCategory.lift_map_pathHom]
  change LinearPathCategory.pathMap (S.standardFormUniversalObj x₀)
      (S.standardFormUniversalNormalizedArrowMap x₀) a.toPath = _
  simp [Quiver.Hom.toPath]

/-- The descended mesh functor has the same value on each represented
universal-cover arrow. -/
@[simp]
theorem standardFormUniversalMeshFunctor_map_arrow
    (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z) :
    (S.standardFormUniversalMeshFunctor x₀).map
        ((MeshCategory.quotientFunctor (k := k)
          (MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData x₀)).map
          (LinearPathCategory.pathHom (k := k) a.toPath)) =
      S.standardFormUniversalNormalizedArrowMap x₀ a := by
  exact S.standardFormUniversalRealization_freeFunctor_map_arrow x₀ a

/-- In particular, every represented mesh-category arrow is sent to an
irreducible module morphism. -/
theorem standardFormUniversalMeshFunctor_map_arrow_isIrreducible
    (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z) :
    IsIrreducibleMorphism
      ((S.standardFormUniversalMeshFunctor x₀).map
        ((MeshCategory.quotientFunctor (k := k)
          (MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData x₀)).map
          (LinearPathCategory.pathHom (k := k) a.toPath))) := by
  rw [S.standardFormUniversalMeshFunctor_map_arrow]
  exact S.standardFormUniversalNormalizedArrowMap_isIrreducible x₀ a

/-- At every lifted vertex, including projective boundary vertices, the
normalized incoming components reassemble to a right almost-split sink. -/
theorem standardFormUniversalNormalizedRealizedSink_isRightAlmostSplit
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    IsRightAlmostSplit
      (S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W) := by
  let h := MeshCategory.RightMeshData.UniversalCover.vertexHeight
    S.standardFormRightMeshData x₀ W - 1
  by_cases hp : 0 < h
  · have heq :
        S.standardFormUniversalRealizedSink x₀
            (S.standardFormUniversalNormalizedArrowMap x₀) W =
          S.standardFormUniversalRealizedSink x₀
            (S.standardFormUniversalPositiveArrowMap x₀) W := by
      unfold standardFormUniversalRealizedSink
      congr 1
      apply congrArg biproduct.desc
      funext i
      apply S.standardFormUniversalNormalizedArrowMap_eq_positive
      have hi :=
        MeshCategory.RightMeshData.UniversalCover.vertexHeight_arrow
          S.standardFormRightMeshData x₀
            (S.standardFormUniversalMiddleArrow x₀ W i)
      dsimp only [h] at hp
      omega
    rw [heq]
    exact (S.standardFormUniversalPositiveArrowMap_sinkCondition x₀)
      |>.rightAlmostSplit W
  · have hn : h = -((h.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hp)]
      omega
    have heq :
        S.standardFormUniversalRealizedSink x₀
            (S.standardFormUniversalNormalizedArrowMap x₀) W =
          S.standardFormUniversalRealizedSink x₀
            (S.standardFormUniversalNonpositiveStage x₀
              (h.natAbs + 1)).arrowMap W := by
      unfold standardFormUniversalRealizedSink
      congr 1
      apply congrArg biproduct.desc
      funext i
      apply S.standardFormUniversalNormalizedArrowMap_eq_stage_succ
        x₀ h.natAbs
      have hi :=
        MeshCategory.RightMeshData.UniversalCover.vertexHeight_arrow
          S.standardFormRightMeshData x₀
            (S.standardFormUniversalMiddleArrow x₀ W i)
      dsimp only [h] at hn
      omega
    rw [heq]
    exact (S.standardFormUniversalNonpositiveStage x₀ (h.natAbs + 1))
      |>.sourceCondition.realizedSink_isRightAlmostSplit S x₀ W

/-- The normalized incoming sink is also right minimal at every lifted
vertex.  This is the second half of the local Auslander--Reiten datum used
when comparing its kernel with the normalized mesh source. -/
theorem standardFormUniversalNormalizedRealizedSink_isRightMinimal
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    IsRightMinimal
      (S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W) := by
  let h := MeshCategory.RightMeshData.UniversalCover.vertexHeight
    S.standardFormRightMeshData x₀ W - 1
  by_cases hp : 0 < h
  · have heq :
        S.standardFormUniversalRealizedSink x₀
            (S.standardFormUniversalNormalizedArrowMap x₀) W =
          S.standardFormUniversalRealizedSink x₀
            (S.standardFormUniversalPositiveArrowMap x₀) W := by
      unfold standardFormUniversalRealizedSink
      congr 1
      apply congrArg biproduct.desc
      funext i
      apply S.standardFormUniversalNormalizedArrowMap_eq_positive
      have hi :=
        MeshCategory.RightMeshData.UniversalCover.vertexHeight_arrow
          S.standardFormRightMeshData x₀
            (S.standardFormUniversalMiddleArrow x₀ W i)
      dsimp only [h] at hp
      omega
    rw [heq]
    exact (S.standardFormUniversalPositiveArrowMap_sinkCondition x₀)
      |>.rightMinimal W
  · have hn : h = -((h.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hp)]
      omega
    have heq :
        S.standardFormUniversalRealizedSink x₀
            (S.standardFormUniversalNormalizedArrowMap x₀) W =
          S.standardFormUniversalRealizedSink x₀
            (S.standardFormUniversalNonpositiveStage x₀
              (h.natAbs + 1)).arrowMap W := by
      unfold standardFormUniversalRealizedSink
      congr 1
      apply congrArg biproduct.desc
      funext i
      apply S.standardFormUniversalNormalizedArrowMap_eq_stage_succ
        x₀ h.natAbs
      have hi :=
        MeshCategory.RightMeshData.UniversalCover.vertexHeight_arrow
          S.standardFormRightMeshData x₀
            (S.standardFormUniversalMiddleArrow x₀ W i)
      dsimp only [h] at hn
      omega
    rw [heq]
    let hD := (S.standardFormUniversalNonpositiveStage x₀
      (h.natAbs + 1)).sourceCondition
    rw [← hD.realizedSinkIso_comp_rightSink S x₀ W]
    exact rightMinimal_precomp_iso
      (S.standardFormRightSink_isRightMinimal W.1)
      (hD.realizedSinkIso S x₀ W)

/-- At a nonprojective lifted vertex, the normalized mesh source remains
left almost split. -/
theorem standardFormUniversalNormalizedRealizedSource_isLeftAlmostSplit
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    IsLeftAlmostSplit
      (S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W) := by
  let h := MeshCategory.RightMeshData.UniversalCover.vertexHeight
    S.standardFormRightMeshData x₀
      (MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ W)
  by_cases hp : 0 < h
  · have heq :
        S.standardFormUniversalRealizedSource x₀
            (S.standardFormUniversalNormalizedArrowMap x₀) W =
          S.standardFormUniversalRealizedSource x₀
            (S.standardFormUniversalPositiveArrowMap x₀) W := by
      unfold standardFormUniversalRealizedSource
      congr 1
      apply congrArg biproduct.lift
      funext i
      exact S.standardFormUniversalNormalizedArrowMap_eq_positive
        x₀ hp (S.standardFormUniversalPairedMiddleArrow x₀ W i)
    rw [heq]
    exact (S.standardFormUniversalPositiveArrowMap_sourceCondition x₀)
      |>.leftAlmostSplit W
  · have hn : h = -((h.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hp)]
      omega
    rw [S.standardFormUniversalNormalizedRealizedSource_eq_stage_succ
      x₀ h.natAbs W hn]
    exact (S.standardFormUniversalNonpositiveStage x₀ (h.natAbs + 1))
      |>.sourceCondition.leftAlmostSplit W

/-- At a nonprojective lifted vertex, the normalized mesh source remains
left minimal. -/
theorem standardFormUniversalNormalizedRealizedSource_isLeftMinimal
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    IsLeftMinimal
      (S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W) := by
  let h := MeshCategory.RightMeshData.UniversalCover.vertexHeight
    S.standardFormRightMeshData x₀
      (MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ W)
  by_cases hp : 0 < h
  · have heq :
        S.standardFormUniversalRealizedSource x₀
            (S.standardFormUniversalNormalizedArrowMap x₀) W =
          S.standardFormUniversalRealizedSource x₀
            (S.standardFormUniversalPositiveArrowMap x₀) W := by
      unfold standardFormUniversalRealizedSource
      congr 1
      apply congrArg biproduct.lift
      funext i
      exact S.standardFormUniversalNormalizedArrowMap_eq_positive
        x₀ hp (S.standardFormUniversalPairedMiddleArrow x₀ W i)
    rw [heq]
    exact (S.standardFormUniversalPositiveArrowMap_sourceCondition x₀)
      |>.leftMinimal W
  · have hn : h = -((h.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonpos (le_of_not_gt hp)]
      omega
    rw [S.standardFormUniversalNormalizedRealizedSource_eq_stage_succ
      x₀ h.natAbs W hn]
    exact (S.standardFormUniversalNonpositiveStage x₀ (h.natAbs + 1))
      |>.sourceCondition.leftMinimal W

/-- The full category on the chosen finite skeleton, bundled inside the
literal finitely generated module category.  This is a definition rather
than an abbreviation so that its induced category structure remains
distinct from the quiver structure on the same finite label type. -/
def FGIndecCategory :=
  InducedCategory (RightModule.FinitelyGeneratedCategory A) S.fgObj

noncomputable instance fgIndecCategoryCategory :
    CategoryTheory.Category S.FGIndecCategory := by
  exact inferInstanceAs (CategoryTheory.Category
    (InducedCategory (RightModule.FinitelyGeneratedCategory A) S.fgObj))

noncomputable instance fgIndecCategoryPreadditive :
    Preadditive S.FGIndecCategory := by
  exact inferInstanceAs (Preadditive
    (InducedCategory (RightModule.FinitelyGeneratedCategory A) S.fgObj))

noncomputable instance fgIndecCategoryLinear :
    Linear k S.FGIndecCategory := by
  exact inferInstanceAs (Linear k
    (InducedCategory (RightModule.FinitelyGeneratedCategory A) S.fgObj))

/-- The same universal mesh realization, with its codomain corestricted to
the finite skeletal category of indecomposable finitely generated modules.
This is the precise codomain in Riedtmann's covering theorem. -/
def standardFormUniversalIndecMeshFunctor (x₀ : Fin S.n) :
    MeshCategory.RawCategory (k := k)
        (MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀) ⥤
      S.FGIndecCategory where
  obj X :=
    (LinearPathCategory.vertex X.as).1
  map f := InducedCategory.homMk
    ((S.standardFormUniversalMeshFunctor x₀).map f)
  map_id X := by
    apply InducedCategory.hom_ext
    change
      (S.standardFormUniversalMeshFunctor x₀).map (𝟙 X) =
        𝟙 ((S.standardFormUniversalMeshFunctor x₀).obj X)
    exact (S.standardFormUniversalMeshFunctor x₀).map_id X
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (S.standardFormUniversalMeshFunctor x₀).map_comp f g

noncomputable instance standardFormUniversalIndecMeshFunctor_additive
    (x₀ : Fin S.n) :
    (S.standardFormUniversalIndecMeshFunctor x₀).Additive where
  map_add := by
    intro X Y f g
    apply InducedCategory.hom_ext
    change
      (S.standardFormUniversalMeshFunctor x₀).map (f + g) =
        (S.standardFormUniversalMeshFunctor x₀).map f +
          (S.standardFormUniversalMeshFunctor x₀).map g
    simp

noncomputable instance standardFormUniversalIndecMeshFunctor_linear
    (x₀ : Fin S.n) :
    (S.standardFormUniversalIndecMeshFunctor x₀).Linear k where
  map_smul f r := by
    apply InducedCategory.hom_ext
    change
      (S.standardFormUniversalMeshFunctor x₀).map (r • f) =
        r • (S.standardFormUniversalMeshFunctor x₀).map f
    simp

/-- Corestriction does not alter the represented normalized arrow map. -/
@[simp]
theorem standardFormUniversalIndecMeshFunctor_map_arrow
    (x₀ : Fin S.n)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : Y ⟶ Z) :
    ((S.standardFormUniversalIndecMeshFunctor x₀).map
        ((MeshCategory.quotientFunctor (k := k)
          (MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData x₀)).map
          (LinearPathCategory.pathHom (k := k) a.toPath))).hom =
      S.standardFormUniversalNormalizedArrowMap x₀ a := by
  exact S.standardFormUniversalMeshFunctor_map_arrow x₀ a

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
