import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalRealization
import MagnitudeConjecture.Algebra.RightModuleRadical
import MagnitudeConjecture.CategoryTheory.AlgebraicallyClosedOccurrenceBasis
import MagnitudeConjecture.CategoryTheory.AlgebraicallyClosedResidue
import MagnitudeConjecture.CategoryTheory.LinearCovering
import MagnitudeConjecture.CategoryTheory.MeshIncomingDecomposition
import MagnitudeConjecture.CategoryTheory.MeshPairedRelation
import MagnitudeConjecture.CategoryTheory.MeshPositiveTail

/-!
# Riedtmann covering theorem for the normalized universal realization

This file implements the radical-layer argument of Riedtmann, Proposition
2.3, for the normalized standard-form universal mesh functor.  The right
almost-split half first approximates every fixed-target morphism by lifted
mesh paths modulo successive powers of the categorical radical.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical
open QuotientSubmoduleEquidistribution.CategoricalIdeal

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalCoveringQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalCoveringArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormUniversalCoveringStarFintype
    (x₀ : Fin S.n) :
    ∀ W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀, Fintype (Quiver.Star W) :=
  (MeshCategory.RightMeshData.UniversalCover.cover
    S.standardFormRightMeshData x₀).sourceStarFintype

noncomputable local instance standardFormUniversalCoveringCostarFintype
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) : Fintype (Quiver.Costar W) :=
  Fintype.ofEquiv
    (Quiver.Costar
      ((MeshCategory.RightMeshData.UniversalCover.projection
        S.standardFormRightMeshData x₀).obj W))
    (Equiv.ofBijective
      ((MeshCategory.RightMeshData.UniversalCover.projection
        S.standardFormRightMeshData x₀).costar W)
      (MeshCategory.RightMeshData.UniversalCover.projection_costar_bijective
        S.standardFormRightMeshData x₀ W)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The scalar residue remainder of an endomorphism of a chosen
indecomposable is radical, hence is not split epic. -/
theorem standardFormResidueRemainder_not_isSplitEpi
    (x : Fin S.n) (f : S.fgObj x ⟶ S.fgObj x) :
    let r := FiniteTauMatrix.algebraicallyClosedResidueMap
      (k := k) S.finiteTauCategoryData.toFiniteRightTauCategoryData x f
    ¬ IsSplitEpi (f - r • 𝟙 (S.fgObj x)) := by
  let T := S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let fT : T.obj x ⟶ T.obj x := f
  let r := FiniteTauMatrix.algebraicallyClosedResidueMap (k := k) T x fT
  have hid : FiniteTauMatrix.algebraicallyClosedResidueMap (k := k) T x
      (𝟙 (T.obj x)) = 1 := by
    letI : IsLocalRing (End (T.obj x)) := T.obj_end_local x
    letI : FiniteDimensional k (End (T.obj x)) := by
      change FiniteDimensional k (T.obj x ⟶ T.obj x)
      infer_instance
    change MagnitudeConjecture.LocalAlgebraResidue.residueScalar k
      (1 : End (T.obj x)) = 1
    simpa using
      (MagnitudeConjecture.LocalAlgebraResidue.residueScalar_algebraMap
        (k := k) (E := End (T.obj x)) 1)
  have hkerT : fT - r • 𝟙 (T.obj x) ∈
      LinearMap.ker
        (FiniteTauMatrix.algebraicallyClosedResidueMap (k := k) T x) := by
    change FiniteTauMatrix.algebraicallyClosedResidueMap (k := k) T x
        (fT - r • 𝟙 (T.obj x)) = 0
    rw [map_sub, map_smul, hid]
    simp [r]
  have hradT : IsRadicalMorphism (fT - r • 𝟙 (T.obj x)) := by
    have hmem : fT - r • 𝟙 (T.obj x) ∈
        MagnitudeConjecture.CategoryTheory.radicalSubmodule
          k (T.obj x) (T.obj x) := by
      rw [FiniteTauMatrix.radicalSubmodule_eq_ker_algebraicallyClosedResidueMap]
      exact hkerT
    exact hmem
  have hnotT := (T.isRadicalMorphism_iff_not_isSplitEpi_to_obj
    (fT - r • 𝟙 (T.obj x))).1 hradT
  change ¬ IsSplitEpi (fT - r • 𝟙 (T.obj x))
  exact hnotT

set_option backward.isDefEq.respectTransparency false in
/-- The scalar residue remainder of an indecomposable endomorphism is also
not split monic. -/
theorem standardFormResidueRemainder_not_isSplitMono
    (x : Fin S.n) (f : S.fgObj x ⟶ S.fgObj x) :
    let r := FiniteTauMatrix.algebraicallyClosedResidueMap
      (k := k) S.finiteTauCategoryData.toFiniteRightTauCategoryData x f
    ¬ IsSplitMono (f - r • 𝟙 (S.fgObj x)) := by
  let r := FiniteTauMatrix.algebraicallyClosedResidueMap
    (k := k) S.finiteTauCategoryData.toFiniteRightTauCategoryData x f
  change ¬ IsSplitMono (f - r • 𝟙 (S.fgObj x))
  intro hmono
  letI : IsSplitMono (f - r • 𝟙 (S.fgObj x)) := hmono
  haveI : IsSplitEpi (f - r • 𝟙 (S.fgObj x)) :=
    S.almostSplitSkeleton.isSplitEpi_of_isSplitMono_between_obj
      (f - r • 𝟙 (S.fgObj x))
  exact S.standardFormResidueRemainder_not_isSplitEpi x f inferInstance

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism between two differently labelled chosen indecomposables is
not split epic. -/
theorem not_isSplitEpi_fgObj_of_ne
    {x y : Fin S.n} (hxy : x ≠ y) (f : S.fgObj x ⟶ S.fgObj y) :
    ¬ IsSplitEpi f := by
  intro hf
  haveI : IsSplitEpi f := hf
  haveI : IsSplitMono f :=
    S.almostSplitSkeleton.isSplitMono_of_isSplitEpi_between_obj f
  haveI : IsIso f := isIso_of_mono_of_isSplitEpi f
  exact hxy (S.fgObj_skeletal ⟨asIso f⟩)

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism between two differently labelled chosen indecomposables is
not split monic. -/
theorem not_isSplitMono_fgObj_of_ne
    {x y : Fin S.n} (hxy : x ≠ y) (f : S.fgObj x ⟶ S.fgObj y) :
    ¬ IsSplitMono f := by
  intro hf
  haveI : IsSplitMono f := hf
  haveI : IsSplitEpi f :=
    S.almostSplitSkeleton.isSplitEpi_of_isSplitMono_between_obj f
  haveI : IsIso f := isIso_of_epi_of_isSplitMono f
  exact hxy (S.fgObj_skeletal ⟨asIso f⟩)

/-- A universal-cover vertex as an object of its raw mesh category. -/
abbrev standardFormUniversalMeshObj (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :=
  MeshCategory.obj (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀) W

/-- The skeletal realization sends the mesh object represented by `W` to
its base label. -/
@[simp]
theorem standardFormUniversalIndecMeshFunctor_obj_meshObj
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    (S.standardFormUniversalIndecMeshFunctor x₀).obj
      (S.standardFormUniversalMeshObj x₀ W) = W.1 :=
  rfl

/-- The possible degree-zero contribution in a fixed-source target fibre.
It is supported at the source vertex itself when its base label is the fixed
downstairs target, and is zero otherwise. -/
def standardFormUniversalTargetFiberDiagonal
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory) (r : k) :
    DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ S.standardFormUniversalMeshObj x₀ W ⟶ Z.1) := by
  classical
  by_cases h : X = W.1
  · let Z : LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X :=
      ⟨S.standardFormUniversalMeshObj x₀ W, by simpa using h.symm⟩
    exact LinearCovering.targetFiberLof (k := k)
      (S.standardFormUniversalIndecMeshFunctor x₀)
      (S.standardFormUniversalMeshObj x₀ W) X Z
      (r • 𝟙 (S.standardFormUniversalMeshObj x₀ W))
  · exact 0

@[simp]
theorem standardFormUniversalTargetFiberDiagonal_zero
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory) :
    S.standardFormUniversalTargetFiberDiagonal x₀ W X 0 = 0 := by
  classical
  unfold standardFormUniversalTargetFiberDiagonal
  split_ifs <;> simp

@[simp]
theorem standardFormUniversalTargetFiberDiagonal_add
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory) (r s : k) :
    S.standardFormUniversalTargetFiberDiagonal x₀ W X (r + s) =
      S.standardFormUniversalTargetFiberDiagonal x₀ W X r +
        S.standardFormUniversalTargetFiberDiagonal x₀ W X s := by
  classical
  unfold standardFormUniversalTargetFiberDiagonal
  split_ifs
  · rw [add_smul, map_add]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem standardFormUniversal_targetFiberHomMap_diagonal_self
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) (r : k) :
    LinearCovering.targetFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀)
        (S.standardFormUniversalMeshObj x₀ W) W.1
        (S.standardFormUniversalTargetFiberDiagonal x₀ W W.1 r) =
      r • 𝟙 ((S.standardFormUniversalIndecMeshFunctor x₀).obj
        (S.standardFormUniversalMeshObj x₀ W)) := by
  classical
  unfold standardFormUniversalTargetFiberDiagonal
  rw [dif_pos rfl, map_smul, map_smul,
    LinearCovering.targetFiberHomMap_lof]
  simp

/-- The possible degree-zero contribution in a fixed-target source fibre.
It is supported at the target vertex itself when its base label is the fixed
downstairs source, and is zero otherwise. -/
def standardFormUniversalSourceFiberDiagonal
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) (r : k) :
    DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ W) := by
  classical
  by_cases h : X = W.1
  · let Z : LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X :=
      ⟨S.standardFormUniversalMeshObj x₀ W, by simpa using h.symm⟩
    exact LinearCovering.sourceFiberLof (k := k)
      (S.standardFormUniversalIndecMeshFunctor x₀) X
      (S.standardFormUniversalMeshObj x₀ W) Z
      (r • 𝟙 (S.standardFormUniversalMeshObj x₀ W))
  · exact 0

@[simp]
theorem standardFormUniversalSourceFiberDiagonal_zero
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    S.standardFormUniversalSourceFiberDiagonal x₀ X W 0 = 0 := by
  classical
  unfold standardFormUniversalSourceFiberDiagonal
  split_ifs <;> simp

@[simp]
theorem standardFormUniversalSourceFiberDiagonal_add
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) (r s : k) :
    S.standardFormUniversalSourceFiberDiagonal x₀ X W (r + s) =
      S.standardFormUniversalSourceFiberDiagonal x₀ X W r +
        S.standardFormUniversalSourceFiberDiagonal x₀ X W s := by
  classical
  unfold standardFormUniversalSourceFiberDiagonal
  split_ifs
  · rw [add_smul, map_add]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem standardFormUniversal_sourceFiberHomMap_diagonal_self
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) (r : k) :
    LinearCovering.sourceFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) W.1
        (S.standardFormUniversalMeshObj x₀ W)
        (S.standardFormUniversalSourceFiberDiagonal x₀ W.1 W r) =
      r • 𝟙 ((S.standardFormUniversalIndecMeshFunctor x₀).obj
        (S.standardFormUniversalMeshObj x₀ W)) := by
  classical
  unfold standardFormUniversalSourceFiberDiagonal
  rw [dif_pos rfl, map_smul, map_smul,
    LinearCovering.sourceFiberHomMap_lof]
  simp

/-- The raw mesh-category morphism represented by one displayed arrow into
the lifted sink at `W`. -/
def standardFormUniversalMiddleHom
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    S.standardFormUniversalMeshObj x₀
        (S.standardFormUniversalMiddleVertex x₀ W i) ⟶
      S.standardFormUniversalMeshObj x₀ W :=
  (MeshCategory.quotientFunctor (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀)).map
    (LinearPathCategory.pathHom (k := k)
      (S.standardFormUniversalMiddleArrow x₀ W i).toPath)

/-- The skeletal realization of the displayed raw mesh arrow is its chosen
normalized irreducible module map. -/
@[simp]
theorem standardFormUniversalIndecMeshFunctor_map_middleHom
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    ((S.standardFormUniversalIndecMeshFunctor x₀).map
      (S.standardFormUniversalMiddleHom x₀ W i)).hom =
        S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalMiddleArrow x₀ W i) := by
  exact S.standardFormUniversalIndecMeshFunctor_map_arrow x₀
    (S.standardFormUniversalMiddleArrow x₀ W i)

/-- The displayed middle arrow with its literal underlying module-Hom type.
This wrapper keeps object-definition transports out of additive formulas. -/
def standardFormUniversalMappedMiddleHom
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i) ⟶
      S.fgObj W.1 :=
  ((S.standardFormUniversalIndecMeshFunctor x₀).map
    (S.standardFormUniversalMiddleHom x₀ W i)).hom

@[simp]
theorem standardFormUniversalMappedMiddleHom_eq_normalized
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    S.standardFormUniversalMappedMiddleHom x₀ W i =
      S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalMiddleArrow x₀ W i) :=
  S.standardFormUniversalIndecMeshFunctor_map_middleHom x₀ W i

/-- The image of an arbitrary incoming arrow is its normalized irreducible
representative.  This star-indexed form avoids transports through the chosen
finite enumeration of the middle term. -/
@[simp]
theorem standardFormUniversalIndecMeshFunctor_map_incomingArrowHom
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Star W) :
    ((S.standardFormUniversalIndecMeshFunctor x₀).map
      ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀).incomingArrowHom (k := k) d)).hom =
      S.standardFormUniversalNormalizedArrowMap x₀ d.2 := by
  exact S.standardFormUniversalIndecMeshFunctor_map_arrow x₀ d.2

/-- An arbitrary incoming arrow after realization, with its literal
underlying module-Hom type. -/
def standardFormUniversalMappedIncomingHom
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Star W) :
    S.fgObj d.1.1 ⟶ S.fgObj W.1 :=
  ((S.standardFormUniversalIndecMeshFunctor x₀).map
    ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀).incomingArrowHom (k := k) d)).hom

@[simp]
theorem standardFormUniversalMappedIncomingHom_eq_normalized
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Star W) :
    S.standardFormUniversalMappedIncomingHom x₀ W d =
      S.standardFormUniversalNormalizedArrowMap x₀ d.2 :=
  S.standardFormUniversalIndecMeshFunctor_map_incomingArrowHom x₀ W d

/-- The image of an arbitrary categorical outgoing arrow is its normalized
irreducible representative. -/
@[simp]
theorem standardFormUniversalIndecMeshFunctor_map_outgoingArrowHom
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Costar W) :
    ((S.standardFormUniversalIndecMeshFunctor x₀).map
      ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀).outgoingArrowHom (k := k) d)).hom =
      S.standardFormUniversalNormalizedArrowMap x₀ d.2 := by
  exact S.standardFormUniversalIndecMeshFunctor_map_arrow x₀ d.2

/-- An arbitrary outgoing categorical arrow after realization, with its
literal underlying module-Hom type. -/
def standardFormUniversalMappedOutgoingHom
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Costar W) :
    S.fgObj W.1 ⟶ S.fgObj d.1.1 :=
  ((S.standardFormUniversalIndecMeshFunctor x₀).map
    ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀).outgoingArrowHom (k := k) d)).hom

@[simp]
theorem standardFormUniversalMappedOutgoingHom_eq_normalized
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Costar W) :
    S.standardFormUniversalMappedOutgoingHom x₀ W d =
      S.standardFormUniversalNormalizedArrowMap x₀ d.2 :=
  S.standardFormUniversalIndecMeshFunctor_map_outgoingArrowHom x₀ W d

set_option backward.isDefEq.respectTransparency false in
/-- A dependent arrow assignment applied after transporting the target of a
reversed quiver arrow is transported by the corresponding object equality. -/
theorem standardFormUniversalArrowAssignment_cast_target
    (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    {Y W W' : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (h : W = W') (a : Y ⟶ W) :
    D (Quiver.Hom.cast rfl h a) =
      eqToHom (congrArg (S.standardFormUniversalObj x₀) h).symm ≫ D a := by
  subst W'
  simp

/-- Transport the distinguished source vertex of an outgoing costar. -/
def standardFormUniversalCostarCast
    (x₀ : Fin S.n)
    {W W' : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (h : W = W') : Quiver.Costar W ≃ Quiver.Costar W' where
  toFun d := ⟨d.1, Quiver.Hom.cast rfl h d.2⟩
  invFun d := ⟨d.1, Quiver.Hom.cast rfl h.symm d.2⟩
  left_inv d := by
    subst W'
    rfl
  right_inv d := by
    subst W'
    rfl

@[simp]
theorem standardFormUniversalCostarCast_apply
    (x₀ : Fin S.n)
    {W W' : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (h : W = W') (d : Quiver.Costar W) :
    S.standardFormUniversalCostarCast x₀ h d =
      ⟨d.1, Quiver.Hom.cast rfl h d.2⟩ := by
  subst W'
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Realization of an outgoing arrow commutes with transport of its source
vertex. -/
theorem standardFormUniversalMappedOutgoingHom_costarCast
    (x₀ : Fin S.n)
    {W W' : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (h : W = W') (d : Quiver.Costar W) :
    S.standardFormUniversalMappedOutgoingHom x₀ W'
        (S.standardFormUniversalCostarCast x₀ h d) =
      eqToHom (congrArg (S.standardFormUniversalObj x₀) h).symm ≫
        S.standardFormUniversalMappedOutgoingHom x₀ W d := by
  rw [S.standardFormUniversalMappedOutgoingHom_eq_normalized,
    S.standardFormUniversalMappedOutgoingHom_eq_normalized]
  change S.standardFormUniversalNormalizedArrowMap x₀
      (Quiver.Hom.cast rfl h d.2) =
    eqToHom (congrArg (S.standardFormUniversalObj x₀) h).symm ≫
      S.standardFormUniversalNormalizedArrowMap x₀ d.2
  exact S.standardFormUniversalArrowAssignment_cast_target x₀
    (S.standardFormUniversalNormalizedArrowMap x₀) h d.2

/-- Literal right-mesh occurrences have the official finite-tau arrow
multiplicity, including at the projective boundary. -/
theorem natCard_meshArrow_eq_arrowMultiplicity
    (target source : Fin S.n) :
    Nat.card (S.MeshArrow target source) =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData source target := by
  classical
  let B := S.meshRightAlmostSplitAt target
  rw [← S.indecomposableMultiplicity_meshRightMiddle source target]
  rw [S.indecomposableMultiplicity_eq_of_fintype_decomposition
    source B.middle B.decomposition]
  change Nat.card {i : B.index // B.label i = source} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The occurrences of one target in the chosen minimal left-almost-split
middle term are equinumerous with the reversed standard-form arrows that
represent maps from the fixed source to that target. -/
theorem natCard_minimalLeftOccurrence_eq_standardFormArrow
    (source target : Fin S.n) :
    Nat.card (S.almostSplitSkeleton.LeftAROccurrence
        (S.minimalLeftAlmostSplitAt source) target) =
      Nat.card (S.StandardFormArrow target source) := by
  let sigma := S.almostSplitSkeleton
  letI : ∀ i : Fin S.n, Module k (sigma.obj i) :=
    fun i ↦ Module.restrictScalars k Aᵐᵒᵖ (sigma.obj i)
  letI : ∀ i : Fin S.n, IsScalarTower k Aᵐᵒᵖ (sigma.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k Aᵐᵒᵖ (sigma.obj i)
  let L := S.minimalLeftAlmostSplitAt source
  let B := S.meshRightAlmostSplitAt target
  calc
    Nat.card (sigma.LeftAROccurrence L target) =
        Module.finrank k
          (sigma.irreducibleHomSpace (K := k) source target) :=
      (sigma.finrank_irreducibleHomSpace_eq_card_leftAROccurrence_of_isAlgClosed
        L target).symm
    _ = Nat.card (sigma.RightAROccurrence B source) :=
      sigma.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
        B source
    _ = FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData source target :=
      S.natCard_meshArrow_eq_arrowMultiplicity target source
    _ = Nat.card (S.StandardFormArrow target source) :=
      (S.natCard_standardFormArrow target source).symm

/-- Match the chosen left-almost-split summand occurrences at `source` with
the outgoing reversed standard-form arrows, target by target. -/
def minimalLeftOccurrenceEquivStandardFormArrow
    (source target : Fin S.n) :
    S.almostSplitSkeleton.LeftAROccurrence
        (S.minimalLeftAlmostSplitAt source) target ≃
      S.StandardFormArrow target source := by
  letI : Fintype
      (S.almostSplitSkeleton.LeftAROccurrence
        (S.minimalLeftAlmostSplitAt source) target) :=
    Fintype.ofFinite _
  apply Fintype.equivOfCardEq
  simpa only [Nat.card_eq_fintype_card] using
    S.natCard_minimalLeftOccurrence_eq_standardFormArrow source target

/-- Square-freeness of the standard-form quiver forces the chosen minimal
left-almost-split middle decomposition to contain no repeated label. -/
theorem minimalLeftAlmostSplitAt_label_injective (source : Fin S.n) :
    Function.Injective (S.minimalLeftAlmostSplitAt source).label := by
  intro t u htu
  let L := S.minimalLeftAlmostSplitAt source
  let et : S.almostSplitSkeleton.LeftAROccurrence L (L.label t) :=
    ⟨t, rfl⟩
  let eu : S.almostSplitSkeleton.LeftAROccurrence L (L.label t) :=
    ⟨u, htu.symm⟩
  let e := S.minimalLeftOccurrenceEquivStandardFormArrow
    source (L.label t)
  letI : Subsingleton (S.StandardFormArrow (L.label t) source) :=
    S.standardFormArrow_subsingleton (L.label t) source
  letI : Subsingleton
      (S.almostSplitSkeleton.LeftAROccurrence L (L.label t)) :=
    e.injective.subsingleton
  exact congrArg Subtype.val (Subsingleton.elim et eu)

/-- Regroup the indices of the chosen minimal left-almost-split middle term
by their target labels. -/
def minimalLeftMiddleIndexEquiv (source : Fin S.n) :
    (S.minimalLeftAlmostSplitAt source).index ≃
      Σ target : Fin S.n,
        S.almostSplitSkeleton.LeftAROccurrence
          (S.minimalLeftAlmostSplitAt source) target where
  toFun t :=
    ⟨(S.minimalLeftAlmostSplitAt source).label t, ⟨t, rfl⟩⟩
  invFun a := a.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨target, t, ht⟩
    subst target
    rfl

/-- The chosen left-almost-split middle indices are the categorical outgoing
costar of the corresponding base standard-form vertex. -/
def minimalLeftMiddleCostarEquiv (source : Fin S.n) :
    (S.minimalLeftAlmostSplitAt source).index ≃ Quiver.Costar source := by
  change (S.minimalLeftAlmostSplitAt source).index ≃
    Σ target : Fin S.n, S.StandardFormArrow target source
  exact (S.minimalLeftMiddleIndexEquiv source).trans
    (Equiv.sigmaCongrRight fun target ↦
      S.minimalLeftOccurrenceEquivStandardFormArrow source target)

@[simp]
theorem minimalLeftMiddleCostarEquiv_fst (source : Fin S.n)
    (t : (S.minimalLeftAlmostSplitAt source).index) :
    (S.minimalLeftMiddleCostarEquiv source t).1 =
      (S.minimalLeftAlmostSplitAt source).label t :=
  rfl

/-- Lift the left-almost-split middle indices uniquely to the outgoing
costar of a selected universal-cover vertex. -/
def standardFormUniversalLeftMiddleCostarEquiv
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    (S.minimalLeftAlmostSplitAt W.1).index ≃ Quiver.Costar W :=
  (S.minimalLeftMiddleCostarEquiv W.1).trans
    (Equiv.ofBijective
      ((MeshCategory.RightMeshData.UniversalCover.projection
        S.standardFormRightMeshData x₀).costar W)
      (MeshCategory.RightMeshData.UniversalCover.projection_costar_bijective
        S.standardFormRightMeshData x₀ W)).symm

/-- Projecting the lifted outgoing arrow attached to a left-middle index
recovers its base costar arrow. -/
theorem standardFormUniversalLeftMiddleCostarEquiv_projection
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (t : (S.minimalLeftAlmostSplitAt W.1).index) :
    (MeshCategory.RightMeshData.UniversalCover.projection
        S.standardFormRightMeshData x₀).costar W
        (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) =
      S.minimalLeftMiddleCostarEquiv W.1 t := by
  exact (Equiv.ofBijective
    ((MeshCategory.RightMeshData.UniversalCover.projection
      S.standardFormRightMeshData x₀).costar W)
    (MeshCategory.RightMeshData.UniversalCover.projection_costar_bijective
      S.standardFormRightMeshData x₀ W)).apply_symm_apply
        (S.minimalLeftMiddleCostarEquiv W.1 t)

/-- The base label of the lifted outgoing target is the label of its chosen
left-almost-split summand. -/
theorem standardFormUniversalLeftMiddleCostarEquiv_target_base
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (t : (S.minimalLeftAlmostSplitAt W.1).index) :
    (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t).1.1 =
      (S.minimalLeftAlmostSplitAt W.1).label t := by
  have h := congrArg Sigma.fst
    (S.standardFormUniversalLeftMiddleCostarEquiv_projection x₀ W t)
  change (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t).1.1 =
    (S.minimalLeftAlmostSplitAt W.1).label t at h
  exact h

/-- Reassemble all realized outgoing arrows at `W` into the chosen minimal
left-almost-split middle term at its base label. -/
def standardFormUniversalRealizedOutgoingSource
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    S.fgObj W.1 ⟶ (S.minimalLeftAlmostSplitAt W.1).middle :=
  biproduct.lift (fun t ↦
      S.standardFormUniversalMappedOutgoingHom x₀ W
          (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
        eqToHom (congrArg S.fgObj
          (S.standardFormUniversalLeftMiddleCostarEquiv_target_base x₀ W t))) ≫
    (S.minimalLeftAlmostSplitAt W.1).decomposition.inv

@[reassoc (attr := simp)]
theorem standardFormUniversalRealizedOutgoingSource_decomposition_π
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (t : (S.minimalLeftAlmostSplitAt W.1).index) :
    S.standardFormUniversalRealizedOutgoingSource x₀ W ≫
        (S.minimalLeftAlmostSplitAt W.1).decomposition.hom ≫
        biproduct.π
          (fun j ↦ S.fgObj
            ((S.minimalLeftAlmostSplitAt W.1).label j)) t =
      S.standardFormUniversalMappedOutgoingHom x₀ W
          (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
        eqToHom (congrArg S.fgObj
          (S.standardFormUniversalLeftMiddleCostarEquiv_target_base x₀ W t)) := by
  change
    (biproduct.lift (fun t ↦
        S.standardFormUniversalMappedOutgoingHom x₀ W
            (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
          eqToHom (congrArg S.fgObj
            (S.standardFormUniversalLeftMiddleCostarEquiv_target_base x₀ W t))) ≫
      (S.minimalLeftAlmostSplitAt W.1).decomposition.inv) ≫
        (S.minimalLeftAlmostSplitAt W.1).decomposition.hom ≫
        biproduct.π
          (fun j ↦ S.fgObj
            ((S.minimalLeftAlmostSplitAt W.1).label j)) t = _
  erw [Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_π]

/-- Every chosen-summand component of the reassembled outgoing source is
irreducible. -/
theorem standardFormUniversalRealizedOutgoingSource_component_isIrreducible
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (t : (S.minimalLeftAlmostSplitAt W.1).index) :
    IsIrreducibleMorphism
      (S.standardFormUniversalRealizedOutgoingSource x₀ W ≫
        (S.minimalLeftAlmostSplitAt W.1).decomposition.hom ≫
        biproduct.π
          (fun j ↦ S.fgObj
            ((S.minimalLeftAlmostSplitAt W.1).label j)) t) := by
  rw [S.standardFormUniversalRealizedOutgoingSource_decomposition_π]
  apply isIrreducibleMorphism_comp_eqToHom
  rw [S.standardFormUniversalMappedOutgoingHom_eq_normalized]
  exact S.standardFormUniversalNormalizedArrowMap_isIrreducible x₀
    (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t).2

set_option backward.isDefEq.respectTransparency false in
/-- The source assembled from every outgoing universal-cover arrow differs
from the chosen minimal left-almost-split map by an automorphism of its
middle term.  This includes injective source vertices. -/
theorem exists_minimalLeftAlmostSplitAt_iso_realizedOutgoingSource
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    ∃ e : (S.minimalLeftAlmostSplitAt W.1).middle ≅
        (S.minimalLeftAlmostSplitAt W.1).middle,
      (S.minimalLeftAlmostSplitAt W.1).map ≫ e.hom =
        S.standardFormUniversalRealizedOutgoingSource x₀ W := by
  classical
  let L := S.minimalLeftAlmostSplitAt W.1
  let E := L.middle
  let F : L.index → FGModuleCat Aᵐᵒᵖ :=
    fun t ↦ S.almostSplitSkeleton.obj (L.label t)
  let eMiddle : E ≅ ⨁ F := L.decomposition
  let i : S.fgObj W.1 ⟶ E := L.map
  let q : S.fgObj W.1 ⟶ E :=
    S.standardFormUniversalRealizedOutgoingSource x₀ W
  let component (t : L.index) : S.fgObj W.1 ⟶ F t :=
    q ≫ eMiddle.hom ≫ biproduct.π F t
  have hcomponent (t : L.index) :
      IsIrreducibleMorphism (component t) := by
    exact S.standardFormUniversalRealizedOutgoingSource_component_isIrreducible
      x₀ W t
  have hiAS : IsLeftAlmostSplit i := L.leftAlmostSplit
  let factor (t : L.index) : E ⟶ F t :=
    Classical.choose (hiAS.factors (component t)
      (hcomponent t).not_isSplitMono)
  have factor_spec (t : L.index) : i ≫ factor t = component t :=
    Classical.choose_spec (hiAS.factors (component t)
      (hcomponent t).not_isSplitMono)
  have factor_splitEpi (t : L.index) : IsSplitEpi (factor t) := by
    rcases (hcomponent t).factorization i (factor t) (factor_spec t) with
      hiSplit | htSplit
    · exact (hiAS.not_isSplitMono hiSplit).elim
    · exact htSplit
  let h : E ⟶ E := biproduct.lift factor ≫ eMiddle.inv
  have hih : i ≫ h = q := by
    apply (cancel_mono eMiddle.hom).1
    apply biproduct.hom_ext
    intro t
    change i ≫ h ≫ eMiddle.hom ≫ biproduct.π F t =
      q ≫ eMiddle.hom ≫ biproduct.π F t
    simp only [h, Category.assoc, Iso.inv_hom_id_assoc,
      biproduct.lift_π]
    exact factor_spec t
  have hlabel : Function.Injective L.label :=
    S.minimalLeftAlmostSplitAt_label_injective W.1
  let inc (t : L.index) : F t ⟶ E :=
    biproduct.ι F t ≫ eMiddle.inv
  have hdiag (t : L.index) : IsIso (inc t ≫ factor t) := by
    have hdiagSplit : IsSplitEpi (inc t ≫ factor t) := by
      by_contra hnot
      have hcomponentNot (j : L.index) :
          ¬ IsSplitEpi (inc j ≫ factor t) := by
        by_cases hjt : j = t
        · subst j
          exact hnot
        · intro hsplit
          letI : IsSplitEpi (inc j ≫ factor t) := hsplit
          haveI : IsSplitMono (inc j ≫ factor t) :=
            S.almostSplitSkeleton.isSplitMono_of_isSplitEpi_between_obj
              (inc j ≫ factor t)
          haveI : IsIso (inc j ≫ factor t) :=
            isIso_of_mono_of_isSplitEpi (inc j ≫ factor t)
          apply hjt
          apply hlabel
          exact S.almostSplitSkeleton.eq_of_iso
            ⟨asIso (inc j ≫ factor t)⟩
      have hdesc : biproduct.desc (fun j ↦ inc j ≫ factor t) =
          eMiddle.inv ≫ factor t := by
        apply biproduct.hom_ext'
        intro j
        simp only [biproduct.ι_desc]
        rfl
      have hnonsplit :=
        S.almostSplitSkeleton.biproductDesc_not_isSplitEpi F
          (fun j ↦ inc j ≫ factor t) hcomponentNot
      apply hnonsplit
      rw [hdesc]
      letI : IsSplitEpi (factor t) := factor_splitEpi t
      infer_instance
    letI : IsSplitEpi (inc t ≫ factor t) := hdiagSplit
    haveI : IsSplitMono (inc t ≫ factor t) :=
      S.almostSplitSkeleton.isSplitMono_of_isSplitEpi_between_obj
        (inc t ≫ factor t)
    exact isIso_of_mono_of_isSplitEpi (inc t ≫ factor t)
  let hSum : (⨁ F) ⟶ ⨁ F := eMiddle.inv ≫ h ≫ eMiddle.hom
  have hpair (a b : L.index) (hab : a ≠ b) :
      ¬ Nonempty (F a ≅ F b) := by
    intro e
    apply hab
    apply hlabel
    exact S.almostSplitSkeleton.eq_of_iso e
  have hsumDiag (t : L.index) : IsIso
      (biproduct.ι F t ≫ hSum ≫ biproduct.π F t) := by
    simpa only [hSum, h, inc, eMiddle, F, Category.assoc,
      Iso.inv_hom_id_assoc, biproduct.lift_π] using hdiag t
  haveI : IsIso hSum :=
    MagnitudeConjecture.CategoryTheory.isIso_of_finBiproduct_diagonal_isIso
      F (fun t ↦ S.fgObj_indecomposable (L.label t))
      (fun t ↦ S.fgObj_end_isLocalRing (L.label t)) hpair hSum hsumDiag
  have heq : h = eMiddle.hom ≫ hSum ≫ eMiddle.inv := by
    simp [hSum, Category.assoc]
  haveI : IsIso h := by
    rw [heq]
    infer_instance
  exact ⟨asIso h, hih⟩

/-- The comparison automorphism between the chosen left-almost-split source
and the outgoing source assembled from the normalized realization. -/
def standardFormUniversalRealizedOutgoingSourceIso
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    (S.minimalLeftAlmostSplitAt W.1).middle ≅
      (S.minimalLeftAlmostSplitAt W.1).middle :=
  Classical.choose
    (S.exists_minimalLeftAlmostSplitAt_iso_realizedOutgoingSource x₀ W)

/-- The chosen left-almost-split map followed by the comparison
automorphism is the reassembled outgoing source. -/
theorem minimalLeftAlmostSplitAt_comp_realizedOutgoingSourceIso
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    (S.minimalLeftAlmostSplitAt W.1).map ≫
        (S.standardFormUniversalRealizedOutgoingSourceIso x₀ W).hom =
      S.standardFormUniversalRealizedOutgoingSource x₀ W :=
  Classical.choose_spec
    (S.exists_minimalLeftAlmostSplitAt_iso_realizedOutgoingSource x₀ W)

/-- The outgoing source assembled from the normalized universal realization
is left almost split at every vertex, including injective vertices. -/
theorem standardFormUniversalRealizedOutgoingSource_isLeftAlmostSplit
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    IsLeftAlmostSplit
      (S.standardFormUniversalRealizedOutgoingSource x₀ W) := by
  rw [← S.minimalLeftAlmostSplitAt_comp_realizedOutgoingSourceIso x₀ W]
  exact leftAlmostSplit_postcomp_iso
    (S.minimalLeftAlmostSplitAt W.1).leftAlmostSplit
    (S.standardFormUniversalRealizedOutgoingSourceIso x₀ W)

/-- The outgoing source assembled from the normalized universal realization
is left minimal at every vertex. -/
theorem standardFormUniversalRealizedOutgoingSource_isLeftMinimal
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    IsLeftMinimal
      (S.standardFormUniversalRealizedOutgoingSource x₀ W) := by
  rw [← S.minimalLeftAlmostSplitAt_comp_realizedOutgoingSourceIso x₀ W]
  exact leftMinimal_postcomp_iso
    (S.minimalLeftAlmostSplitAt W.1).leftMinimal
    (S.standardFormUniversalRealizedOutgoingSourceIso x₀ W)

/-- At a noninjective lifted vertex, the source assembled from all outgoing
normalized arrows is monic.  Under the comparison automorphism it is the
chosen left almost-split monomorphism at the underlying indecomposable. -/
theorem standardFormUniversalRealizedOutgoingSource_mono_of_not_injective
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1)) :
    Mono (S.standardFormUniversalRealizedOutgoingSource x₀ W) := by
  rw [← S.minimalLeftAlmostSplitAt_comp_realizedOutgoingSourceIso x₀ W]
  exact mono_comp'
    (S.noninjectiveLeftAlmostSplit_mono ⟨W.1, hW⟩) (by infer_instance)

/-- At a noninjective lifted vertex, the normalized outgoing arrows jointly
detect morphisms into that vertex. -/
theorem eq_zero_of_comp_standardFormUniversalMappedOutgoingHom_of_not_injective
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1))
    (q : S.fgObj X ⟶ S.fgObj W.1)
    (hq : ∀ d : Quiver.Costar W,
      q ≫ S.standardFormUniversalMappedOutgoingHom x₀ W d = 0) :
    q = 0 := by
  let source := S.standardFormUniversalRealizedOutgoingSource x₀ W
  letI : Mono source :=
    S.standardFormUniversalRealizedOutgoingSource_mono_of_not_injective
      x₀ W hW
  apply (cancel_mono source).1
  rw [zero_comp]
  apply (cancel_mono (S.minimalLeftAlmostSplitAt W.1).decomposition.hom).1
  rw [zero_comp]
  apply biproduct.hom_ext
  intro t
  rw [zero_comp]
  calc
    (q ≫ source) ≫ (S.minimalLeftAlmostSplitAt W.1).decomposition.hom ≫
          biproduct.π
            (fun j ↦ S.fgObj
              ((S.minimalLeftAlmostSplitAt W.1).label j)) t =
        q ≫ (source ≫
          (S.minimalLeftAlmostSplitAt W.1).decomposition.hom ≫
            biproduct.π
              (fun j ↦ S.fgObj
                ((S.minimalLeftAlmostSplitAt W.1).label j)) t) := by
          simp only [Category.assoc]
    _ = q ≫
        (S.standardFormUniversalMappedOutgoingHom x₀ W
            (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
          eqToHom (congrArg S.fgObj
            (S.standardFormUniversalLeftMiddleCostarEquiv_target_base
              x₀ W t))) := by
          rw [show source =
            S.standardFormUniversalRealizedOutgoingSource x₀ W from rfl,
            S.standardFormUniversalRealizedOutgoingSource_decomposition_π]
    _ = 0 := by rw [← Category.assoc, hq, zero_comp]

/-- Expanding the chosen left-middle biproduct writes a factor through the
reassembled outgoing source as the sum of its lifted-arrow components. -/
theorem standardFormUniversal_factor_realizedOutgoingSource_eq_sum
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : Fin S.n)
    (h : (S.minimalLeftAlmostSplitAt W.1).middle ⟶ S.fgObj X) :
    S.standardFormUniversalRealizedOutgoingSource x₀ W ≫ h =
      ∑ t : (S.minimalLeftAlmostSplitAt W.1).index,
        S.standardFormUniversalMappedOutgoingHom x₀ W
            (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
          eqToHom (congrArg S.fgObj
            (S.standardFormUniversalLeftMiddleCostarEquiv_target_base
              x₀ W t)) ≫
          biproduct.ι
              (fun j ↦ S.fgObj
                ((S.minimalLeftAlmostSplitAt W.1).label j)) t ≫
          (S.minimalLeftAlmostSplitAt W.1).decomposition.inv ≫ h := by
  classical
  let L := S.minimalLeftAlmostSplitAt W.1
  let F : L.index → FGModuleCat Aᵐᵒᵖ :=
    fun t ↦ S.fgObj (L.label t)
  let c : ∀ t : L.index, S.fgObj W.1 ⟶ F t := fun t ↦
    S.standardFormUniversalMappedOutgoingHom x₀ W
        (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
      eqToHom (congrArg S.fgObj
        (S.standardFormUniversalLeftMiddleCostarEquiv_target_base x₀ W t))
  let d : ∀ t : L.index, F t ⟶ S.fgObj X := fun t ↦
    biproduct.ι F t ≫ L.decomposition.inv ≫ h
  change (biproduct.lift c ≫ L.decomposition.inv) ≫ h =
    ∑ t, c t ≫ d t
  calc
    (biproduct.lift c ≫ L.decomposition.inv) ≫ h =
        biproduct.lift c ≫ (L.decomposition.inv ≫ h) :=
      Category.assoc _ _ _
    _ = biproduct.lift c ≫ biproduct.desc d := by
      congr 1
      symm
      apply biproduct.hom_ext'
      intro t
      simp [d, Category.assoc]
    _ = ∑ t, c t ≫ d t := biproduct.lift_desc

set_option backward.isDefEq.respectTransparency false in
/-- Remove the scalar residue of an endomorphism and factor the radical
remainder through all normalized outgoing arrows. -/
theorem standardFormUniversal_endomorphism_eq_scalar_add_outgoing_sum
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (f : S.fgObj W.1 ⟶ S.fgObj W.1) :
    ∃ (r : k)
      (g : ∀ t : (S.minimalLeftAlmostSplitAt W.1).index,
        S.fgObj
            (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t).1.1 ⟶
          S.fgObj W.1),
      f = r • 𝟙 (S.fgObj W.1) +
        ∑ t, S.standardFormUniversalMappedOutgoingHom x₀ W
            (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
          g t := by
  let r := FiniteTauMatrix.algebraicallyClosedResidueMap
    (k := k) S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 f
  have hnot : ¬ IsSplitMono (f - r • 𝟙 (S.fgObj W.1)) :=
    S.standardFormResidueRemainder_not_isSplitMono W.1 f
  obtain ⟨h, hh⟩ :=
    (S.standardFormUniversalRealizedOutgoingSource_isLeftAlmostSplit x₀ W)
      |>.factors (f - r • 𝟙 (S.fgObj W.1)) hnot
  let g : ∀ t : (S.minimalLeftAlmostSplitAt W.1).index,
      S.fgObj
          (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t).1.1 ⟶
        S.fgObj W.1 := fun t ↦
    eqToHom (congrArg S.fgObj
        (S.standardFormUniversalLeftMiddleCostarEquiv_target_base x₀ W t)) ≫
      biproduct.ι
          (fun j ↦ S.fgObj
            ((S.minimalLeftAlmostSplitAt W.1).label j)) t ≫
      (S.minimalLeftAlmostSplitAt W.1).decomposition.inv ≫ h
  refine ⟨r, g, ?_⟩
  rw [← S.standardFormUniversal_factor_realizedOutgoingSource_eq_sum
    x₀ W W.1 h, hh]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- A morphism to a differently labelled indecomposable factors through all
normalized outgoing arrows at its source. -/
theorem standardFormUniversal_morphism_eq_outgoing_sum_of_ne
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    {X : Fin S.n} (hWX : W.1 ≠ X)
    (f : S.fgObj W.1 ⟶ S.fgObj X) :
    ∃ g : ∀ t : (S.minimalLeftAlmostSplitAt W.1).index,
        S.fgObj
            (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t).1.1 ⟶
          S.fgObj X,
      f = ∑ t, S.standardFormUniversalMappedOutgoingHom x₀ W
            (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
          g t := by
  have hnot : ¬ IsSplitMono f := S.not_isSplitMono_fgObj_of_ne hWX f
  obtain ⟨h, hh⟩ :=
    (S.standardFormUniversalRealizedOutgoingSource_isLeftAlmostSplit x₀ W)
      |>.factors f hnot
  let g : ∀ t : (S.minimalLeftAlmostSplitAt W.1).index,
      S.fgObj
          (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t).1.1 ⟶
        S.fgObj X := fun t ↦
    eqToHom (congrArg S.fgObj
        (S.standardFormUniversalLeftMiddleCostarEquiv_target_base x₀ W t)) ≫
      biproduct.ι
          (fun j ↦ S.fgObj
            ((S.minimalLeftAlmostSplitAt W.1).label j)) t ≫
      (S.minimalLeftAlmostSplitAt W.1).decomposition.inv ≫ h
  refine ⟨g, ?_⟩
  rw [← S.standardFormUniversal_factor_realizedOutgoingSource_eq_sum
    x₀ W X h]
  exact hh.symm

set_option backward.isDefEq.respectTransparency false in
/-- The fixed-source Riedtmann one-step decomposition, with the scalar
identity term already bundled as a target-fibre contribution. -/
theorem standardFormUniversal_oneStep_targetFiber
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory)
    (f : S.fgObj W.1 ⟶ S.fgObj X) :
    ∃ (a : DirectSum
        (LinearCovering.Fiber
          (S.standardFormUniversalIndecMeshFunctor x₀) X)
        (fun Z ↦ S.standardFormUniversalMeshObj x₀ W ⟶ Z.1))
      (g : ∀ t : (S.minimalLeftAlmostSplitAt W.1).index,
        S.fgObj
            (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t).1.1 ⟶
          S.fgObj X),
      (InducedCategory.homMk f :
          (S.standardFormUniversalIndecMeshFunctor x₀).obj
              (S.standardFormUniversalMeshObj x₀ W) ⟶ X) =
        LinearCovering.targetFiberHomMap (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀)
          (S.standardFormUniversalMeshObj x₀ W) X a +
        (InducedCategory.homMk
          (∑ t, S.standardFormUniversalMappedOutgoingHom x₀ W
              (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
            g t) :
          (S.standardFormUniversalIndecMeshFunctor x₀).obj
              (S.standardFormUniversalMeshObj x₀ W) ⟶ X) := by
  classical
  by_cases hWX : W.1 = X
  · subst X
    obtain ⟨r, g, hfg⟩ :=
      S.standardFormUniversal_endomorphism_eq_scalar_add_outgoing_sum x₀ W f
    let a := S.standardFormUniversalTargetFiberDiagonal x₀ W W.1 r
    refine ⟨a, g, ?_⟩
    have ha :
        LinearCovering.targetFiberHomMap (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀)
          (S.standardFormUniversalMeshObj x₀ W) W.1 a =
            r • 𝟙 ((S.standardFormUniversalIndecMeshFunctor x₀).obj
              (S.standardFormUniversalMeshObj x₀ W)) := by
      exact S.standardFormUniversal_targetFiberHomMap_diagonal_self x₀ W r
    rw [ha]
    apply InducedCategory.hom_ext
    exact hfg
  · obtain ⟨g, hfg⟩ :=
      S.standardFormUniversal_morphism_eq_outgoing_sum_of_ne x₀ W hWX f
    refine ⟨0, g, ?_⟩
    rw [map_zero, zero_add]
    apply InducedCategory.hom_ext
    exact hfg

/-- Every outgoing arrow of the normalized universal realization belongs to
the categorical radical ideal. -/
theorem standardFormUniversalNormalizedOutgoingArrow_mem_radical
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Costar W) :
    S.standardFormUniversalMappedOutgoingHom x₀ W d ∈
      S.fgNilpotentRadicalData.ideal.hom
        (S.fgObj W.1) (S.fgObj d.1.1) := by
  apply (S.fgNilpotentRadicalData.mem_ideal_iff _).2
  apply (S.finiteTauCategoryData.isRadicalMorphism_iff_not_isSplitMono_from_obj
    _).2
  rw [S.standardFormUniversalMappedOutgoingHom_eq_normalized]
  exact (S.standardFormUniversalNormalizedArrowMap_isIrreducible x₀ d.2)
    |>.not_isSplitMono

set_option backward.isDefEq.respectTransparency false in
/-- Riedtmann's fixed-source approximation: modulo the `n`-th radical
power, every module morphism is the image of a finite target-fibre sum of
raw mesh morphisms. -/
theorem standardFormUniversal_exists_targetFiber_mod_radicalPower
    (x₀ : Fin S.n)
    (X : S.FGIndecCategory) :
    ∀ (n : ℕ)
      (W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀)
      (f : S.fgObj W.1 ⟶ S.fgObj X),
      ∃ a : DirectSum
          (LinearCovering.Fiber
            (S.standardFormUniversalIndecMeshFunctor x₀) X)
          (fun Z ↦ S.standardFormUniversalMeshObj x₀ W ⟶ Z.1),
        ((InducedCategory.homMk f :
              (S.standardFormUniversalIndecMeshFunctor x₀).obj
                  (S.standardFormUniversalMeshObj x₀ W) ⟶ X) -
            LinearCovering.targetFiberHomMap (k := k)
              (S.standardFormUniversalIndecMeshFunctor x₀)
              (S.standardFormUniversalMeshObj x₀ W) X a).hom ∈
          (S.fgNilpotentRadicalData.ideal.pow n).hom
            (S.fgObj W.1) (S.fgObj X) := by
  classical
  intro n
  induction n with
  | zero =>
      intro W f
      refine ⟨0, ?_⟩
      rw [map_zero]
      change _ ∈ (⊤ : CategoricalIdeal.HomIdeal
        (RightModule.FinitelyGeneratedCategory A)).hom
          (S.fgObj W.1) (S.fgObj X)
      simp
  | succ n ih =>
      intro W f
      obtain ⟨a₀, g, hfg⟩ :=
        S.standardFormUniversal_oneStep_targetFiber x₀ W X f
      choose a ha using fun t ↦ ih
        (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t).1 (g t)
      let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀
      let d : (S.minimalLeftAlmostSplitAt W.1).index → Quiver.Costar W :=
        fun t ↦ S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t
      let b := fun t ↦ LinearCovering.targetFiberPrecomp (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X
        (T.outgoingArrowHom (k := k) (d t)) (a t)
      let total := a₀ + ∑ t, b t
      refine ⟨total, ?_⟩
      have hmap :
          LinearCovering.targetFiberHomMap (k := k)
              (S.standardFormUniversalIndecMeshFunctor x₀)
              (S.standardFormUniversalMeshObj x₀ W) X total =
            LinearCovering.targetFiberHomMap (k := k)
                (S.standardFormUniversalIndecMeshFunctor x₀)
                (S.standardFormUniversalMeshObj x₀ W) X a₀ +
              ∑ t,
                (S.standardFormUniversalIndecMeshFunctor x₀).map
                    (T.outgoingArrowHom (k := k) (d t)) ≫
                  LinearCovering.targetFiberHomMap (k := k)
                    (S.standardFormUniversalIndecMeshFunctor x₀)
                    (S.standardFormUniversalMeshObj x₀ (d t).1) X (a t) := by
        dsimp only [total, b]
        rw [map_add, map_sum]
        apply congrArg₂ (.+.) rfl
        apply Finset.sum_congr rfl
        intro t _
        exact LinearCovering.targetFiberHomMap_targetFiberPrecomp
          (k := k) (S.standardFormUniversalIndecMeshFunctor x₀) X
          (T.outgoingArrowHom (k := k) (d t)) (a t)
      have hsum :
          (InducedCategory.homMk
            (∑ t, S.standardFormUniversalMappedOutgoingHom x₀ W (d t) ≫
              g t) :
              (S.standardFormUniversalIndecMeshFunctor x₀).obj
                  (S.standardFormUniversalMeshObj x₀ W) ⟶ X) =
            ∑ t,
              (S.standardFormUniversalIndecMeshFunctor x₀).map
                  (T.outgoingArrowHom (k := k) (d t)) ≫
                (InducedCategory.homMk (g t) :
                  (S.standardFormUniversalIndecMeshFunctor x₀).obj
                      (S.standardFormUniversalMeshObj x₀ (d t).1) ⟶ X) := by
        apply (InducedCategory.homLinearEquiv (R := k)).injective
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro t _
        rfl
      have herr :
          (InducedCategory.homMk f :
              (S.standardFormUniversalIndecMeshFunctor x₀).obj
                  (S.standardFormUniversalMeshObj x₀ W) ⟶ X) -
              LinearCovering.targetFiberHomMap (k := k)
                (S.standardFormUniversalIndecMeshFunctor x₀)
                (S.standardFormUniversalMeshObj x₀ W) X total =
            ∑ t,
              (S.standardFormUniversalIndecMeshFunctor x₀).map
                  (T.outgoingArrowHom (k := k) (d t)) ≫
                ((InducedCategory.homMk (g t) :
                    (S.standardFormUniversalIndecMeshFunctor x₀).obj
                        (S.standardFormUniversalMeshObj x₀ (d t).1) ⟶ X) -
                  LinearCovering.targetFiberHomMap (k := k)
                    (S.standardFormUniversalIndecMeshFunctor x₀)
                    (S.standardFormUniversalMeshObj x₀ (d t).1) X
                    (a t)) := by
        rw [hfg, hsum, hmap]
        simp_rw [Preadditive.comp_sub]
        rw [Finset.sum_sub_distrib]
        abel
      rw [herr]
      rw [← InducedCategory.homLinearEquiv_apply (R := k), map_sum]
      rw [CategoricalIdeal.HomIdeal.pow_succ_eq_mul_pow]
      apply ((S.fgNilpotentRadicalData.ideal ⋆ᵢ
        S.fgNilpotentRadicalData.ideal.pow n).hom
          (S.fgObj W.1) (S.fgObj X)).sum_mem
      intro t _
      rw [InducedCategory.homLinearEquiv_apply,
        InducedCategory.comp_hom]
      exact CategoricalIdeal.HomIdeal.comp_mem_mul
        (S.standardFormUniversalNormalizedOutgoingArrow_mem_radical x₀ W
          (d t)) (ha t)

set_option backward.isDefEq.respectTransparency false in
/-- Nilpotence terminates the fixed-source radical approximation, giving
exact surjectivity of the target-fibre map at every represented source. -/
theorem standardFormUniversal_targetFiberHomMap_surjective_meshObj
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory) :
    Function.Surjective
      (LinearCovering.targetFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀)
        (S.standardFormUniversalMeshObj x₀ W) X) := by
  intro f
  obtain ⟨N, hN⟩ := S.fgNilpotentRadicalData.nilpotent
  obtain ⟨a, ha⟩ :=
    S.standardFormUniversal_exists_targetFiber_mod_radicalPower
      x₀ X N W f.hom
  rw [hN] at ha
  have hzero :
      (InducedCategory.homMk f.hom :
          (S.standardFormUniversalIndecMeshFunctor x₀).obj
              (S.standardFormUniversalMeshObj x₀ W) ⟶ X) -
        LinearCovering.targetFiberHomMap (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀)
          (S.standardFormUniversalMeshObj x₀ W) X a = 0 := by
    apply InducedCategory.hom_ext
    exact ha
  refine ⟨a, ?_⟩
  have heq := sub_eq_zero.mp hzero
  exact heq.symm.trans (InducedCategory.hom_ext rfl).symm

/-- Every fixed-source target-fibre family is a possible scalar at the
source vertex plus families precomposed with the arrows leaving that vertex.
This is the direct-sum form of decomposition by the first arrow. -/
theorem standardFormUniversal_exists_targetFiber_eq_diagonal_add_outgoing
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ S.standardFormUniversalMeshObj x₀ W ⟶ Z.1)) :
    ∃ (r : k)
      (b : ∀ d : Quiver.Costar W,
        DirectSum
          (LinearCovering.Fiber
            (S.standardFormUniversalIndecMeshFunctor x₀) X)
          (fun Z ↦ S.standardFormUniversalMeshObj x₀ d.1 ⟶ Z.1)),
      a = S.standardFormUniversalTargetFiberDiagonal x₀ W X r +
        ∑ d : Quiver.Costar W,
          LinearCovering.targetFiberPrecomp (k := k)
            (S.standardFormUniversalIndecMeshFunctor x₀) X
            ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
              S.standardFormRightMeshData x₀).outgoingArrowHom (k := k) d)
            (b d) := by
  classical
  let F := S.standardFormUniversalIndecMeshFunctor x₀
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  induction a using DirectSum.induction_on with
  | zero =>
      refine ⟨0, fun _ ↦ 0, ?_⟩
      simp
  | add a₁ a₂ h₁ h₂ =>
      obtain ⟨r₁, b₁, hb₁⟩ := h₁
      obtain ⟨r₂, b₂, hb₂⟩ := h₂
      refine ⟨r₁ + r₂, fun d ↦ b₁ d + b₂ d, ?_⟩
      rw [hb₁, hb₂, S.standardFormUniversalTargetFiberDiagonal_add]
      simp_rw [map_add]
      rw [Finset.sum_add_distrib]
      abel
  | of Z f =>
      rw [← DirectSum.lof_eq_of k
        (LinearCovering.Fiber F X)
        (fun V ↦ S.standardFormUniversalMeshObj x₀ W ⟶ V.1) Z f]
      obtain ⟨r, c, hf⟩ :=
        T.exists_eq_targetRawDiagonalScalar_add_rawOutgoingSum f
      let b : ∀ d : Quiver.Costar W,
          DirectSum
            (LinearCovering.Fiber F X)
            (fun V ↦ S.standardFormUniversalMeshObj x₀ d.1 ⟶ V.1) :=
        fun d ↦ LinearCovering.targetFiberLof (k := k) F
          (S.standardFormUniversalMeshObj x₀ d.1) X Z (c d)
      by_cases hWZ : S.standardFormUniversalMeshObj x₀ W = Z.1
      · have hXW : X = W.1 := by
          have h := Z.2
          rw [← hWZ] at h
          exact h.symm
        have hdiag :
            (DirectSum.lof k
                (LinearCovering.Fiber F X)
                (fun V ↦ S.standardFormUniversalMeshObj x₀ W ⟶ V.1) Z)
                (T.targetRawDiagonalScalar W Z.1 r) =
              S.standardFormUniversalTargetFiberDiagonal x₀ W X r := by
          unfold MeshCategory.RightMeshData.targetRawDiagonalScalar
          rw [dif_pos hWZ]
          unfold standardFormUniversalTargetFiberDiagonal
          rw [dif_pos hXW]
          subst X
          have hZ : Z =
              (⟨S.standardFormUniversalMeshObj x₀ W, rfl⟩ :
                LinearCovering.Fiber F W.1) := Subtype.ext hWZ.symm
          subst Z
          unfold LinearCovering.targetFiberLof
          rfl
        refine ⟨r, b, ?_⟩
        rw [hf, map_add, hdiag]
        apply congrArg₂ (.+.) rfl
        rw [MeshCategory.RightMeshData.rawOutgoingSum, map_sum]
        apply Finset.sum_congr rfl
        intro d _
        exact (LinearCovering.targetFiberPrecomp_lof (k := k) F X
          (T.outgoingArrowHom (k := k) d) Z (c d)).symm
      · have hdiag : T.targetRawDiagonalScalar W Z.1 r = 0 := by
          unfold MeshCategory.RightMeshData.targetRawDiagonalScalar
          rw [dif_neg hWZ]
        refine ⟨0, b, ?_⟩
        rw [hf, hdiag, zero_add,
          MeshCategory.RightMeshData.rawOutgoingSum, map_sum,
          S.standardFormUniversalTargetFiberDiagonal_zero, zero_add]
        apply Finset.sum_congr rfl
        intro d _
        exact (LinearCovering.targetFiberPrecomp_lof (k := k) F X
          (T.outgoingArrowHom (k := k) d) Z (c d)).symm

/-- The downstairs nonprojective endpoint whose translate is a selected
noninjective standard-form label. -/
def standardFormUniversalNoninjectiveMeshBase
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1)) :
    {z : Fin S.n // z ∉ S.standardFormRightMeshData.projective} :=
  ⟨((S.rightTranslationEquiv).symm ⟨W.1, hW⟩).1,
    ((S.rightTranslationEquiv).symm ⟨W.1, hW⟩).2⟩

/-- The recovered downstairs mesh endpoint translates to the base label of
the selected noninjective lifted vertex. -/
theorem standardFormUniversalNoninjectiveMeshBase_tau
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1)) :
    S.standardFormRightMeshData.tau
        (S.standardFormUniversalNoninjectiveMeshBase x₀ W hW) = W.1 := by
  exact congrArg Subtype.val
    (S.rightTranslationEquiv.apply_symm_apply ⟨W.1, hW⟩)

/-- Reverse the formal mesh edge at a noninjective lifted vertex.  The
result is the unique lifted nonprojective mesh endpoint whose translate is
the original vertex. -/
def standardFormUniversalNoninjectiveMeshEndpoint
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1)) :
    {Z : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      Z ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀} := by
  let z := S.standardFormUniversalNoninjectiveMeshBase x₀ W hW
  let hbase := S.standardFormUniversalNoninjectiveMeshBase_tau x₀ W hW
  let e : @Quiver.Hom
      (Quiver.Symmetrify
        (MeshCategory.RightMeshData.UniversalCover.AugmentedVertex
          S.standardFormRightMeshData))
      (Quiver.symmetrifyQuiver
        (MeshCategory.RightMeshData.UniversalCover.AugmentedVertex
          S.standardFormRightMeshData)) z.1 W.1 :=
    Quiver.Hom.cast rfl hbase
      (MeshCategory.RightMeshData.UniversalCover.meshArrow
        S.standardFormRightMeshData z)
  let Z := MeshCategory.RightMeshData.UniversalCover.extend
    S.standardFormRightMeshData x₀ W (Quiver.reverse e)
  exact ⟨Z, by
    change z.1 ∉ S.standardFormRightMeshData.projective
    exact z.2⟩

/-- Translating the endpoint obtained by reversing the formal mesh edge
recovers the original noninjective lifted vertex. -/
theorem standardFormUniversalNoninjectiveMeshEndpoint_tau
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1)) :
    MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀
      (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW) = W := by
  let z := S.standardFormUniversalNoninjectiveMeshBase x₀ W hW
  let hbase := S.standardFormUniversalNoninjectiveMeshBase_tau x₀ W hW
  let e : @Quiver.Hom
      (Quiver.Symmetrify
        (MeshCategory.RightMeshData.UniversalCover.AugmentedVertex
          S.standardFormRightMeshData))
      (Quiver.symmetrifyQuiver
        (MeshCategory.RightMeshData.UniversalCover.AugmentedVertex
          S.standardFormRightMeshData)) z.1 W.1 :=
    Quiver.Hom.cast rfl hbase
      (MeshCategory.RightMeshData.UniversalCover.meshArrow
        S.standardFormRightMeshData z)
  have hext := MeshCategory.RightMeshData.UniversalCover.extend_reverse_left
    S.standardFormRightMeshData x₀ W e
  change MeshCategory.RightMeshData.UniversalCover.extend
      S.standardFormRightMeshData x₀
        (MeshCategory.RightMeshData.UniversalCover.extend
          S.standardFormRightMeshData x₀ W (Quiver.reverse e))
        (MeshCategory.RightMeshData.UniversalCover.meshArrow
          S.standardFormRightMeshData z) = W
  have hecast := MeshCategory.RightMeshData.UniversalCover.extend_cast_target
    S.standardFormRightMeshData x₀
      (MeshCategory.RightMeshData.UniversalCover.extend
        S.standardFormRightMeshData x₀ W (Quiver.reverse e))
      (MeshCategory.RightMeshData.UniversalCover.meshArrow
        S.standardFormRightMeshData z) hbase
  exact hecast.symm.trans hext

/-- The raw mesh morphism represented by the polarized partner of an
arbitrary incoming arrow at a nonprojective lifted vertex. -/
def standardFormUniversalPairedIncomingHom
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (d : Quiver.Star W.1) :
    S.standardFormUniversalMeshObj x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) ⟶
      S.standardFormUniversalMeshObj x₀ d.1 :=
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  T.incomingArrowHom (k := k)
    (⟨T.tau W, T.arrowEquiv W d.1 d.2⟩ : Quiver.Star d.1)

/-- A polarized partner of an arbitrary incoming arrow after realization,
with its literal underlying module-Hom type. -/
def standardFormUniversalMappedPairedIncomingHom
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (d : Quiver.Star W.1) :
    S.fgObj (S.standardFormTau
        (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
          S.standardFormRightMeshData x₀ W)) ⟶
      S.fgObj d.1.1 :=
  ((S.standardFormUniversalIndecMeshFunctor x₀).map
    (S.standardFormUniversalPairedIncomingHom x₀ W d)).hom

@[simp]
theorem standardFormUniversalMappedPairedIncomingHom_eq_normalized
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (d : Quiver.Star W.1) :
    S.standardFormUniversalMappedPairedIncomingHom x₀ W d =
      S.standardFormUniversalNormalizedArrowMap x₀
        ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀).arrowEquiv W d.1 d.2) := by
  unfold standardFormUniversalMappedPairedIncomingHom
    standardFormUniversalPairedIncomingHom
  exact S.standardFormUniversalIndecMeshFunctor_map_arrow x₀
    ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀).arrowEquiv W d.1 d.2)

/-- The ordinary mesh relation remains zero after applying it coefficientwise
to an entire fixed-target source fibre. -/
theorem standardFormUniversal_paired_sourceFiber_sum_eq_zero
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (q : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W))) :
    (∑ d : Quiver.Star W.1,
      LinearCovering.sourceFiberPostcomp (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X
        ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀).incomingArrowHom (k := k) d)
        (LinearCovering.sourceFiberPostcomp (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          (S.standardFormUniversalPairedIncomingHom x₀ W d) q)) = 0 := by
  classical
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  induction q using DirectSum.induction_on with
  | zero => simp
  | add q₁ q₂ hq₁ hq₂ =>
      simp_rw [map_add]
      rw [Finset.sum_add_distrib, hq₁, hq₂, add_zero]
  | of Z f =>
      rw [← DirectSum.lof_eq_of k
        (LinearCovering.Fiber
          (S.standardFormUniversalIndecMeshFunctor x₀) X)
        (fun V ↦ V.1 ⟶ S.standardFormUniversalMeshObj x₀
          (MeshCategory.RightMeshData.UniversalCover.tau
            S.standardFormRightMeshData x₀ W)) Z f]
      change (∑ d : Quiver.Star W.1,
        LinearCovering.sourceFiberPostcomp (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          (T.incomingArrowHom (k := k) d)
          (LinearCovering.sourceFiberPostcomp (k := k)
            (S.standardFormUniversalIndecMeshFunctor x₀) X
            (S.standardFormUniversalPairedIncomingHom x₀ W d)
            (LinearCovering.sourceFiberLof (k := k)
              (S.standardFormUniversalIndecMeshFunctor x₀) X
              (S.standardFormUniversalMeshObj x₀
                (MeshCategory.RightMeshData.UniversalCover.tau
                  S.standardFormRightMeshData x₀ W)) Z f))) = 0
      simp_rw [LinearCovering.sourceFiberPostcomp_lof]
      calc
        (∑ d : Quiver.Star W.1,
          LinearCovering.sourceFiberPostcomp (k := k)
            (S.standardFormUniversalIndecMeshFunctor x₀) X
            (T.incomingArrowHom (k := k) d)
            (LinearCovering.sourceFiberLof (k := k)
              (S.standardFormUniversalIndecMeshFunctor x₀) X
              (S.standardFormUniversalMeshObj x₀ d.1) Z
              (f ≫ S.standardFormUniversalPairedIncomingHom x₀ W d))) =
            ∑ d : Quiver.Star W.1,
              LinearCovering.sourceFiberLof (k := k)
                (S.standardFormUniversalIndecMeshFunctor x₀) X
                (S.standardFormUniversalMeshObj x₀ W.1) Z
                ((f ≫ S.standardFormUniversalPairedIncomingHom x₀ W d) ≫
                  T.incomingArrowHom (k := k) d) := by
          apply Finset.sum_congr rfl
          intro d _
          exact LinearCovering.sourceFiberPostcomp_lof (k := k)
            (S.standardFormUniversalIndecMeshFunctor x₀) X
            (T.incomingArrowHom (k := k) d) Z
            (f ≫ S.standardFormUniversalPairedIncomingHom x₀ W d)
        _ = 0 := by
          rw [← map_sum]
          have hrel : (∑ d : Quiver.Star W.1,
              (f ≫ S.standardFormUniversalPairedIncomingHom x₀ W d) ≫
                T.incomingArrowHom (k := k) d) = 0 := by
            convert T.raw_paired_incomingSum_eq_zero (k := k) W Z.1 f using 1
            apply Finset.sum_congr rfl
            intro d _
            simp only [standardFormUniversalPairedIncomingHom, T,
              Category.assoc]
            congr
          rw [hrel, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary mesh relation remains zero after applying it
coefficientwise to an entire fixed-source target fibre. -/
theorem standardFormUniversal_paired_targetFiber_sum_eq_zero
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (q : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ S.standardFormUniversalMeshObj x₀ W.1 ⟶ Z.1)) :
    (∑ d : Quiver.Star W.1,
      LinearCovering.targetFiberPrecomp (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X
        (S.standardFormUniversalPairedIncomingHom x₀ W d)
        (LinearCovering.targetFiberPrecomp (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData x₀).incomingArrowHom (k := k) d)
          q)) = 0 := by
  classical
  let F := S.standardFormUniversalIndecMeshFunctor x₀
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  induction q using DirectSum.induction_on with
  | zero => simp
  | add q₁ q₂ hq₁ hq₂ =>
      simp_rw [map_add]
      rw [Finset.sum_add_distrib, hq₁, hq₂, add_zero]
  | of Z f =>
      rw [← DirectSum.lof_eq_of k
        (LinearCovering.Fiber F X)
        (fun V ↦ S.standardFormUniversalMeshObj x₀ W.1 ⟶ V.1) Z f]
      change (∑ d : Quiver.Star W.1,
        LinearCovering.targetFiberPrecomp (k := k) F X
          (S.standardFormUniversalPairedIncomingHom x₀ W d)
          (LinearCovering.targetFiberPrecomp (k := k) F X
            (T.incomingArrowHom (k := k) d)
            (LinearCovering.targetFiberLof (k := k) F
              (S.standardFormUniversalMeshObj x₀ W.1) X Z f))) = 0
      have hrel : (∑ d : Quiver.Star W.1,
          (S.standardFormUniversalPairedIncomingHom x₀ W d ≫
            T.incomingArrowHom (k := k) d) ≫ f) = 0 := by
        have h := T.paired_incomingSum_comp_eq_zero (k := k) W Z.1 f
        simpa only [standardFormUniversalPairedIncomingHom, T,
          Category.assoc] using h
      have hprecomp (d : Quiver.Star W.1) :
          LinearCovering.targetFiberPrecomp (k := k) F X
              (S.standardFormUniversalPairedIncomingHom x₀ W d)
              (LinearCovering.targetFiberPrecomp (k := k) F X
                (T.incomingArrowHom (k := k) d)
                (LinearCovering.targetFiberLof (k := k) F
                  (S.standardFormUniversalMeshObj x₀ W.1) X Z f)) =
            LinearCovering.targetFiberLof (k := k) F
              (S.standardFormUniversalMeshObj x₀
                (MeshCategory.RightMeshData.UniversalCover.tau
                  S.standardFormRightMeshData x₀ W)) X Z
              ((S.standardFormUniversalPairedIncomingHom x₀ W d ≫
                T.incomingArrowHom (k := k) d) ≫ f) := by
        rw [LinearCovering.targetFiberPrecomp_comp,
          LinearCovering.targetFiberPrecomp_lof]
      calc
        (∑ d : Quiver.Star W.1,
          LinearCovering.targetFiberPrecomp (k := k) F X
            (S.standardFormUniversalPairedIncomingHom x₀ W d)
            (LinearCovering.targetFiberPrecomp (k := k) F X
              (T.incomingArrowHom (k := k) d)
              (LinearCovering.targetFiberLof (k := k) F
                (S.standardFormUniversalMeshObj x₀ W.1) X Z f))) =
            ∑ d, LinearCovering.targetFiberLof (k := k) F
              (S.standardFormUniversalMeshObj x₀
                (MeshCategory.RightMeshData.UniversalCover.tau
                  S.standardFormRightMeshData x₀ W)) X Z
              ((S.standardFormUniversalPairedIncomingHom x₀ W d ≫
                T.incomingArrowHom (k := k) d) ≫ f) := by
          apply Finset.sum_congr rfl
          intro d _
          exact hprecomp d
        _ = LinearCovering.targetFiberLof (k := k) F
              (S.standardFormUniversalMeshObj x₀
                (MeshCategory.RightMeshData.UniversalCover.tau
                  S.standardFormRightMeshData x₀ W)) X Z
              (∑ d, (S.standardFormUniversalPairedIncomingHom x₀ W d ≫
                T.incomingArrowHom (k := k) d) ≫ f) := by rw [map_sum]
        _ = 0 := by rw [hrel, map_zero]

/-- Every incoming arrow of the universal mesh has radical image, without
choosing a displayed middle-term index. -/
theorem standardFormUniversalNormalizedIncomingArrow_mem_radical
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Star W) :
    S.standardFormUniversalNormalizedArrowMap x₀ d.2 ∈
      S.fgNilpotentRadicalData.ideal.hom (S.fgObj d.1.1) (S.fgObj W.1) := by
  obtain ⟨i, hi⟩ :=
    (S.standardFormUniversalMiddleStarEquiv x₀ W).surjective d
  subst d
  rw [S.standardFormUniversalMiddleStarEquiv_apply]
  apply (S.fgNilpotentRadicalData.mem_ideal_iff _).2
  apply (S.finiteTauCategoryData.isRadicalMorphism_iff_not_isSplitEpi_to_obj
    _).2
  exact (S.standardFormUniversalNormalizedArrowMap_isIrreducible x₀
    (S.standardFormUniversalMiddleArrow x₀ W i)).not_isSplitEpi

/-- Every fixed-target source-fibre family is a possible scalar at the
target vertex plus families postcomposed with the arrows entering that
vertex.  This is the direct-sum form of decomposition by the final arrow. -/
theorem standardFormUniversal_exists_sourceFiber_eq_diagonal_add_incoming
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ W)) :
    ∃ (r : k)
      (b : ∀ d : Quiver.Star W,
        DirectSum
          (LinearCovering.Fiber
            (S.standardFormUniversalIndecMeshFunctor x₀) X)
          (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ d.1)),
      a = S.standardFormUniversalSourceFiberDiagonal x₀ X W r +
        ∑ d : Quiver.Star W,
          LinearCovering.sourceFiberPostcomp (k := k)
            (S.standardFormUniversalIndecMeshFunctor x₀) X
            ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
              S.standardFormRightMeshData x₀).incomingArrowHom (k := k) d)
            (b d) := by
  classical
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  induction a using DirectSum.induction_on with
  | zero =>
      refine ⟨0, fun _ ↦ 0, ?_⟩
      simp
  | add a₁ a₂ h₁ h₂ =>
      obtain ⟨r₁, b₁, hb₁⟩ := h₁
      obtain ⟨r₂, b₂, hb₂⟩ := h₂
      refine ⟨r₁ + r₂, fun d ↦ b₁ d + b₂ d, ?_⟩
      rw [hb₁, hb₂, S.standardFormUniversalSourceFiberDiagonal_add]
      simp_rw [map_add]
      rw [Finset.sum_add_distrib]
      abel
  | of Z f =>
      rw [← DirectSum.lof_eq_of k
        (LinearCovering.Fiber
          (S.standardFormUniversalIndecMeshFunctor x₀) X)
        (fun V ↦ V.1 ⟶ S.standardFormUniversalMeshObj x₀ W) Z f]
      obtain ⟨r, c, hf⟩ :=
        T.exists_eq_rawDiagonalScalar_add_rawIncomingSum f
      let b : ∀ d : Quiver.Star W,
          DirectSum
            (LinearCovering.Fiber
              (S.standardFormUniversalIndecMeshFunctor x₀) X)
            (fun V ↦ V.1 ⟶ S.standardFormUniversalMeshObj x₀ d.1) :=
        fun d ↦ LinearCovering.sourceFiberLof (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          (S.standardFormUniversalMeshObj x₀ d.1) Z (c d)
      by_cases hZW : Z.1 = S.standardFormUniversalMeshObj x₀ W
      · have hXW : X = W.1 := by
          have h := Z.2
          rw [hZW] at h
          exact h.symm
        have hdiag :
            (DirectSum.lof k
                (LinearCovering.Fiber
                  (S.standardFormUniversalIndecMeshFunctor x₀) X)
                (fun Y ↦ Y.1 ⟶ S.standardFormUniversalMeshObj x₀ W) Z)
                (T.rawDiagonalScalar Z.1 W r) =
              S.standardFormUniversalSourceFiberDiagonal x₀ X W r := by
          unfold MeshCategory.RightMeshData.rawDiagonalScalar
          rw [dif_pos hZW]
          unfold standardFormUniversalSourceFiberDiagonal
          rw [dif_pos hXW]
          subst X
          have hZ : Z =
              (⟨S.standardFormUniversalMeshObj x₀ W, rfl⟩ :
                LinearCovering.Fiber
                  (S.standardFormUniversalIndecMeshFunctor x₀) W.1) :=
            Subtype.ext hZW
          subst Z
          unfold LinearCovering.sourceFiberLof
          rfl
        refine ⟨r, b, ?_⟩
        rw [hf, map_add, hdiag]
        apply congrArg₂ (.+.) rfl
        rw [MeshCategory.RightMeshData.rawIncomingSum, map_sum]
        apply Finset.sum_congr rfl
        intro d _
        exact (LinearCovering.sourceFiberPostcomp_lof (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          (T.incomingArrowHom (k := k) d) Z (c d)).symm
      · have hdiag : T.rawDiagonalScalar Z.1 W r = 0 := by
          unfold MeshCategory.RightMeshData.rawDiagonalScalar
          rw [dif_neg]
          exact hZW
        refine ⟨0, b, ?_⟩
        rw [hf, hdiag, zero_add,
          MeshCategory.RightMeshData.rawIncomingSum, map_sum,
          S.standardFormUniversalSourceFiberDiagonal_zero, zero_add]
        apply Finset.sum_congr rfl
        intro d _
        exact (LinearCovering.sourceFiberPostcomp_lof (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          (T.incomingArrowHom (k := k) d) Z (c d)).symm

/-- Every displayed normalized arrow lies in the categorical radical ideal
of the representation-finite module category. -/
theorem standardFormUniversalNormalizedMiddleArrow_mem_radical
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalMiddleArrow x₀ W i) ∈
      S.fgNilpotentRadicalData.ideal.hom
        (S.fgObj (FiniteTauMatrix.rightMiddleLabel
          S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i))
        (S.fgObj W.1) := by
  apply (S.fgNilpotentRadicalData.mem_ideal_iff _).2
  apply (S.finiteTauCategoryData.isRadicalMorphism_iff_not_isSplitEpi_to_obj
    _).2
  exact (S.standardFormUniversalNormalizedArrowMap_isIrreducible x₀
    (S.standardFormUniversalMiddleArrow x₀ W i)).not_isSplitEpi

set_option backward.isDefEq.respectTransparency false in
/-- At a nonprojective lifted vertex, the normalized mesh source is a weak
kernel of the normalized mesh sink.  This is the local exactness statement
used to peel a relation one mesh layer farther from its endpoint. -/
theorem standardFormUniversalNormalizedRealizedSource_factors_of_comp_sink_eq_zero
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    {X : FGModuleCat Aᵐᵒᵖ}
    (q : X ⟶
      (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂)
    (hq : q ≫ S.standardFormUniversalRealizedSink x₀
      (S.standardFormUniversalNormalizedArrowMap x₀) W.1 = 0) :
    ∃ t : X ⟶ S.fgObj
        (S.standardFormTau
          (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
            S.standardFormRightMeshData x₀ W)),
      t ≫ S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W = q := by
  let z := MeshCategory.RightMeshData.UniversalCover.baseNonprojective
    S.standardFormRightMeshData x₀ W
  let f := S.standardFormRightSink W.1.1
  let g := S.standardFormUniversalRealizedSink x₀
    (S.standardFormUniversalNormalizedArrowMap x₀) W.1
  obtain ⟨e, he⟩ := exists_rightAlmostSplit_middleIso
    (S.standardFormRightSink_isRightAlmostSplit W.1.1)
    (S.standardFormRightSink_isRightMinimal W.1.1)
    (S.standardFormUniversalNormalizedRealizedSink_isRightAlmostSplit x₀ W.1)
    (S.standardFormUniversalNormalizedRealizedSink_isRightMinimal x₀ W.1)
  have heg : e.inv ≫ f = g := by
    dsimp only [f, g]
    rw [← he]
    simp
  let i := S.standardFormRightSource z ≫ e.hom
  have hiAS : IsLeftAlmostSplit i :=
    leftAlmostSplit_postcomp_iso
      (S.standardFormRightSource_isLeftAlmostSplit z) e
  haveI : Mono (S.standardFormRightSource z) :=
    S.standardFormRightSource_mono z
  haveI : Mono i := by
    dsimp only [i]
    infer_instance
  have factor_i {Y : FGModuleCat Aᵐᵒᵖ}
      (r : Y ⟶ (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂)
      (hr : r ≫ g = 0) : ∃ s, s ≫ i = r := by
    have hr' : (r ≫ e.inv) ≫ f = 0 := by
      simpa only [Category.assoc, heg] using hr
    obtain ⟨s, hs⟩ :=
      S.standardFormRightSource_factors_of_comp_rightSink_eq_zero z
        (r ≫ e.inv) hr'
    refine ⟨s, ?_⟩
    dsimp only [i]
    calc
      s ≫ (S.standardFormRightSource z ≫ e.hom) =
          (r ≫ e.inv) ≫ e.hom := by rw [← Category.assoc, hs]
      _ = r := by simp
  let source := S.standardFormUniversalRealizedSource x₀
    (S.standardFormUniversalNormalizedArrowMap x₀) W
  have hsourceMono : Mono source :=
    (S.standardFormUniversalNormalizedRealizedSource_isLeftAlmostSplit x₀ W)
      |>.mono_of_nonsplit_mono i hiAS.not_isSplitMono
  letI : Mono source := hsourceMono
  obtain ⟨u, hu⟩ := factor_i source
    (S.standardFormUniversalNormalized_mesh_zero x₀ W)
  haveI : Mono u := mono_of_mono_fac hu
  letI : IsIso u := RightModule.isIso_of_mono_finiteLength_endomorphism
    (fgModule_isFiniteLength (k := k)
      (S.fgObj (S.standardFormTau z))) u
  obtain ⟨s, hs⟩ := factor_i q hq
  refine ⟨s ≫ inv u, ?_⟩
  dsimp only [source] at hu ⊢
  calc
    (s ≫ inv u) ≫
        S.standardFormUniversalRealizedSource x₀
          (S.standardFormUniversalNormalizedArrowMap x₀) W =
      (s ≫ inv u) ≫ (u ≫ i) := by rw [hu]
    _ = s ≫ i := by simp
    _ = q := hs

set_option backward.isDefEq.respectTransparency false in
/-- At a nonprojective lifted vertex, the normalized mesh sink is a weak
cokernel of the normalized mesh source.  This is the target-side local
exactness statement used to peel a relation one mesh layer farther from its
source. -/
theorem standardFormUniversalNormalizedRealizedSink_factors_of_source_comp_eq_zero
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    {X : FGModuleCat Aᵐᵒᵖ}
    (q : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂ ⟶ X)
    (hq : S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W ≫ q = 0) :
    ∃ t : S.fgObj W.1.1 ⟶ X,
      S.standardFormUniversalRealizedSink x₀
          (S.standardFormUniversalNormalizedArrowMap x₀) W.1 ≫ t = q := by
  let source := S.standardFormUniversalRealizedSource x₀
    (S.standardFormUniversalNormalizedArrowMap x₀) W
  let sink := S.standardFormUniversalRealizedSink x₀
    (S.standardFormUniversalNormalizedArrowMap x₀) W.1
  let x : {x : Fin S.n // ¬ Injective (S.fgObj x)} :=
    ⟨(MeshCategory.RightMeshData.UniversalCover.tau
      S.standardFormRightMeshData x₀ W).1,
      S.standardFormUniversal_tau_noninjective x₀ W⟩
  let B := S.minimalLeftAlmostSplitAt x.1
  letI : Mono B.map := S.noninjectiveLeftAlmostSplit_mono x
  have hsourceMono : Mono source :=
    (S.standardFormUniversalNormalizedRealizedSource_isLeftAlmostSplit x₀ W)
      |>.mono_of_nonsplit_mono B.map B.leftAlmostSplit.not_isSplitMono
  letI : Mono source := hsourceMono
  have hWnp : ¬ Projective (S.fgObj W.1.1) := by
    simpa [MeshCategory.RightMeshData.UniversalCover.projectiveSet,
      standardFormRightMeshData, standardFormProjectiveSet] using W.2
  have hsinkEpi : Epi sink :=
    IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      S.almostSplitSkeleton sink
        (S.standardFormUniversalNormalizedRealizedSink_isRightAlmostSplit
          x₀ W.1) hWnp
  letI : Epi sink := hsinkEpi
  have hzero : source ≫ sink = 0 :=
    S.standardFormUniversalNormalized_mesh_zero x₀ W
  have hkernel : IsLimit (KernelFork.ofι source hzero) := by
    apply KernelFork.IsLimit.ofι' source hzero
    intro Y r hr
    let hfactor :=
      S.standardFormUniversalNormalizedRealizedSource_factors_of_comp_sink_eq_zero
        x₀ W r hr
    exact ⟨Classical.choose hfactor, Classical.choose_spec hfactor⟩
  let hcok := Abelian.epiIsCokernelOfKernel
    (KernelFork.ofι source hzero) hkernel
  obtain ⟨t, ht⟩ := CokernelCofork.IsColimit.desc' hcok q hq
  exact ⟨t, ht⟩

/-- Expanding through the displayed middle biproduct writes a factor through
the normalized realized sink as the finite sum of its arrow components. -/
theorem standardFormUniversal_factor_realizedSink_eq_sum
    (x₀ : Fin S.n)
    (X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (h : S.fgObj X ⟶
      (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂) :
    h ≫ S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W =
      ∑ i : Fin (FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
        (h ≫ FiniteTauMatrix.rightMiddleProjection
            S.finiteTauCategoryData W.1 i) ≫
          S.standardFormUniversalNormalizedArrowMap x₀
            (S.standardFormUniversalMiddleArrow x₀ W i) := by
  classical
  let E := (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂
  let n := FiniteTauMatrix.rightMiddleArity
    S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1
  let F : Fin n → FGModuleCat Aᵐᵒᵖ := fun i ↦
    S.fgObj (FiniteTauMatrix.rightMiddleLabel
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i)
  let e : E ≅ ⨁ F :=
    FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1
  let D : ∀ i, F i ⟶ S.fgObj W.1 := fun i ↦
    S.standardFormUniversalNormalizedArrowMap x₀
      (S.standardFormUniversalMiddleArrow x₀ W i)
  unfold standardFormUniversalRealizedSink
    FiniteTauMatrix.rightMiddleProjection
  change h ≫ (e.hom ≫ biproduct.desc D) = ∑ i : Fin n,
    (h ≫ (e.hom ≫ biproduct.π F i)) ≫
      D i
  calc
    h ≫ (e.hom ≫ biproduct.desc D) =
        h ≫ e.hom ≫ (∑ i : Fin n,
          biproduct.π F i ≫ biproduct.ι F i) ≫
            biproduct.desc D := by
      rw [biproduct.total]
      simp
    _ = _ := by
      simp only [Preadditive.comp_sum, Preadditive.sum_comp,
        Category.assoc, biproduct.ι_desc]

/-- Assemble the displayed incoming coefficients into the chosen middle term
of the almost-split sink at `W`. -/
def standardFormUniversalIncomingMiddleLift
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (c : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
      S.fgObj X ⟶ S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i)) :
    S.fgObj X ⟶
      (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ :=
  biproduct.lift c ≫
    (FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1).inv

/-- A component of the assembled incoming middle map is its displayed
coefficient. -/
@[reassoc (attr := simp)]
theorem standardFormUniversalIncomingMiddleLift_projection
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (c : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
      S.fgObj X ⟶ S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i))
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    S.standardFormUniversalIncomingMiddleLift x₀ X W c ≫
        FiniteTauMatrix.rightMiddleProjection
          S.finiteTauCategoryData W.1 i =
      c i := by
  unfold standardFormUniversalIncomingMiddleLift
    FiniteTauMatrix.rightMiddleProjection
  erw [Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_π]

set_option backward.isDefEq.respectTransparency false in
/-- Composing the assembled middle map with the normalized sink is the sum
of its displayed incoming-arrow composites. -/
theorem standardFormUniversalIncomingMiddleLift_comp_sink
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (c : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
      S.fgObj X ⟶ S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i)) :
    S.standardFormUniversalIncomingMiddleLift x₀ X W c ≫
        S.standardFormUniversalRealizedSink x₀
          (S.standardFormUniversalNormalizedArrowMap x₀) W =
      ∑ i : Fin (FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
        c i ≫ S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalMiddleArrow x₀ W i) := by
  simpa only [S.standardFormUniversalIncomingMiddleLift_projection] using
    S.standardFormUniversal_factor_realizedSink_eq_sum x₀ X W
      (S.standardFormUniversalIncomingMiddleLift x₀ X W c)

/-- Assemble maps out of the displayed middle summands into a map from the
chosen right-mesh middle term. -/
def standardFormUniversalOutgoingMiddleDesc
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (c : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
      S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i) ⟶
        S.fgObj X) :
    (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶ S.fgObj X :=
  (FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1).hom ≫ biproduct.desc c

/-- Restricting the assembled outgoing middle map to a displayed summand
recovers its coefficient. -/
@[reassoc (attr := simp)]
theorem rightMiddleInclusion_standardFormUniversalOutgoingMiddleDesc
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (c : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
      S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i) ⟶
        S.fgObj X)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    FiniteTauMatrix.rightMiddleInclusion
        S.finiteTauCategoryData W.1 i ≫
      S.standardFormUniversalOutgoingMiddleDesc x₀ X W c = c i := by
  simp [FiniteTauMatrix.rightMiddleInclusion,
    standardFormUniversalOutgoingMiddleDesc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Composing the normalized mesh source with an assembled outgoing middle
map is the sum of the polarized-arrow composites. -/
theorem standardFormUniversalRealizedSource_comp_outgoingMiddleDesc
    (x₀ X : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (c : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1),
      S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1 i) ⟶
        S.fgObj X) :
    S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalNormalizedArrowMap x₀) W ≫
      S.standardFormUniversalOutgoingMiddleDesc x₀ X W.1 c =
        ∑ i, S.standardFormUniversalNormalizedArrowMap x₀
            (S.standardFormUniversalPairedMiddleArrow x₀ W i) ≫ c i := by
  classical
  unfold standardFormUniversalRealizedSource
    standardFormUniversalOutgoingMiddleDesc
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact biproduct.lift_desc

set_option backward.isDefEq.respectTransparency false in
/-- At a nonprojective lifted endpoint, every relation among the normalized
polarized arrows leaving its translate is generated by the arrows entering
the endpoint. -/
theorem standardFormUniversal_nonprojective_outgoing_exact
    (x₀ X : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (c : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1),
      S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1 i) ⟶
        S.fgObj X)
    (hc : (∑ i, S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalPairedMiddleArrow x₀ W i) ≫ c i) = 0) :
    ∃ t : S.fgObj W.1.1 ⟶ S.fgObj X,
      ∀ i, c i = S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalMiddleArrow x₀ W.1 i) ≫ t := by
  let q := S.standardFormUniversalOutgoingMiddleDesc x₀ X W.1 c
  have hq : S.standardFormUniversalRealizedSource x₀
      (S.standardFormUniversalNormalizedArrowMap x₀) W ≫ q = 0 := by
    dsimp only [q]
    rw [S.standardFormUniversalRealizedSource_comp_outgoingMiddleDesc, hc]
  obtain ⟨t, ht⟩ :=
    S.standardFormUniversalNormalizedRealizedSink_factors_of_source_comp_eq_zero
      x₀ W q hq
  refine ⟨t, fun i ↦ ?_⟩
  calc
    c i = FiniteTauMatrix.rightMiddleInclusion
          S.finiteTauCategoryData W.1.1 i ≫ q :=
      (S.rightMiddleInclusion_standardFormUniversalOutgoingMiddleDesc
        x₀ X W.1 c i).symm
    _ = FiniteTauMatrix.rightMiddleInclusion
          S.finiteTauCategoryData W.1.1 i ≫
        (S.standardFormUniversalRealizedSink x₀
          (S.standardFormUniversalNormalizedArrowMap x₀) W.1 ≫ t) := by
      rw [ht]
    _ = S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalMiddleArrow x₀ W.1 i) ≫ t := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Nonprojective outgoing exactness in the star coordinates at the mesh
endpoint: a relation among polarized partners factors through the incoming
arrows. -/
theorem standardFormUniversal_nonprojective_outgoingStar_exact
    (x₀ X : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (c : ∀ d : Quiver.Star W.1, S.fgObj d.1.1 ⟶ S.fgObj X)
    (hc : (∑ d, S.standardFormUniversalMappedPairedIncomingHom x₀ W d ≫
      c d) = 0) :
    ∃ t : S.fgObj W.1.1 ⟶ S.fgObj X,
      ∀ d, c d =
        S.standardFormUniversalMappedIncomingHom x₀ W.1 d ≫ t := by
  classical
  let e := S.standardFormUniversalMiddleStarEquiv x₀ W.1
  let c' : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1),
      S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1 i) ⟶
        S.fgObj X := fun i ↦ c
    (⟨S.standardFormUniversalMiddleVertex x₀ W.1 i,
      S.standardFormUniversalMiddleArrow x₀ W.1 i⟩ : Quiver.Star W.1)
  let f : Quiver.Star W.1 →
      (S.fgObj
          (MeshCategory.RightMeshData.UniversalCover.tau
            S.standardFormRightMeshData x₀ W).1 ⟶ S.fgObj X) :=
    fun d ↦ S.standardFormUniversalMappedPairedIncomingHom x₀ W d ≫ c d
  have hc' : (∑ i, S.standardFormUniversalNormalizedArrowMap x₀
      (S.standardFormUniversalPairedMiddleArrow x₀ W i) ≫ c' i) = 0 := by
    calc
      (∑ i, S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalPairedMiddleArrow x₀ W i) ≫ c' i) =
          ∑ i, f
            (⟨S.standardFormUniversalMiddleVertex x₀ W.1 i,
              S.standardFormUniversalMiddleArrow x₀ W.1 i⟩ :
                Quiver.Star W.1) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [c', f,
          S.standardFormUniversalMappedPairedIncomingHom_eq_normalized]
        rfl
      _ = ∑ i, f (e i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg f
          (S.standardFormUniversalMiddleStarEquiv_apply x₀ W.1 i).symm
      _ = ∑ d, f d := e.sum_comp _
      _ = 0 := hc
  obtain ⟨t, ht⟩ := S.standardFormUniversal_nonprojective_outgoing_exact
    x₀ X W c' hc'
  refine ⟨t, fun d ↦ ?_⟩
  obtain ⟨i, hi⟩ := e.surjective d
  subst d
  rw [S.standardFormUniversalMiddleStarEquiv_apply]
  calc
    c (⟨S.standardFormUniversalMiddleVertex x₀ W.1 i,
        S.standardFormUniversalMiddleArrow x₀ W.1 i⟩ : Quiver.Star W.1) =
        c' i := rfl
    _ = S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalMiddleArrow x₀ W.1 i) ≫ t := ht i
    _ = S.standardFormUniversalMappedIncomingHom x₀ W.1
        (⟨S.standardFormUniversalMiddleVertex x₀ W.1 i,
          S.standardFormUniversalMiddleArrow x₀ W.1 i⟩ : Quiver.Star W.1) ≫
        t := by
      rw [S.standardFormUniversalMappedIncomingHom_eq_normalized]

/-- Polarization identifies the incoming star of a nonprojective mesh
endpoint with the outgoing costar of its translated source. -/
def standardFormUniversalMeshStarCostarEquiv
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    Quiver.Star W.1 ≃ Quiver.Costar
      (MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ W) :=
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  Equiv.sigmaCongrRight fun Y ↦ T.arrowEquiv W Y

@[simp]
theorem standardFormUniversalMeshStarCostarEquiv_apply
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (d : Quiver.Star W.1) :
    S.standardFormUniversalMeshStarCostarEquiv x₀ W d =
      ⟨d.1,
        (MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀).arrowEquiv W d.1 d.2⟩ :=
  rfl

/-- The costar arrow obtained by polarization realizes the same normalized
map as the corresponding paired incoming arrow. -/
theorem standardFormUniversalMappedOutgoingHom_meshStarCostarEquiv
    (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (d : Quiver.Star W.1) :
    S.standardFormUniversalMappedOutgoingHom x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W)
        (S.standardFormUniversalMeshStarCostarEquiv x₀ W d) =
      S.standardFormUniversalMappedPairedIncomingHom x₀ W d := by
  rw [S.standardFormUniversalMappedOutgoingHom_eq_normalized,
    S.standardFormUniversalMappedPairedIncomingHom_eq_normalized]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A vanishing family after all arrows leaving a translated mesh source is
obtained by postcomposing the arrows entering the mesh endpoint. -/
theorem standardFormUniversal_nonprojective_translatedCostar_exact
    (x₀ X : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (c : ∀ d : Quiver.Costar
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W),
      S.fgObj d.1.1 ⟶ S.fgObj X)
    (hc : (∑ d, S.standardFormUniversalMappedOutgoingHom x₀
        (MeshCategory.RightMeshData.UniversalCover.tau
          S.standardFormRightMeshData x₀ W) d ≫ c d) = 0) :
    ∃ t : S.fgObj W.1.1 ⟶ S.fgObj X,
      ∀ d : Quiver.Star W.1,
        c (S.standardFormUniversalMeshStarCostarEquiv x₀ W d) =
          S.standardFormUniversalMappedIncomingHom x₀ W.1 d ≫ t := by
  classical
  let e := S.standardFormUniversalMeshStarCostarEquiv x₀ W
  let c' : ∀ d : Quiver.Star W.1, S.fgObj d.1.1 ⟶ S.fgObj X :=
    fun d ↦ c (e d)
  let f : Quiver.Costar
      (MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ W) →
      (S.fgObj
          (MeshCategory.RightMeshData.UniversalCover.tau
            S.standardFormRightMeshData x₀ W).1 ⟶ S.fgObj X) :=
    fun d ↦ S.standardFormUniversalMappedOutgoingHom x₀
      (MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ W) d ≫ c d
  have hc' : (∑ d, S.standardFormUniversalMappedPairedIncomingHom x₀ W d ≫
      c' d) = 0 := by
    calc
      (∑ d, S.standardFormUniversalMappedPairedIncomingHom x₀ W d ≫
          c' d) = ∑ d, f (e d) := by
        apply Finset.sum_congr rfl
        intro d _
        dsimp only [c', f]
        rw [S.standardFormUniversalMappedOutgoingHom_meshStarCostarEquiv]
      _ = ∑ d, f d := e.sum_comp _
      _ = 0 := hc
  obtain ⟨t, ht⟩ :=
    S.standardFormUniversal_nonprojective_outgoingStar_exact x₀ X W c' hc'
  exact ⟨t, ht⟩

/-- For a noninjective lifted source, its outgoing costar is parametrized by
the incoming star of the canonical mesh endpoint whose translate is that
source. -/
def standardFormUniversalNoninjectiveOutgoingCostarEquiv
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1)) :
    Quiver.Star (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1 ≃
      Quiver.Costar W :=
  (S.standardFormUniversalMeshStarCostarEquiv x₀
      (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW)).trans
    (S.standardFormUniversalCostarCast x₀
      (S.standardFormUniversalNoninjectiveMeshEndpoint_tau x₀ W hW))

@[simp]
theorem standardFormUniversalNoninjectiveOutgoingCostarEquiv_fst
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1))
    (d : Quiver.Star
      (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1) :
    (S.standardFormUniversalNoninjectiveOutgoingCostarEquiv x₀ W hW d).1 = d.1 :=
  rfl

/-- The incoming star arrow associated with an outgoing costar at a
noninjective source. -/
def standardFormUniversalNoninjectiveIncomingCostarArrow
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1))
    (d : Quiver.Costar W) : Quiver.Star
      (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1 :=
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  let U := S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW
  let hτ := S.standardFormUniversalNoninjectiveMeshEndpoint_tau x₀ W hW
  ⟨d.1, (T.arrowEquiv U d.1).symm
    (Quiver.Hom.cast rfl hτ.symm d.2)⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem standardFormUniversalNoninjectiveIncomingCostarArrow_apply
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1))
    (d : Quiver.Star
      (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1) :
    S.standardFormUniversalNoninjectiveIncomingCostarArrow x₀ W hW
        (S.standardFormUniversalNoninjectiveOutgoingCostarEquiv x₀ W hW d) = d := by
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  let U := S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW
  let hτ := S.standardFormUniversalNoninjectiveMeshEndpoint_tau x₀ W hW
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change (T.arrowEquiv U d.1).symm
      (Quiver.Hom.cast rfl hτ.symm
        (Quiver.Hom.cast rfl hτ (T.arrowEquiv U d.1 d.2))) = d.2
    rw [Quiver.Hom.cast_cast]
    have hp : hτ.trans hτ.symm = rfl := Subsingleton.elim _ _
    rw [hp, Quiver.Hom.cast_rfl_rfl, Equiv.symm_apply_apply]

/-- The incoming arrow associated with an outgoing costar at a noninjective
source, with its source definitionally equal to the costar endpoint. -/
def standardFormUniversalNoninjectiveIncomingCostarHom
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1))
    (d : Quiver.Costar W) :
    S.standardFormUniversalMeshObj x₀ d.1 ⟶
      S.standardFormUniversalMeshObj x₀
        (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1 :=
  (MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀).incomingArrowHom (k := k)
    (S.standardFormUniversalNoninjectiveIncomingCostarArrow x₀ W hW d)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem standardFormUniversalNoninjectiveIncomingCostarHom_apply
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1))
    (d : Quiver.Star
      (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1) :
    S.standardFormUniversalNoninjectiveIncomingCostarHom x₀ W hW
        (S.standardFormUniversalNoninjectiveOutgoingCostarEquiv x₀ W hW d) =
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀).incomingArrowHom (k := k) d := by
  unfold standardFormUniversalNoninjectiveIncomingCostarHom
  apply eq_of_heq
  exact congr_arg_heq (fun a ↦
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀).incomingArrowHom (k := k) a)
    (S.standardFormUniversalNoninjectiveIncomingCostarArrow_apply x₀ W hW d)

set_option backward.isDefEq.respectTransparency false in
/-- At a noninjective lifted source, a vanishing outgoing costar family is
obtained by postcomposing the incoming arrows at its canonical mesh endpoint. -/
theorem standardFormUniversal_noninjective_outgoingCostar_exact
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1))
    (c : ∀ d : Quiver.Costar W, S.fgObj d.1.1 ⟶ S.fgObj X)
    (hc : (∑ d, S.standardFormUniversalMappedOutgoingHom x₀ W d ≫ c d) = 0) :
    ∃ t : S.fgObj
        (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1.1 ⟶
          S.fgObj X,
      ∀ d : Quiver.Star
          (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1,
        c (S.standardFormUniversalNoninjectiveOutgoingCostarEquiv x₀ W hW d) =
          S.standardFormUniversalMappedIncomingHom x₀
            (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1 d ≫ t := by
  classical
  let U := S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW
  let hτ := S.standardFormUniversalNoninjectiveMeshEndpoint_tau x₀ W hW
  let ecast := S.standardFormUniversalCostarCast x₀ hτ
  let c' : ∀ d : Quiver.Costar
      (MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ U),
      S.fgObj d.1.1 ⟶ S.fgObj X := fun d ↦ c (ecast d)
  let f : Quiver.Costar W → (S.fgObj W.1 ⟶ S.fgObj X) :=
    fun d ↦ S.standardFormUniversalMappedOutgoingHom x₀ W d ≫ c d
  let q : S.fgObj
      (MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ U).1 ⟶ S.fgObj X :=
    ∑ d, S.standardFormUniversalMappedOutgoingHom x₀
      (MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ U) d ≫ c' d
  have hpre : eqToHom
      (congrArg (S.standardFormUniversalObj x₀) hτ).symm ≫ q = 0 := by
    dsimp only [q]
    calc
      eqToHom (congrArg (S.standardFormUniversalObj x₀) hτ).symm ≫
          (∑ d, S.standardFormUniversalMappedOutgoingHom x₀
            (MeshCategory.RightMeshData.UniversalCover.tau
              S.standardFormRightMeshData x₀ U) d ≫ c' d) =
          ∑ d, f (ecast d) := by
        rw [Preadditive.comp_sum]
        apply Finset.sum_congr rfl
        intro d _
        dsimp only [f, c']
        rw [← Category.assoc,
          ← S.standardFormUniversalMappedOutgoingHom_costarCast]
      _ = ∑ d, f d := ecast.sum_comp _
      _ = 0 := hc
  have hq : q = 0 := by
    apply (cancel_epi
      (eqToHom (congrArg (S.standardFormUniversalObj x₀) hτ).symm)).1
    simpa using hpre
  obtain ⟨t, ht⟩ :=
    S.standardFormUniversal_nonprojective_translatedCostar_exact
      x₀ X U c' hq
  exact ⟨t, ht⟩

set_option backward.isDefEq.respectTransparency false in
/-- The mesh relation at the canonical endpoint of a noninjective source,
transported to that literal source vertex, vanishes coefficientwise in the
target fibre. -/
theorem standardFormUniversal_noninjective_paired_targetFiber_sum_eq_zero
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : ¬ Injective (S.fgObj W.1))
    (q : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ S.standardFormUniversalMeshObj x₀
        (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1 ⟶ Z.1)) :
    (∑ d : Quiver.Star
        (S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW).1,
      LinearCovering.targetFiberPrecomp (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X
        ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀).outgoingArrowHom (k := k)
            (S.standardFormUniversalNoninjectiveOutgoingCostarEquiv
              x₀ W hW d))
        (LinearCovering.targetFiberPrecomp (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData x₀).incomingArrowHom (k := k) d)
          q)) = 0 := by
  classical
  let F := S.standardFormUniversalIndecMeshFunctor x₀
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  let U := S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW
  let hτ := S.standardFormUniversalNoninjectiveMeshEndpoint_tau x₀ W hW
  let e := S.standardFormUniversalNoninjectiveOutgoingCostarEquiv x₀ W hW
  let hobj := congrArg (S.standardFormUniversalMeshObj x₀) hτ
  have harrow (d : Quiver.Star U.1) :
      T.outgoingArrowHom (k := k) (e d) =
        eqToHom hobj.symm ≫ S.standardFormUniversalPairedIncomingHom x₀ U d := by
    have hc := T.outgoingArrowHom_cast_source (k := k) hτ
      (S.standardFormUniversalMeshStarCostarEquiv x₀ U d)
    change T.outgoingArrowHom (k := k)
        (⟨d.1, Quiver.Hom.cast rfl hτ (T.arrowEquiv U d.1 d.2)⟩ :
          Quiver.Costar W) =
      eqToHom hobj.symm ≫ T.outgoingArrowHom (k := k)
        (⟨d.1, T.arrowEquiv U d.1 d.2⟩ : Quiver.Costar (T.tau U))
    exact hc
  have hmesh := S.standardFormUniversal_paired_targetFiber_sum_eq_zero
    x₀ X U q
  calc
    (∑ d : Quiver.Star U.1,
      LinearCovering.targetFiberPrecomp (k := k) F X
        (T.outgoingArrowHom (k := k) (e d))
        (LinearCovering.targetFiberPrecomp (k := k) F X
          (T.incomingArrowHom (k := k) d) q)) =
        ∑ d : Quiver.Star U.1,
          LinearCovering.targetFiberPrecomp (k := k) F X
            (eqToHom hobj.symm ≫
              S.standardFormUniversalPairedIncomingHom x₀ U d)
            (LinearCovering.targetFiberPrecomp (k := k) F X
              (T.incomingArrowHom (k := k) d) q) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [harrow d]
      rfl
    _ = LinearCovering.targetFiberPrecomp (k := k) F X
          (eqToHom hobj.symm)
          (∑ d : Quiver.Star U.1,
            LinearCovering.targetFiberPrecomp (k := k) F X
              (S.standardFormUniversalPairedIncomingHom x₀ U d)
              (LinearCovering.targetFiberPrecomp (k := k) F X
                (T.incomingArrowHom (k := k) d) q)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d _
      exact (LinearCovering.targetFiberPrecomp_comp (k := k) F X
        (eqToHom hobj.symm)
        (S.standardFormUniversalPairedIncomingHom x₀ U d)
        (LinearCovering.targetFiberPrecomp (k := k) F X
          (T.incomingArrowHom (k := k) d) q)).symm
    _ = 0 := by rw [hmesh, map_zero]

/-- Assemble maps from the chosen minimal left-almost-split summands into a
map out of its middle term. -/
def standardFormUniversalLeftOutgoingMiddleDesc
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (c : ∀ t : (S.minimalLeftAlmostSplitAt W.1).index,
      S.fgObj ((S.minimalLeftAlmostSplitAt W.1).label t) ⟶ S.fgObj X) :
    (S.minimalLeftAlmostSplitAt W.1).middle ⟶ S.fgObj X :=
  (S.minimalLeftAlmostSplitAt W.1).decomposition.hom ≫ biproduct.desc c

set_option backward.isDefEq.respectTransparency false in
/-- A displayed summand of the assembled left-middle map is its prescribed
coefficient. -/
@[reassoc (attr := simp)]
theorem standardFormUniversalLeftOutgoingMiddleDesc_component
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (c : ∀ t : (S.minimalLeftAlmostSplitAt W.1).index,
      S.fgObj ((S.minimalLeftAlmostSplitAt W.1).label t) ⟶ S.fgObj X)
    (t : (S.minimalLeftAlmostSplitAt W.1).index) :
    biproduct.ι
        (fun j ↦ S.fgObj ((S.minimalLeftAlmostSplitAt W.1).label j)) t ≫
      (S.minimalLeftAlmostSplitAt W.1).decomposition.inv ≫
      S.standardFormUniversalLeftOutgoingMiddleDesc x₀ X W c = c t := by
  unfold standardFormUniversalLeftOutgoingMiddleDesc
  simp only [Iso.inv_hom_id_assoc, biproduct.ι_desc]

set_option backward.isDefEq.respectTransparency false in
/-- Composing the realized outgoing source with an assembled left-middle
map is the corresponding finite costar sum. -/
theorem standardFormUniversalRealizedOutgoingSource_comp_leftOutgoingMiddleDesc
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (c : ∀ t : (S.minimalLeftAlmostSplitAt W.1).index,
      S.fgObj ((S.minimalLeftAlmostSplitAt W.1).label t) ⟶ S.fgObj X) :
    S.standardFormUniversalRealizedOutgoingSource x₀ W ≫
      S.standardFormUniversalLeftOutgoingMiddleDesc x₀ X W c =
        ∑ t, S.standardFormUniversalMappedOutgoingHom x₀ W
            (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
          eqToHom (congrArg S.fgObj
            (S.standardFormUniversalLeftMiddleCostarEquiv_target_base
              x₀ W t)) ≫ c t := by
  classical
  unfold standardFormUniversalRealizedOutgoingSource
    standardFormUniversalLeftOutgoingMiddleDesc
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact biproduct.lift_desc

set_option backward.isDefEq.respectTransparency false in
/-- At an injective source, a relation among the chosen outgoing summands
has every coefficient zero. -/
theorem standardFormUniversal_injective_outgoing_exact
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : Injective (S.fgObj W.1))
    (c : ∀ t : (S.minimalLeftAlmostSplitAt W.1).index,
      S.fgObj ((S.minimalLeftAlmostSplitAt W.1).label t) ⟶ S.fgObj X)
    (hc : (∑ t, S.standardFormUniversalMappedOutgoingHom x₀ W
        (S.standardFormUniversalLeftMiddleCostarEquiv x₀ W t) ≫
      eqToHom (congrArg S.fgObj
        (S.standardFormUniversalLeftMiddleCostarEquiv_target_base x₀ W t)) ≫
      c t) = 0) :
    ∀ t, c t = 0 := by
  let q := S.standardFormUniversalLeftOutgoingMiddleDesc x₀ X W c
  let source := S.standardFormUniversalRealizedOutgoingSource x₀ W
  letI : Injective (S.fgObj W.1) := hW
  have hsourceEpi : Epi source :=
    MagnitudeConjecture.CategoryTheory.leftAlmostSplit_epi_of_injective_source
      source
      (S.standardFormUniversalRealizedOutgoingSource_isLeftAlmostSplit x₀ W)
      (S.standardFormUniversalRealizedOutgoingSource_isLeftMinimal x₀ W)
  letI : Epi source := hsourceEpi
  have hq : source ≫ q = 0 := by
    dsimp only [source, q]
    rw [S.standardFormUniversalRealizedOutgoingSource_comp_leftOutgoingMiddleDesc,
      hc]
  have hqzero : q = 0 := by
    apply (cancel_epi source).1
    simpa using hq
  intro t
  rw [← S.standardFormUniversalLeftOutgoingMiddleDesc_component x₀ X W c t]
  dsimp only [q] at hqzero
  rw [hqzero]
  simp only [comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- At an injective lifted source, a vanishing outgoing costar sum has all
coefficients zero. -/
theorem standardFormUniversal_injective_outgoingCostar_exact
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : Injective (S.fgObj W.1))
    (c : ∀ d : Quiver.Costar W, S.fgObj d.1.1 ⟶ S.fgObj X)
    (hc : (∑ d, S.standardFormUniversalMappedOutgoingHom x₀ W d ≫ c d) = 0) :
    ∀ d, c d = 0 := by
  classical
  let e := S.standardFormUniversalLeftMiddleCostarEquiv x₀ W
  let c' : ∀ t : (S.minimalLeftAlmostSplitAt W.1).index,
      S.fgObj ((S.minimalLeftAlmostSplitAt W.1).label t) ⟶ S.fgObj X :=
    fun t ↦ eqToHom (congrArg S.fgObj
      (S.standardFormUniversalLeftMiddleCostarEquiv_target_base x₀ W t).symm) ≫
        c (e t)
  let f : Quiver.Costar W → (S.fgObj W.1 ⟶ S.fgObj X) :=
    fun d ↦ S.standardFormUniversalMappedOutgoingHom x₀ W d ≫ c d
  have hc' : (∑ t, S.standardFormUniversalMappedOutgoingHom x₀ W (e t) ≫
      eqToHom (congrArg S.fgObj
        (S.standardFormUniversalLeftMiddleCostarEquiv_target_base x₀ W t)) ≫
      c' t) = 0 := by
    calc
      (∑ t, S.standardFormUniversalMappedOutgoingHom x₀ W (e t) ≫
          eqToHom (congrArg S.fgObj
            (S.standardFormUniversalLeftMiddleCostarEquiv_target_base
              x₀ W t)) ≫ c' t) = ∑ t, f (e t) := by
        apply Finset.sum_congr rfl
        intro t _
        simp [c', f, Category.assoc]
      _ = ∑ d, f d := e.sum_comp _
      _ = 0 := hc
  have hzero := S.standardFormUniversal_injective_outgoing_exact
    x₀ X W hW c' hc'
  intro d
  obtain ⟨t, ht⟩ := e.surjective d
  subst d
  have hz := congrArg
    (fun q ↦ eqToHom (congrArg S.fgObj
      (S.standardFormUniversalLeftMiddleCostarEquiv_target_base x₀ W t)) ≫ q)
    (hzero t)
  simpa [c', Category.assoc] using hz

set_option backward.isDefEq.respectTransparency false in
/-- A scalar identity cannot cancel a sum through the normalized outgoing
costar arrows. -/
theorem standardFormUniversal_scalar_eq_zero_of_add_outgoingCostar_eq_zero
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (r : k)
    (c : ∀ d : Quiver.Costar W, S.fgObj d.1.1 ⟶ S.fgObj W.1)
    (hc : r • 𝟙 (S.fgObj W.1) +
      (∑ d, S.standardFormUniversalMappedOutgoingHom x₀ W d ≫ c d) = 0) :
    r = 0 := by
  let s : S.fgObj W.1 ⟶ S.fgObj W.1 :=
    ∑ d, S.standardFormUniversalMappedOutgoingHom x₀ W d ≫ c d
  have hs : s ∈ S.fgNilpotentRadicalData.ideal.hom
      (S.fgObj W.1) (S.fgObj W.1) := by
    dsimp only [s]
    apply (S.fgNilpotentRadicalData.ideal.hom _ _).sum_mem
    intro d _
    exact S.fgNilpotentRadicalData.ideal.postcomp (c d)
      (S.standardFormUniversalNormalizedOutgoingArrow_mem_radical x₀ W d)
  have hscalar : r • 𝟙 (S.fgObj W.1) ∈
      S.fgNilpotentRadicalData.ideal.hom
        (S.fgObj W.1) (S.fgObj W.1) := by
    have heq : r • 𝟙 (S.fgObj W.1) = -s := by
      calc
        r • 𝟙 (S.fgObj W.1) =
            (r • 𝟙 (S.fgObj W.1) + s) - s := by abel
        _ = -s := by rw [hc]; simp
    rw [heq]
    exact (S.fgNilpotentRadicalData.ideal.hom _ _).neg_mem hs
  have hrad : IsRadicalMorphism (r • 𝟙 (S.fgObj W.1)) :=
    (S.fgNilpotentRadicalData.mem_ideal_iff _).1 hscalar
  have hnot : ¬ IsSplitEpi (r • 𝟙 (S.fgObj W.1)) :=
    (S.finiteTauCategoryData.isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (r • 𝟙 (S.fgObj W.1))).1 hrad
  by_contra hr
  exact hnot (MagnitudeConjecture.isSplitEpi_smul_id_of_ne_zero
    (k := k) (S.fgObj W.1) hr)

set_option backward.isDefEq.respectTransparency false in
/-- At a projective lifted endpoint, a vanishing incoming-arrow sum has all
displayed coefficients zero. -/
theorem standardFormUniversal_projective_incoming_exact
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : W ∈ MeshCategory.RightMeshData.UniversalCover.projectiveSet
      S.standardFormRightMeshData x₀)
    (c : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
      S.fgObj X ⟶ S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i))
    (hc : (∑ i, c i ≫
      S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalMiddleArrow x₀ W i)) = 0) :
    ∀ i, c i = 0 := by
  let q := S.standardFormUniversalIncomingMiddleLift x₀ X W c
  let sink := S.standardFormUniversalRealizedSink x₀
    (S.standardFormUniversalNormalizedArrowMap x₀) W
  haveI : Projective (S.fgObj W.1) := by
    change W.1 ∈ S.standardFormProjectiveSet
    exact hW
  haveI : Mono sink :=
    MagnitudeConjecture.CategoryTheory.rightAlmostSplit_mono_of_projective_target
      sink
      (S.standardFormUniversalNormalizedRealizedSink_isRightAlmostSplit x₀ W)
      (S.standardFormUniversalNormalizedRealizedSink_isRightMinimal x₀ W)
  have hq : q ≫ sink = 0 := by
    dsimp only [q, sink]
    rw [S.standardFormUniversalIncomingMiddleLift_comp_sink, hc]
  have hqzero : q = 0 := by
    apply (cancel_mono sink).1
    simpa using hq
  intro i
  rw [← S.standardFormUniversalIncomingMiddleLift_projection x₀ X W c i]
  dsimp only [q] at hqzero
  rw [hqzero, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Projective incoming exactness in the star coordinates produced directly
by raw final-arrow decomposition. -/
theorem standardFormUniversal_projective_incomingStar_exact
    (x₀ X : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : W ∈ MeshCategory.RightMeshData.UniversalCover.projectiveSet
      S.standardFormRightMeshData x₀)
    (c : ∀ d : Quiver.Star W, S.fgObj X ⟶ S.fgObj d.1.1)
    (hc : (∑ d, c d ≫
      S.standardFormUniversalMappedIncomingHom x₀ W d) = 0) :
    ∀ d, c d = 0 := by
  classical
  let e := S.standardFormUniversalMiddleStarEquiv x₀ W
  let c' : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
      S.fgObj X ⟶ S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i) :=
    fun i ↦ c
      (⟨S.standardFormUniversalMiddleVertex x₀ W i,
        S.standardFormUniversalMiddleArrow x₀ W i⟩ : Quiver.Star W)
  let f : Quiver.Star W → (S.fgObj X ⟶ S.fgObj W.1) :=
    fun d ↦ c d ≫ S.standardFormUniversalMappedIncomingHom x₀ W d
  have hc' : (∑ i, c' i ≫
      S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalMiddleArrow x₀ W i)) = 0 := by
    calc
      (∑ i, c' i ≫ S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalMiddleArrow x₀ W i)) =
          ∑ i, f
            (⟨S.standardFormUniversalMiddleVertex x₀ W i,
              S.standardFormUniversalMiddleArrow x₀ W i⟩ :
                Quiver.Star W) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [c', f,
          S.standardFormUniversalMappedIncomingHom_eq_normalized]
      _ = ∑ i, f (e i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg f
          (S.standardFormUniversalMiddleStarEquiv_apply x₀ W i).symm
      _ = ∑ d, f d :=
        e.sum_comp _
      _ = 0 := hc
  have hzero := S.standardFormUniversal_projective_incoming_exact
    x₀ X W hW c' hc'
  intro d
  obtain ⟨i, hi⟩ := e.surjective d
  subst d
  rw [S.standardFormUniversalMiddleStarEquiv_apply]
  exact hzero i

set_option backward.isDefEq.respectTransparency false in
/-- At a nonprojective lifted endpoint, a vanishing incoming-arrow sum is
the image of the paired mesh-source family. -/
theorem standardFormUniversal_nonprojective_incoming_exact
    (x₀ X : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (c : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1),
      S.fgObj X ⟶ S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1 i))
    (hc : (∑ i, c i ≫
      S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalMiddleArrow x₀ W.1 i)) = 0) :
    ∃ t : S.fgObj X ⟶ S.fgObj
        (S.standardFormTau
          (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
            S.standardFormRightMeshData x₀ W)),
      ∀ i, c i = t ≫
        S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalPairedMiddleArrow x₀ W i) := by
  let q := S.standardFormUniversalIncomingMiddleLift x₀ X W.1 c
  have hq : q ≫ S.standardFormUniversalRealizedSink x₀
      (S.standardFormUniversalNormalizedArrowMap x₀) W.1 = 0 := by
    dsimp only [q]
    rw [S.standardFormUniversalIncomingMiddleLift_comp_sink, hc]
  obtain ⟨t, ht⟩ :=
    S.standardFormUniversalNormalizedRealizedSource_factors_of_comp_sink_eq_zero
      x₀ W q hq
  refine ⟨t, fun i ↦ ?_⟩
  calc
    c i = q ≫ FiniteTauMatrix.rightMiddleProjection
        S.finiteTauCategoryData W.1.1 i :=
      (S.standardFormUniversalIncomingMiddleLift_projection
        x₀ X W.1 c i).symm
    _ = (t ≫ S.standardFormUniversalRealizedSource x₀
          (S.standardFormUniversalNormalizedArrowMap x₀) W) ≫
        FiniteTauMatrix.rightMiddleProjection
          S.finiteTauCategoryData W.1.1 i := by rw [ht]
    _ = t ≫ S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalPairedMiddleArrow x₀ W i) := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Nonprojective incoming exactness in the star coordinates produced
directly by raw final-arrow decomposition. -/
theorem standardFormUniversal_nonprojective_incomingStar_exact
    (x₀ X : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (c : ∀ d : Quiver.Star W.1, S.fgObj X ⟶ S.fgObj d.1.1)
    (hc : (∑ d, c d ≫
      S.standardFormUniversalMappedIncomingHom x₀ W.1 d) = 0) :
    ∃ t : S.fgObj X ⟶ S.fgObj
        (S.standardFormTau
          (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
            S.standardFormRightMeshData x₀ W)),
      ∀ d, c d = t ≫
        S.standardFormUniversalMappedPairedIncomingHom x₀ W d := by
  classical
  let e := S.standardFormUniversalMiddleStarEquiv x₀ W.1
  let c' : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1),
      S.fgObj X ⟶ S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1 i) :=
    fun i ↦ c
      (⟨S.standardFormUniversalMiddleVertex x₀ W.1 i,
        S.standardFormUniversalMiddleArrow x₀ W.1 i⟩ : Quiver.Star W.1)
  let f : Quiver.Star W.1 → (S.fgObj X ⟶ S.fgObj W.1.1) :=
    fun d ↦ c d ≫ S.standardFormUniversalMappedIncomingHom x₀ W.1 d
  have hc' : (∑ i, c' i ≫
      S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalMiddleArrow x₀ W.1 i)) = 0 := by
    calc
      (∑ i, c' i ≫ S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalMiddleArrow x₀ W.1 i)) =
          ∑ i, f
            (⟨S.standardFormUniversalMiddleVertex x₀ W.1 i,
              S.standardFormUniversalMiddleArrow x₀ W.1 i⟩ :
                Quiver.Star W.1) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [c', f,
          S.standardFormUniversalMappedIncomingHom_eq_normalized]
      _ = ∑ i, f (e i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg f
          (S.standardFormUniversalMiddleStarEquiv_apply x₀ W.1 i).symm
      _ = ∑ d, f d := e.sum_comp _
      _ = 0 := hc
  obtain ⟨t, ht⟩ := S.standardFormUniversal_nonprojective_incoming_exact
    x₀ X W c' hc'
  refine ⟨t, fun d ↦ ?_⟩
  obtain ⟨i, hi⟩ := e.surjective d
  subst d
  rw [S.standardFormUniversalMiddleStarEquiv_apply]
  calc
    c (⟨S.standardFormUniversalMiddleVertex x₀ W.1 i,
        S.standardFormUniversalMiddleArrow x₀ W.1 i⟩ : Quiver.Star W.1) =
        c' i := rfl
    _ = t ≫ S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalPairedMiddleArrow x₀ W i) := ht i
    _ = t ≫ S.standardFormUniversalMappedPairedIncomingHom x₀ W
        (⟨S.standardFormUniversalMiddleVertex x₀ W.1 i,
          S.standardFormUniversalMiddleArrow x₀ W.1 i⟩ : Quiver.Star W.1) := by
      rw [S.standardFormUniversalMappedPairedIncomingHom_eq_normalized]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- A scalar identity cannot cancel a sum through the normalized incoming
irreducible arrows. -/
theorem standardFormUniversal_scalar_eq_zero_of_add_incoming_eq_zero
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (r : k)
    (c : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
      S.fgObj W.1 ⟶ S.fgObj (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i))
    (hc : r • 𝟙 (S.fgObj W.1) +
      (∑ i, c i ≫ S.standardFormUniversalMappedMiddleHom x₀ W i) = 0) :
    r = 0 := by
  let s : S.fgObj W.1 ⟶ S.fgObj W.1 :=
    ∑ i, c i ≫ S.standardFormUniversalMappedMiddleHom x₀ W i
  have hs : s ∈ S.fgNilpotentRadicalData.ideal.hom
      (S.fgObj W.1) (S.fgObj W.1) := by
    dsimp only [s]
    apply (S.fgNilpotentRadicalData.ideal.hom _ _).sum_mem
    intro i _
    apply S.fgNilpotentRadicalData.ideal.precomp (c i)
    rw [S.standardFormUniversalMappedMiddleHom_eq_normalized]
    exact S.standardFormUniversalNormalizedMiddleArrow_mem_radical x₀ W i
  have hscalar : r • 𝟙 (S.fgObj W.1) ∈
      S.fgNilpotentRadicalData.ideal.hom
        (S.fgObj W.1) (S.fgObj W.1) := by
    have heq : r • 𝟙 (S.fgObj W.1) = -s := by
      calc
        r • 𝟙 (S.fgObj W.1) =
            (r • 𝟙 (S.fgObj W.1) + s) - s := by abel
        _ = -s := by rw [hc]; simp
    rw [heq]
    exact (S.fgNilpotentRadicalData.ideal.hom _ _).neg_mem hs
  have hrad : IsRadicalMorphism (r • 𝟙 (S.fgObj W.1)) :=
    (S.fgNilpotentRadicalData.mem_ideal_iff _).1 hscalar
  have hnot : ¬ IsSplitEpi (r • 𝟙 (S.fgObj W.1)) :=
    (S.finiteTauCategoryData.isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (r • 𝟙 (S.fgObj W.1))).1 hrad
  by_contra hr
  exact hnot (MagnitudeConjecture.isSplitEpi_smul_id_of_ne_zero
    (k := k) (S.fgObj W.1) hr)

set_option backward.isDefEq.respectTransparency false in
/-- Star-indexed scalar separation, in the coordinates produced directly by
the raw final-arrow decomposition. -/
theorem standardFormUniversal_scalar_eq_zero_of_add_incomingStar_eq_zero
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (r : k)
    (c : ∀ d : Quiver.Star W, S.fgObj W.1 ⟶ S.fgObj d.1.1)
    (hc : r • 𝟙 (S.fgObj W.1) +
      (∑ d, c d ≫ S.standardFormUniversalMappedIncomingHom x₀ W d) = 0) :
    r = 0 := by
  let s : S.fgObj W.1 ⟶ S.fgObj W.1 :=
    ∑ d, c d ≫ S.standardFormUniversalMappedIncomingHom x₀ W d
  have hs : s ∈ S.fgNilpotentRadicalData.ideal.hom
      (S.fgObj W.1) (S.fgObj W.1) := by
    dsimp only [s]
    apply (S.fgNilpotentRadicalData.ideal.hom _ _).sum_mem
    intro d _
    apply S.fgNilpotentRadicalData.ideal.precomp (c d)
    rw [S.standardFormUniversalMappedIncomingHom_eq_normalized]
    exact S.standardFormUniversalNormalizedIncomingArrow_mem_radical x₀ W d
  have hscalar : r • 𝟙 (S.fgObj W.1) ∈
      S.fgNilpotentRadicalData.ideal.hom
        (S.fgObj W.1) (S.fgObj W.1) := by
    have heq : r • 𝟙 (S.fgObj W.1) = -s := by
      calc
        r • 𝟙 (S.fgObj W.1) =
            (r • 𝟙 (S.fgObj W.1) + s) - s := by abel
        _ = -s := by rw [hc]; simp
    rw [heq]
    exact (S.fgNilpotentRadicalData.ideal.hom _ _).neg_mem hs
  have hrad : IsRadicalMorphism (r • 𝟙 (S.fgObj W.1)) :=
    (S.fgNilpotentRadicalData.mem_ideal_iff _).1 hscalar
  have hnot : ¬ IsSplitEpi (r • 𝟙 (S.fgObj W.1)) :=
    (S.finiteTauCategoryData.isRadicalMorphism_iff_not_isSplitEpi_to_obj
      (r • 𝟙 (S.fgObj W.1))).1 hrad
  by_contra hr
  exact hnot (MagnitudeConjecture.isSplitEpi_smul_id_of_ne_zero
    (k := k) (S.fgObj W.1) hr)

set_option backward.isDefEq.respectTransparency false in
/-- One radical-layer step for an endomorphism: remove its scalar residue,
then factor the radical remainder through the lifted right almost-split
sink. -/
theorem standardFormUniversal_endomorphism_eq_scalar_add_arrow_sum
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (f : S.fgObj W.1 ⟶ S.fgObj W.1) :
    ∃ (r : k)
      (g : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
        S.fgObj W.1 ⟶
          S.fgObj (FiniteTauMatrix.rightMiddleLabel
            S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i)),
      f = r • 𝟙 (S.fgObj W.1) +
        (∑ i, g i ≫
          (S.standardFormUniversalNormalizedArrowMap x₀
            (S.standardFormUniversalMiddleArrow x₀ W i) :
              S.fgObj (FiniteTauMatrix.rightMiddleLabel
                S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i) ⟶
                S.fgObj W.1) : S.fgObj W.1 ⟶ S.fgObj W.1) := by
  let r := FiniteTauMatrix.algebraicallyClosedResidueMap
    (k := k) S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 f
  have hnot : ¬ IsSplitEpi (f - r • 𝟙 (S.fgObj W.1)) :=
    S.standardFormResidueRemainder_not_isSplitEpi W.1 f
  obtain ⟨h, hh⟩ :=
    (S.standardFormUniversalNormalizedRealizedSink_isRightAlmostSplit x₀ W)
      |>.factors (f - r • 𝟙 (S.fgObj W.1)) hnot
  refine ⟨r, fun i ↦ h ≫ FiniteTauMatrix.rightMiddleProjection
    S.finiteTauCategoryData W.1 i, ?_⟩
  rw [← S.standardFormUniversal_factor_realizedSink_eq_sum x₀ W.1 W h,
    hh]
  abel

set_option backward.isDefEq.respectTransparency false in
/-- One radical-layer step between differently labelled indecomposables:
the morphism itself factors through the lifted right almost-split sink. -/
theorem standardFormUniversal_morphism_eq_arrow_sum_of_ne
    (x₀ : Fin S.n)
    {X : Fin S.n}
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hXW : X ≠ W.1)
    (f : S.fgObj X ⟶ S.fgObj W.1) :
    ∃ g : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
      S.fgObj X ⟶
        S.fgObj (FiniteTauMatrix.rightMiddleLabel
          S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i),
      f = ∑ i, g i ≫ S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalMiddleArrow x₀ W i) := by
  have hnot : ¬ IsSplitEpi f := S.not_isSplitEpi_fgObj_of_ne hXW f
  obtain ⟨h, hh⟩ :=
    (S.standardFormUniversalNormalizedRealizedSink_isRightAlmostSplit x₀ W)
      |>.factors f hnot
  refine ⟨fun i ↦ h ≫ FiniteTauMatrix.rightMiddleProjection
    S.finiteTauCategoryData W.1 i, ?_⟩
  rw [← S.standardFormUniversal_factor_realizedSink_eq_sum x₀ X W h]
  exact hh.symm

set_option backward.isDefEq.respectTransparency false in
/-- The Riedtmann one-step decomposition, already bundling the scalar
identity term as a source-fibre contribution of the mesh functor. -/
theorem standardFormUniversal_oneStep_sourceFiber
    (x₀ : Fin S.n)
    (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (f : S.fgObj X ⟶ S.fgObj W.1) :
    ∃ (a : DirectSum
        (LinearCovering.Fiber
          (S.standardFormUniversalIndecMeshFunctor x₀) X)
        (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ W))
      (g : ∀ i : Fin (FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1),
        S.fgObj X ⟶
          S.fgObj (FiniteTauMatrix.rightMiddleLabel
            S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i)),
      (InducedCategory.homMk f : X ⟶
          (S.standardFormUniversalIndecMeshFunctor x₀).obj
            (S.standardFormUniversalMeshObj x₀ W)) =
        LinearCovering.sourceFiberHomMap (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          (S.standardFormUniversalMeshObj x₀ W) a +
        (InducedCategory.homMk
          (∑ i, g i ≫
            (S.standardFormUniversalNormalizedArrowMap x₀
              (S.standardFormUniversalMiddleArrow x₀ W i) :
                S.fgObj (FiniteTauMatrix.rightMiddleLabel
                  S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i) ⟶
                  S.fgObj W.1) : S.fgObj X ⟶ S.fgObj W.1) : X ⟶
            (S.standardFormUniversalIndecMeshFunctor x₀).obj
              (S.standardFormUniversalMeshObj x₀ W)) := by
  classical
  by_cases hXW : X = W.1
  · subst X
    obtain ⟨r, g, hfg⟩ :=
      S.standardFormUniversal_endomorphism_eq_scalar_add_arrow_sum x₀ W f
    let Z : LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) W.1 :=
      ⟨S.standardFormUniversalMeshObj x₀ W, rfl⟩
    let a := LinearCovering.sourceFiberLof (k := k)
      (S.standardFormUniversalIndecMeshFunctor x₀) W.1
      (S.standardFormUniversalMeshObj x₀ W) Z
      (r • 𝟙 (S.standardFormUniversalMeshObj x₀ W))
    refine ⟨a, g, ?_⟩
    have ha :
        LinearCovering.sourceFiberHomMap (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) W.1
          (S.standardFormUniversalMeshObj x₀ W) a =
            r • 𝟙 ((S.standardFormUniversalIndecMeshFunctor x₀).obj
              (S.standardFormUniversalMeshObj x₀ W)) := by
      dsimp only [a]
      rw [LinearCovering.sourceFiberHomMap_lof]
      simp [Z]
    rw [ha]
    apply InducedCategory.hom_ext
    change f = r • 𝟙 (S.fgObj W.1) +
      (∑ i, g i ≫
        (S.standardFormUniversalNormalizedArrowMap x₀
          (S.standardFormUniversalMiddleArrow x₀ W i) :
            S.fgObj (FiniteTauMatrix.rightMiddleLabel
              S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i) ⟶
              S.fgObj W.1) : S.fgObj W.1 ⟶ S.fgObj W.1)
    exact hfg
  · obtain ⟨g, hfg⟩ :=
      S.standardFormUniversal_morphism_eq_arrow_sum_of_ne x₀ W hXW f
    refine ⟨0, g, ?_⟩
    rw [map_zero, zero_add]
    apply InducedCategory.hom_ext
    change f = ∑ i, g i ≫
      (S.standardFormUniversalNormalizedArrowMap x₀
        (S.standardFormUniversalMiddleArrow x₀ W i) :
          S.fgObj (FiniteTauMatrix.rightMiddleLabel
            S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i) ⟶
            S.fgObj W.1)
    exact hfg

set_option backward.isDefEq.respectTransparency false in
/-- Riedtmann's fixed-target approximation: modulo the `n`-th radical
power, every module morphism is the image of a finite source-fibre sum of
raw mesh morphisms. -/
theorem standardFormUniversal_exists_sourceFiber_mod_radicalPower
    (x₀ : Fin S.n)
    (X : S.FGIndecCategory) :
    ∀ (n : ℕ)
      (W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀)
      (f : S.fgObj X ⟶ S.fgObj W.1),
      ∃ a : DirectSum
          (LinearCovering.Fiber
            (S.standardFormUniversalIndecMeshFunctor x₀) X)
          (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ W),
        ((InducedCategory.homMk f : X ⟶
              (S.standardFormUniversalIndecMeshFunctor x₀).obj
                (S.standardFormUniversalMeshObj x₀ W)) -
            LinearCovering.sourceFiberHomMap (k := k)
              (S.standardFormUniversalIndecMeshFunctor x₀) X
              (S.standardFormUniversalMeshObj x₀ W) a).hom ∈
          (S.fgNilpotentRadicalData.ideal.pow n).hom
            (S.fgObj X) (S.fgObj W.1) := by
  classical
  intro n
  induction n with
  | zero =>
      intro W f
      refine ⟨0, ?_⟩
      rw [map_zero]
      change _ ∈ (⊤ : CategoricalIdeal.HomIdeal
        (RightModule.FinitelyGeneratedCategory A)).hom
          (S.fgObj X) (S.fgObj W.1)
      simp
  | succ n ih =>
      intro W f
      obtain ⟨a₀, g, hfg⟩ :=
        S.standardFormUniversal_oneStep_sourceFiber x₀ X W f
      choose a ha using fun i ↦ ih
        (S.standardFormUniversalMiddleVertex x₀ W i) (g i)
      let b := fun i ↦ LinearCovering.sourceFiberPostcomp (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X
        (S.standardFormUniversalMiddleHom x₀ W i) (a i)
      let total := a₀ + ∑ i, b i
      refine ⟨total, ?_⟩
      have hmap :
          LinearCovering.sourceFiberHomMap (k := k)
              (S.standardFormUniversalIndecMeshFunctor x₀) X
              (S.standardFormUniversalMeshObj x₀ W) total =
            LinearCovering.sourceFiberHomMap (k := k)
                (S.standardFormUniversalIndecMeshFunctor x₀) X
                (S.standardFormUniversalMeshObj x₀ W) a₀ +
              ∑ i,
                LinearCovering.sourceFiberHomMap (k := k)
                    (S.standardFormUniversalIndecMeshFunctor x₀) X
                    (S.standardFormUniversalMeshObj x₀
                      (S.standardFormUniversalMiddleVertex x₀ W i)) (a i) ≫
                  (S.standardFormUniversalIndecMeshFunctor x₀).map
                    (S.standardFormUniversalMiddleHom x₀ W i) := by
        dsimp only [total, b]
        rw [map_add, map_sum]
        apply congrArg₂ (.+.) rfl
        apply Finset.sum_congr rfl
        intro i _
        exact LinearCovering.sourceFiberHomMap_sourceFiberPostcomp
          (k := k) (S.standardFormUniversalIndecMeshFunctor x₀) X
          (S.standardFormUniversalMiddleHom x₀ W i) (a i)
      have hsum :
          (InducedCategory.homMk
            (∑ i, g i ≫
              (S.standardFormUniversalNormalizedArrowMap x₀
                (S.standardFormUniversalMiddleArrow x₀ W i) :
                  S.fgObj (FiniteTauMatrix.rightMiddleLabel
                    S.finiteTauCategoryData.toFiniteRightTauCategoryData
                      W.1 i) ⟶ S.fgObj W.1)) :
              X ⟶ (S.standardFormUniversalIndecMeshFunctor x₀).obj
                (S.standardFormUniversalMeshObj x₀ W)) =
            ∑ i, (InducedCategory.homMk (g i) : X ⟶
                (S.standardFormUniversalIndecMeshFunctor x₀).obj
                  (S.standardFormUniversalMeshObj x₀
                    (S.standardFormUniversalMiddleVertex x₀ W i))) ≫
              (S.standardFormUniversalIndecMeshFunctor x₀).map
                (S.standardFormUniversalMiddleHom x₀ W i) := by
        apply (InducedCategory.homLinearEquiv (R := k)).injective
        simp only [InducedCategory.homLinearEquiv_apply,
          InducedCategory.homMk_hom, map_sum, InducedCategory.comp_hom,
          S.standardFormUniversalIndecMeshFunctor_map_middleHom]
      have herr :
          (InducedCategory.homMk f : X ⟶
              (S.standardFormUniversalIndecMeshFunctor x₀).obj
                (S.standardFormUniversalMeshObj x₀ W)) -
              LinearCovering.sourceFiberHomMap (k := k)
                (S.standardFormUniversalIndecMeshFunctor x₀) X
                (S.standardFormUniversalMeshObj x₀ W) total =
            ∑ i,
              ((InducedCategory.homMk (g i) : X ⟶
                    (S.standardFormUniversalIndecMeshFunctor x₀).obj
                      (S.standardFormUniversalMeshObj x₀
                        (S.standardFormUniversalMiddleVertex x₀ W i))) -
                  LinearCovering.sourceFiberHomMap (k := k)
                    (S.standardFormUniversalIndecMeshFunctor x₀) X
                    (S.standardFormUniversalMeshObj x₀
                      (S.standardFormUniversalMiddleVertex x₀ W i)) (a i)) ≫
                (S.standardFormUniversalIndecMeshFunctor x₀).map
                  (S.standardFormUniversalMiddleHom x₀ W i) := by
        rw [hfg, hsum, hmap]
        simp_rw [Preadditive.sub_comp]
        rw [Finset.sum_sub_distrib]
        abel
      rw [herr]
      rw [← InducedCategory.homLinearEquiv_apply (R := k), map_sum]
      rw [CategoricalIdeal.HomIdeal.pow_succ]
      apply ((S.fgNilpotentRadicalData.ideal.pow n ⋆ᵢ
        S.fgNilpotentRadicalData.ideal).hom
          (S.fgObj X) (S.fgObj W.1)).sum_mem
      intro i _
      rw [InducedCategory.homLinearEquiv_apply,
        InducedCategory.comp_hom,
        S.standardFormUniversalIndecMeshFunctor_map_middleHom]
      exact CategoricalIdeal.HomIdeal.comp_mem_mul (ha i)
        (S.standardFormUniversalNormalizedMiddleArrow_mem_radical x₀ W i)

set_option backward.isDefEq.respectTransparency false in
/-- Nilpotence terminates the radical-layer approximation, giving exact
surjectivity of the fixed-target source-fibre map at every represented
universal-cover vertex. -/
theorem standardFormUniversal_sourceFiberHomMap_surjective_meshObj
    (x₀ : Fin S.n)
    (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    Function.Surjective
      (LinearCovering.sourceFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X
        (S.standardFormUniversalMeshObj x₀ W)) := by
  intro f
  obtain ⟨N, hN⟩ := S.fgNilpotentRadicalData.nilpotent
  obtain ⟨a, ha⟩ :=
    S.standardFormUniversal_exists_sourceFiber_mod_radicalPower
      x₀ X N W f.hom
  rw [hN] at ha
  have hzero :
      (InducedCategory.homMk f.hom : X ⟶
          (S.standardFormUniversalIndecMeshFunctor x₀).obj
            (S.standardFormUniversalMeshObj x₀ W)) -
        LinearCovering.sourceFiberHomMap (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          (S.standardFormUniversalMeshObj x₀ W) a = 0 := by
    apply InducedCategory.hom_ext
    exact ha
  refine ⟨a, ?_⟩
  have heq := sub_eq_zero.mp hzero
  exact heq.symm.trans (InducedCategory.hom_ext rfl).symm

set_option backward.isDefEq.respectTransparency false in
/-- One exact Riedtmann peeling step in a fixed-target source fibre.  A
family in the kernel is a sum through the arrows entering the target, and
the coefficient family can be chosen in the kernel at every preceding
target.  In the nonprojective case this is achieved by lifting the common
mesh-source factor and subtracting the resulting mesh relation. -/
theorem standardFormUniversal_sourceFiber_kernel_peel
    (x₀ : Fin S.n)
    (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ W))
    (ha : LinearCovering.sourceFiberHomMap (k := k)
      (S.standardFormUniversalIndecMeshFunctor x₀) X
      (S.standardFormUniversalMeshObj x₀ W) a = 0) :
    ∃ b : ∀ d : Quiver.Star W,
        DirectSum
          (LinearCovering.Fiber
            (S.standardFormUniversalIndecMeshFunctor x₀) X)
          (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ d.1),
      (∀ d, LinearCovering.sourceFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X
        (S.standardFormUniversalMeshObj x₀ d.1) (b d) = 0) ∧
      a = ∑ d : Quiver.Star W,
        LinearCovering.sourceFiberPostcomp (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData x₀).incomingArrowHom (k := k) d)
          (b d) := by
  classical
  let F := S.standardFormUniversalIndecMeshFunctor x₀
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  obtain ⟨r, b, hb⟩ :=
    S.standardFormUniversal_exists_sourceFiber_eq_diagonal_add_incoming
      x₀ X W a
  let c : ∀ d : Quiver.Star W, S.fgObj X ⟶ S.fgObj d.1.1 :=
    fun d ↦ (LinearCovering.sourceFiberHomMap (k := k) F X
      (S.standardFormUniversalMeshObj x₀ d.1) (b d)).hom
  have hdown :
      LinearCovering.sourceFiberHomMap (k := k) F X
          (S.standardFormUniversalMeshObj x₀ W)
          (S.standardFormUniversalSourceFiberDiagonal x₀ X W r) +
        ∑ d : Quiver.Star W,
          LinearCovering.sourceFiberHomMap (k := k) F X
              (S.standardFormUniversalMeshObj x₀ d.1) (b d) ≫
            F.map (T.incomingArrowHom (k := k) d) = 0 := by
    calc
      LinearCovering.sourceFiberHomMap (k := k) F X
            (S.standardFormUniversalMeshObj x₀ W)
            (S.standardFormUniversalSourceFiberDiagonal x₀ X W r) +
          ∑ d : Quiver.Star W,
            LinearCovering.sourceFiberHomMap (k := k) F X
                (S.standardFormUniversalMeshObj x₀ d.1) (b d) ≫
              F.map (T.incomingArrowHom (k := k) d) =
          LinearCovering.sourceFiberHomMap (k := k) F X
            (S.standardFormUniversalMeshObj x₀ W)
            (S.standardFormUniversalSourceFiberDiagonal x₀ X W r +
              ∑ d : Quiver.Star W,
                LinearCovering.sourceFiberPostcomp (k := k) F X
                  (T.incomingArrowHom (k := k) d) (b d)) := by
        rw [map_add, map_sum]
        apply congrArg₂ (.+.) rfl
        apply Finset.sum_congr rfl
        intro d _
        exact (LinearCovering.sourceFiberHomMap_sourceFiberPostcomp
          (k := k) F X (T.incomingArrowHom (k := k) d) (b d)).symm
      _ = LinearCovering.sourceFiberHomMap (k := k) F X
          (S.standardFormUniversalMeshObj x₀ W) a := by rw [← hb]
      _ = 0 := ha
  let diagonalHom : S.fgObj X ⟶ S.fgObj W.1 :=
    (LinearCovering.sourceFiberHomMap (k := k) F X
      (S.standardFormUniversalMeshObj x₀ W)
      (S.standardFormUniversalSourceFiberDiagonal x₀ X W r)).hom
  let incomingTerm : Quiver.Star W → (S.fgObj X ⟶ S.fgObj W.1) :=
    fun d ↦ (LinearCovering.sourceFiberHomMap (k := k) F X
        (S.standardFormUniversalMeshObj x₀ d.1) (b d) ≫
      F.map (T.incomingArrowHom (k := k) d)).hom
  have hdownTerms : diagonalHom +
      ∑ d : Quiver.Star W, incomingTerm d = 0 := by
    have h := congrArg (InducedCategory.homLinearEquiv (R := k)) hdown
    simp only [map_add, map_sum, map_zero,
      InducedCategory.homLinearEquiv_apply] at h
    simpa only [diagonalHom, incomingTerm, F,
      S.standardFormUniversalIndecMeshFunctor_obj_meshObj] using h
  have hdownHom :
      diagonalHom +
        ∑ d : Quiver.Star W,
          c d ≫ S.standardFormUniversalMappedIncomingHom x₀ W d = 0 := by
    calc
      diagonalHom + ∑ d : Quiver.Star W,
          c d ≫ S.standardFormUniversalMappedIncomingHom x₀ W d =
          diagonalHom + ∑ d : Quiver.Star W, incomingTerm d := by
        apply congrArg₂ (.+.) rfl
        apply Finset.sum_congr rfl
        intro d _
        dsimp only [incomingTerm, c,
          standardFormUniversalMappedIncomingHom]
        rw [InducedCategory.comp_hom]
      _ = 0 := hdownTerms
  have hdiag : S.standardFormUniversalSourceFiberDiagonal x₀ X W r = 0 := by
    by_cases hXW : X = W.1
    · subst X
      have hscalar := hdownHom
      dsimp only [diagonalHom] at hscalar
      rw [S.standardFormUniversal_sourceFiberHomMap_diagonal_self] at hscalar
      have hid :
          (r • 𝟙 ((S.standardFormUniversalIndecMeshFunctor x₀).obj
            (S.standardFormUniversalMeshObj x₀ W))).hom =
            r • 𝟙 (S.fgObj W.1) := by
        change InducedCategory.homLinearEquiv (R := k)
            (r • 𝟙 ((S.standardFormUniversalIndecMeshFunctor x₀).obj
              (S.standardFormUniversalMeshObj x₀ W))) = _
        rw [map_smul, InducedCategory.homLinearEquiv_apply,
          InducedCategory.id_hom]
        simpa only [S.standardFormUniversalIndecMeshFunctor_obj_meshObj]
      rw [hid] at hscalar
      have hr : r = 0 := by
        apply S.standardFormUniversal_scalar_eq_zero_of_add_incomingStar_eq_zero
          x₀ W r c
        simpa only using hscalar
      rw [hr, S.standardFormUniversalSourceFiberDiagonal_zero]
    · unfold standardFormUniversalSourceFiberDiagonal
      rw [dif_neg hXW]
  rw [hdiag, map_zero, zero_add] at hdown
  have hdiagHom : diagonalHom = 0 := by
    dsimp only [diagonalHom]
    rw [hdiag, map_zero]
    rfl
  have hc : (∑ d : Quiver.Star W,
      c d ≫ S.standardFormUniversalMappedIncomingHom x₀ W d) = 0 := by
    rw [hdiagHom, zero_add] at hdownHom
    exact hdownHom
  have hdecomp : a = ∑ d : Quiver.Star W,
      LinearCovering.sourceFiberPostcomp (k := k) F X
        (T.incomingArrowHom (k := k) d) (b d) := by
    simpa only [hdiag, zero_add] using hb
  by_cases hW : W ∈
      MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀
  · have hzero := S.standardFormUniversal_projective_incomingStar_exact
      x₀ X W hW c hc
    refine ⟨b, ?_, hdecomp⟩
    intro d
    apply InducedCategory.hom_ext
    change c d = (0 : S.fgObj X ⟶ S.fgObj d.1.1)
    exact hzero d
  · let Wnp : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
          S.standardFormRightMeshData x₀ //
        W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀} := ⟨W, hW⟩
    obtain ⟨t, ht⟩ :=
      S.standardFormUniversal_nonprojective_incomingStar_exact
        x₀ X Wnp c hc
    let tauW := MeshCategory.RightMeshData.UniversalCover.tau
      S.standardFormRightMeshData x₀ Wnp
    let t' : X ⟶ F.obj (S.standardFormUniversalMeshObj x₀ tauW) :=
      InducedCategory.homMk t
    obtain ⟨q, hq⟩ :=
      S.standardFormUniversal_sourceFiberHomMap_surjective_meshObj
        x₀ X tauW t'
    let b' : ∀ d : Quiver.Star W,
        DirectSum
          (LinearCovering.Fiber F X)
          (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ d.1) :=
      fun d ↦ b d - LinearCovering.sourceFiberPostcomp (k := k) F X
        (S.standardFormUniversalPairedIncomingHom x₀ Wnp d) q
    refine ⟨b', ?_, ?_⟩
    · intro d
      dsimp only [b']
      rw [map_sub,
        LinearCovering.sourceFiberHomMap_sourceFiberPostcomp]
      apply InducedCategory.hom_ext
      change c d -
        (LinearCovering.sourceFiberHomMap (k := k) F X
          (S.standardFormUniversalMeshObj x₀ tauW) q).hom ≫
            S.standardFormUniversalMappedPairedIncomingHom x₀ Wnp d = 0
      have hqhom := congrArg InducedCategory.Hom.hom hq
      change (LinearCovering.sourceFiberHomMap (k := k) F X
        (S.standardFormUniversalMeshObj x₀ tauW) q).hom = t at hqhom
      rw [hqhom, ht d, sub_self]
    · calc
        a = ∑ d : Quiver.Star W,
            LinearCovering.sourceFiberPostcomp (k := k) F X
              (T.incomingArrowHom (k := k) d) (b d) := hdecomp
        _ = ∑ d : Quiver.Star W,
            LinearCovering.sourceFiberPostcomp (k := k) F X
              (T.incomingArrowHom (k := k) d) (b' d) := by
          dsimp only [b']
          simp_rw [map_sub]
          rw [Finset.sum_sub_distrib,
            S.standardFormUniversal_paired_sourceFiber_sum_eq_zero
              x₀ X Wnp q, sub_zero]

set_option backward.isDefEq.respectTransparency false in
/-- One exact Riedtmann peeling step in a fixed-source target fibre.  A
kernel family is a sum through the arrows leaving its source, with every
coefficient family again in the kernel. -/
theorem standardFormUniversal_targetFiber_kernel_peel
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ S.standardFormUniversalMeshObj x₀ W ⟶ Z.1))
    (ha : LinearCovering.targetFiberHomMap (k := k)
      (S.standardFormUniversalIndecMeshFunctor x₀)
      (S.standardFormUniversalMeshObj x₀ W) X a = 0) :
    ∃ b : ∀ d : Quiver.Costar W,
        DirectSum
          (LinearCovering.Fiber
            (S.standardFormUniversalIndecMeshFunctor x₀) X)
          (fun Z ↦ S.standardFormUniversalMeshObj x₀ d.1 ⟶ Z.1),
      (∀ d, LinearCovering.targetFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀)
        (S.standardFormUniversalMeshObj x₀ d.1) X (b d) = 0) ∧
      a = ∑ d : Quiver.Costar W,
        LinearCovering.targetFiberPrecomp (k := k)
          (S.standardFormUniversalIndecMeshFunctor x₀) X
          ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData x₀).outgoingArrowHom (k := k) d)
          (b d) := by
  classical
  let F := S.standardFormUniversalIndecMeshFunctor x₀
  let T := MeshCategory.RightMeshData.UniversalCover.rightMeshData
    S.standardFormRightMeshData x₀
  obtain ⟨r, b, hb⟩ :=
    S.standardFormUniversal_exists_targetFiber_eq_diagonal_add_outgoing
      x₀ W X a
  let c : ∀ d : Quiver.Costar W, S.fgObj d.1.1 ⟶ S.fgObj X :=
    fun d ↦ (LinearCovering.targetFiberHomMap (k := k) F
      (S.standardFormUniversalMeshObj x₀ d.1) X (b d)).hom
  have hdown :
      LinearCovering.targetFiberHomMap (k := k) F
          (S.standardFormUniversalMeshObj x₀ W) X
          (S.standardFormUniversalTargetFiberDiagonal x₀ W X r) +
        ∑ d : Quiver.Costar W,
          F.map (T.outgoingArrowHom (k := k) d) ≫
            LinearCovering.targetFiberHomMap (k := k) F
              (S.standardFormUniversalMeshObj x₀ d.1) X (b d) = 0 := by
    calc
      LinearCovering.targetFiberHomMap (k := k) F
            (S.standardFormUniversalMeshObj x₀ W) X
            (S.standardFormUniversalTargetFiberDiagonal x₀ W X r) +
          ∑ d : Quiver.Costar W,
            F.map (T.outgoingArrowHom (k := k) d) ≫
              LinearCovering.targetFiberHomMap (k := k) F
                (S.standardFormUniversalMeshObj x₀ d.1) X (b d) =
          LinearCovering.targetFiberHomMap (k := k) F
            (S.standardFormUniversalMeshObj x₀ W) X
            (S.standardFormUniversalTargetFiberDiagonal x₀ W X r +
              ∑ d : Quiver.Costar W,
                LinearCovering.targetFiberPrecomp (k := k) F X
                  (T.outgoingArrowHom (k := k) d) (b d)) := by
        rw [map_add, map_sum]
        apply congrArg₂ (.+.) rfl
        apply Finset.sum_congr rfl
        intro d _
        exact (LinearCovering.targetFiberHomMap_targetFiberPrecomp
          (k := k) F X (T.outgoingArrowHom (k := k) d) (b d)).symm
      _ = LinearCovering.targetFiberHomMap (k := k) F
          (S.standardFormUniversalMeshObj x₀ W) X a := by rw [← hb]
      _ = 0 := ha
  let diagonalHom : S.fgObj W.1 ⟶ S.fgObj X :=
    (LinearCovering.targetFiberHomMap (k := k) F
      (S.standardFormUniversalMeshObj x₀ W) X
      (S.standardFormUniversalTargetFiberDiagonal x₀ W X r)).hom
  let outgoingTerm : Quiver.Costar W → (S.fgObj W.1 ⟶ S.fgObj X) :=
    fun d ↦ (F.map (T.outgoingArrowHom (k := k) d) ≫
      LinearCovering.targetFiberHomMap (k := k) F
        (S.standardFormUniversalMeshObj x₀ d.1) X (b d)).hom
  have hdownTerms : diagonalHom +
      ∑ d : Quiver.Costar W, outgoingTerm d = 0 := by
    have h := congrArg (InducedCategory.homLinearEquiv (R := k)) hdown
    simp only [map_add, map_sum, map_zero,
      InducedCategory.homLinearEquiv_apply] at h
    simpa only [diagonalHom, outgoingTerm, F,
      S.standardFormUniversalIndecMeshFunctor_obj_meshObj] using h
  have hdownHom : diagonalHom +
      ∑ d : Quiver.Costar W,
        S.standardFormUniversalMappedOutgoingHom x₀ W d ≫ c d = 0 := by
    calc
      diagonalHom + ∑ d : Quiver.Costar W,
          S.standardFormUniversalMappedOutgoingHom x₀ W d ≫ c d =
        diagonalHom + ∑ d : Quiver.Costar W, outgoingTerm d := by
          apply congrArg₂ (.+.) rfl
          apply Finset.sum_congr rfl
          intro d _
          dsimp only [outgoingTerm, c,
            standardFormUniversalMappedOutgoingHom]
          rw [InducedCategory.comp_hom]
      _ = 0 := hdownTerms
  have hdiag : S.standardFormUniversalTargetFiberDiagonal x₀ W X r = 0 := by
    by_cases hXW : X = W.1
    · subst X
      have hscalar := hdownHom
      dsimp only [diagonalHom] at hscalar
      rw [S.standardFormUniversal_targetFiberHomMap_diagonal_self] at hscalar
      have hid :
          (r • 𝟙 ((S.standardFormUniversalIndecMeshFunctor x₀).obj
            (S.standardFormUniversalMeshObj x₀ W))).hom =
            r • 𝟙 (S.fgObj W.1) := by
        change InducedCategory.homLinearEquiv (R := k)
            (r • 𝟙 ((S.standardFormUniversalIndecMeshFunctor x₀).obj
              (S.standardFormUniversalMeshObj x₀ W))) = _
        rw [map_smul, InducedCategory.homLinearEquiv_apply,
          InducedCategory.id_hom]
        simpa only [S.standardFormUniversalIndecMeshFunctor_obj_meshObj]
      rw [hid] at hscalar
      have hr : r = 0 := by
        apply S.standardFormUniversal_scalar_eq_zero_of_add_outgoingCostar_eq_zero
          x₀ W r c
        simpa only using hscalar
      rw [hr, S.standardFormUniversalTargetFiberDiagonal_zero]
    · unfold standardFormUniversalTargetFiberDiagonal
      rw [dif_neg hXW]
  rw [hdiag, map_zero, zero_add] at hdown
  have hdiagHom : diagonalHom = 0 := by
    dsimp only [diagonalHom]
    rw [hdiag, map_zero]
    rfl
  have hc : (∑ d : Quiver.Costar W,
      S.standardFormUniversalMappedOutgoingHom x₀ W d ≫ c d) = 0 := by
    rw [hdiagHom, zero_add] at hdownHom
    exact hdownHom
  have hdecomp : a = ∑ d : Quiver.Costar W,
      LinearCovering.targetFiberPrecomp (k := k) F X
        (T.outgoingArrowHom (k := k) d) (b d) := by
    simpa only [hdiag, zero_add] using hb
  by_cases hW : Injective (S.fgObj W.1)
  · have hzero := S.standardFormUniversal_injective_outgoingCostar_exact
      x₀ X W hW c hc
    refine ⟨b, ?_, hdecomp⟩
    intro d
    apply InducedCategory.hom_ext
    change c d = (0 : S.fgObj d.1.1 ⟶ S.fgObj X)
    exact hzero d
  · let U := S.standardFormUniversalNoninjectiveMeshEndpoint x₀ W hW
    let e := S.standardFormUniversalNoninjectiveOutgoingCostarEquiv x₀ W hW
    obtain ⟨t, ht⟩ :=
      S.standardFormUniversal_noninjective_outgoingCostar_exact
        x₀ X W hW c hc
    let t' : F.obj (S.standardFormUniversalMeshObj x₀ U.1) ⟶ X :=
      InducedCategory.homMk t
    obtain ⟨q, hq⟩ :=
      S.standardFormUniversal_targetFiberHomMap_surjective_meshObj
        x₀ U.1 X t'
    let b' : ∀ d : Quiver.Costar W,
        DirectSum
          (LinearCovering.Fiber F X)
          (fun Z ↦ S.standardFormUniversalMeshObj x₀ d.1 ⟶ Z.1) :=
      fun d ↦ b d - LinearCovering.targetFiberPrecomp (k := k) F X
        (S.standardFormUniversalNoninjectiveIncomingCostarHom x₀ W hW d) q
    refine ⟨b', ?_, ?_⟩
    · intro d
      obtain ⟨u, hu⟩ := e.surjective d
      subst d
      dsimp only [b']
      rw [S.standardFormUniversalNoninjectiveIncomingCostarHom_apply]
      rw [map_sub,
        LinearCovering.targetFiberHomMap_targetFiberPrecomp]
      rw [sub_eq_zero]
      rw [hq]
      have htu := ht u
      dsimp only [c] at htu
      apply InducedCategory.hom_ext
      dsimp only [c, t', e]
      rw [InducedCategory.comp_hom]
      simpa only [F, U,
        S.standardFormUniversalIndecMeshFunctor_obj_meshObj,
        S.standardFormUniversalIndecMeshFunctor_map_incomingArrowHom,
        S.standardFormUniversalMappedIncomingHom_eq_normalized,
        InducedCategory.homMk_hom]
        using htu
    · let g : Quiver.Costar W → DirectSum
          (LinearCovering.Fiber F X)
          (fun Z ↦ S.standardFormUniversalMeshObj x₀ W ⟶ Z.1) :=
        fun d ↦ LinearCovering.targetFiberPrecomp (k := k) F X
          (T.outgoingArrowHom (k := k) d)
          (LinearCovering.targetFiberPrecomp (k := k) F X
            (S.standardFormUniversalNoninjectiveIncomingCostarHom
              x₀ W hW d) q)
      have hcorr : (∑ d : Quiver.Costar W, g d) = 0 := by
        calc
          (∑ d : Quiver.Costar W, g d) = ∑ u, g (e u) :=
            (e.sum_comp g).symm
          _ = ∑ u : Quiver.Star U.1,
              LinearCovering.targetFiberPrecomp (k := k) F X
                (T.outgoingArrowHom (k := k) (e u))
                (LinearCovering.targetFiberPrecomp (k := k) F X
                  (T.incomingArrowHom (k := k) u) q) := by
            apply Finset.sum_congr rfl
            intro u _
            dsimp only [g]
            rw [S.standardFormUniversalNoninjectiveIncomingCostarHom_apply]
            rfl
          _ = 0 := S.standardFormUniversal_noninjective_paired_targetFiber_sum_eq_zero
            x₀ X W hW q
      calc
        a = ∑ d : Quiver.Costar W,
            LinearCovering.targetFiberPrecomp (k := k) F X
              (T.outgoingArrowHom (k := k) d) (b d) := hdecomp
        _ = ∑ d : Quiver.Costar W,
            LinearCovering.targetFiberPrecomp (k := k) F X
              (T.outgoingArrowHom (k := k) d) (b' d) := by
          dsimp only [b']
          simp_rw [map_sub]
          rw [Finset.sum_sub_distrib]
          rw [show (∑ d : Quiver.Costar W,
            LinearCovering.targetFiberPrecomp (k := k) F X
              (T.outgoingArrowHom (k := k) d)
              (LinearCovering.targetFiberPrecomp (k := k) F X
                (S.standardFormUniversalNoninjectiveIncomingCostarHom
                  x₀ W hW d) q)) = 0 from hcorr, sub_zero]

/-- Componentwise path-length tail membership for a fixed-target
source-fibre family. -/
def standardFormUniversalSourceFiberInLengthTail
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) (n : ℕ)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ W)) : Prop :=
  ∀ Z, a Z ∈ MeshCategory.lengthTail (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀)
    (LinearPathCategory.vertex Z.1.as) W n

/-- Postcomposition by one displayed incoming arrow raises the
componentwise path-length tail by one. -/
theorem standardFormUniversal_sourceFiberPostcomp_inLengthTail_succ
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Star W) (n : ℕ)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ d.1))
    (ha : S.standardFormUniversalSourceFiberInLengthTail x₀ X d.1 n a) :
    S.standardFormUniversalSourceFiberInLengthTail x₀ X W (n + 1)
      (LinearCovering.sourceFiberPostcomp (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X
        ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀).incomingArrowHom (k := k) d) a) := by
  classical
  intro Z
  rw [LinearCovering.sourceFiberPostcomp_apply]
  apply MeshCategory.comp_mem_lengthTail (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀) (ha Z)
  exact MeshCategory.mem_lengthTail_of_mem_lengthComponent (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀) (by omega)
    ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀).incomingArrowHom_mem_lengthComponent_one
        (k := k) d)

/-- Componentwise path-length tails are separated on a fixed-target
source fibre. -/
theorem standardFormUniversal_sourceFiber_eq_zero_of_inLengthTail_all
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ W))
    (ha : ∀ n, S.standardFormUniversalSourceFiberInLengthTail
      x₀ X W n a) :
    a = 0 := by
  classical
  apply DirectSum.ext
  intro Z
  simp only [DirectSum.zero_apply]
  exact MeshCategory.eq_zero_of_mem_lengthTail_all (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀) (fun n ↦ ha n Z)

/-- Iterated kernel peeling places a fixed-target kernel family in every
prescribed path-length tail. -/
theorem standardFormUniversal_sourceFiber_kernel_mem_lengthTail
    (x₀ : Fin S.n) (X : S.FGIndecCategory) (n : ℕ)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ W))
    (ha : LinearCovering.sourceFiberHomMap (k := k)
      (S.standardFormUniversalIndecMeshFunctor x₀) X
      (S.standardFormUniversalMeshObj x₀ W) a = 0) :
    S.standardFormUniversalSourceFiberInLengthTail x₀ X W n a := by
  classical
  induction n generalizing W a with
  | zero =>
      unfold standardFormUniversalSourceFiberInLengthTail
      intro Z
      rw [MeshCategory.lengthTail_zero_eq_top]
      trivial
  | succ n ih =>
      obtain ⟨b, hb, hdecomp⟩ :=
        S.standardFormUniversal_sourceFiber_kernel_peel x₀ X W a ha
      rw [hdecomp]
      intro Z
      rw [DirectSum.sum_apply]
      apply Submodule.sum_mem
      intro d hd
      exact S.standardFormUniversal_sourceFiberPostcomp_inLengthTail_succ
        x₀ X W d n (b d) (ih d.1 (b d) (hb d)) Z

/-- The fixed-target source-fibre map of the normalized universal
realization has trivial kernel. -/
theorem standardFormUniversal_sourceFiber_kernel_eq_zero
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ Z.1 ⟶ S.standardFormUniversalMeshObj x₀ W))
    (ha : LinearCovering.sourceFiberHomMap (k := k)
      (S.standardFormUniversalIndecMeshFunctor x₀) X
      (S.standardFormUniversalMeshObj x₀ W) a = 0) :
    a = 0 := by
  apply S.standardFormUniversal_sourceFiber_eq_zero_of_inLengthTail_all
    x₀ X W a
  intro n
  exact S.standardFormUniversal_sourceFiber_kernel_mem_lengthTail
    x₀ X n W a ha

/-- Fixed-target source-fibre injectivity for a displayed universal-cover
mesh object. -/
theorem standardFormUniversal_sourceFiberHomMap_injective_meshObj
    (x₀ : Fin S.n) (X : S.FGIndecCategory)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    Function.Injective
      (LinearCovering.sourceFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X
        (S.standardFormUniversalMeshObj x₀ W)) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply S.standardFormUniversal_sourceFiber_kernel_eq_zero x₀ X W
  rw [map_sub, hab, sub_self]

/-- Every raw mesh-category object is literally represented by its
underlying universal-cover vertex, so the fixed-target surjectivity holds
for an arbitrary target object. -/
theorem standardFormUniversal_sourceFiberHomMap_surjective
    (x₀ : Fin S.n)
    (X : S.FGIndecCategory)
    (Y : MeshCategory.RawCategory (k := k)
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀)) :
    Function.Surjective
      (LinearCovering.sourceFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X Y) := by
  exact S.standardFormUniversal_sourceFiberHomMap_surjective_meshObj
    x₀ X (LinearPathCategory.vertex Y.as)

/-- The fixed-target source-fibre map is injective for an arbitrary raw
mesh-category target. -/
theorem standardFormUniversal_sourceFiberHomMap_injective
    (x₀ : Fin S.n)
    (X : S.FGIndecCategory)
    (Y : MeshCategory.RawCategory (k := k)
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀)) :
    Function.Injective
      (LinearCovering.sourceFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X Y) := by
  exact S.standardFormUniversal_sourceFiberHomMap_injective_meshObj
    x₀ X (LinearPathCategory.vertex Y.as)

/-- The normalized universal realization satisfies the fixed-target half
of the linear covering condition. -/
theorem standardFormUniversal_sourceFiberHomMap_bijective
    (x₀ : Fin S.n)
    (X : S.FGIndecCategory)
    (Y : MeshCategory.RawCategory (k := k)
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀)) :
    Function.Bijective
      (LinearCovering.sourceFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X Y) :=
  ⟨S.standardFormUniversal_sourceFiberHomMap_injective x₀ X Y,
    S.standardFormUniversal_sourceFiberHomMap_surjective x₀ X Y⟩

/-- Every raw mesh-category source is literally represented by its
underlying universal-cover vertex, so fixed-source target-fibre surjectivity
holds for an arbitrary source object. -/
theorem standardFormUniversal_targetFiberHomMap_surjective
    (x₀ : Fin S.n)
    (Y : MeshCategory.RawCategory (k := k)
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀))
    (X : S.FGIndecCategory) :
    Function.Surjective
      (LinearCovering.targetFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) Y X) := by
  exact S.standardFormUniversal_targetFiberHomMap_surjective_meshObj
    x₀ (LinearPathCategory.vertex Y.as) X

/-- Componentwise path-length tail membership for a fixed-source
target-fibre family. -/
def standardFormUniversalTargetFiberInLengthTail
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory) (n : ℕ)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ S.standardFormUniversalMeshObj x₀ W ⟶ Z.1)) : Prop :=
  ∀ Z, a Z ∈ MeshCategory.lengthTail (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀)
    W (LinearPathCategory.vertex Z.1.as) n

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition by one displayed outgoing arrow raises the
componentwise path-length tail by one. -/
theorem standardFormUniversal_targetFiberPrecomp_inLengthTail_succ
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Costar W) (X : S.FGIndecCategory) (n : ℕ)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ S.standardFormUniversalMeshObj x₀ d.1 ⟶ Z.1))
    (ha : S.standardFormUniversalTargetFiberInLengthTail x₀ d.1 X n a) :
    S.standardFormUniversalTargetFiberInLengthTail x₀ W X (n + 1)
      (LinearCovering.targetFiberPrecomp (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) X
        ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀).outgoingArrowHom (k := k) d) a) := by
  classical
  intro Z
  rw [LinearCovering.targetFiberPrecomp_apply]
  change ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀).outgoingArrowHom (k := k) d ≫ a Z) ∈
    MeshCategory.lengthTail (k := k)
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀) W
      (LinearPathCategory.vertex Z.1.as) (n + 1)
  have harrow :
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀).outgoingArrowHom (k := k) d ∈
        MeshCategory.lengthTail (k := k)
          (MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData x₀) W d.1 1 :=
    MeshCategory.mem_lengthTail_of_mem_lengthComponent (k := k)
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀) (by omega)
      ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀).outgoingArrowHom_mem_lengthComponent_one
          (k := k) d)
  simpa only [Nat.add_comm] using MeshCategory.comp_mem_lengthTail (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀) harrow (ha Z)

/-- Componentwise path-length tails are separated on a fixed-source
target fibre. -/
theorem standardFormUniversal_targetFiber_eq_zero_of_inLengthTail_all
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ S.standardFormUniversalMeshObj x₀ W ⟶ Z.1))
    (ha : ∀ n, S.standardFormUniversalTargetFiberInLengthTail
      x₀ W X n a) :
    a = 0 := by
  classical
  apply DirectSum.ext
  intro Z
  simp only [DirectSum.zero_apply]
  exact MeshCategory.eq_zero_of_mem_lengthTail_all (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀) (fun n ↦ ha n Z)

/-- Iterated kernel peeling places a fixed-source kernel family in every
prescribed path-length tail. -/
theorem standardFormUniversal_targetFiber_kernel_mem_lengthTail
    (x₀ : Fin S.n) (n : ℕ)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ S.standardFormUniversalMeshObj x₀ W ⟶ Z.1))
    (ha : LinearCovering.targetFiberHomMap (k := k)
      (S.standardFormUniversalIndecMeshFunctor x₀)
      (S.standardFormUniversalMeshObj x₀ W) X a = 0) :
    S.standardFormUniversalTargetFiberInLengthTail x₀ W X n a := by
  classical
  induction n generalizing W a with
  | zero =>
      unfold standardFormUniversalTargetFiberInLengthTail
      intro Z
      rw [MeshCategory.lengthTail_zero_eq_top]
      trivial
  | succ n ih =>
      obtain ⟨b, hb, hdecomp⟩ :=
        S.standardFormUniversal_targetFiber_kernel_peel x₀ W X a ha
      rw [hdecomp]
      intro Z
      rw [DirectSum.sum_apply]
      apply Submodule.sum_mem
      intro d hd
      exact S.standardFormUniversal_targetFiberPrecomp_inLengthTail_succ
        x₀ W d X n (b d) (ih d.1 (b d) (hb d)) Z

/-- The fixed-source target-fibre map of the normalized universal
realization has trivial kernel. -/
theorem standardFormUniversal_targetFiber_kernel_eq_zero
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory)
    (a : DirectSum
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor x₀) X)
      (fun Z ↦ S.standardFormUniversalMeshObj x₀ W ⟶ Z.1))
    (ha : LinearCovering.targetFiberHomMap (k := k)
      (S.standardFormUniversalIndecMeshFunctor x₀)
      (S.standardFormUniversalMeshObj x₀ W) X a = 0) :
    a = 0 := by
  apply S.standardFormUniversal_targetFiber_eq_zero_of_inLengthTail_all
    x₀ W X a
  intro n
  exact S.standardFormUniversal_targetFiber_kernel_mem_lengthTail
    x₀ n W X a ha

/-- Fixed-source target-fibre injectivity for a displayed universal-cover
mesh object. -/
theorem standardFormUniversal_targetFiberHomMap_injective_meshObj
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (X : S.FGIndecCategory) :
    Function.Injective
      (LinearCovering.targetFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀)
        (S.standardFormUniversalMeshObj x₀ W) X) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply S.standardFormUniversal_targetFiber_kernel_eq_zero x₀ W X
  rw [map_sub, hab, sub_self]

/-- The fixed-source target-fibre map is injective for an arbitrary raw
mesh-category source. -/
theorem standardFormUniversal_targetFiberHomMap_injective
    (x₀ : Fin S.n)
    (Y : MeshCategory.RawCategory (k := k)
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀))
    (X : S.FGIndecCategory) :
    Function.Injective
      (LinearCovering.targetFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) Y X) := by
  exact S.standardFormUniversal_targetFiberHomMap_injective_meshObj
    x₀ (LinearPathCategory.vertex Y.as) X

/-- The normalized universal realization satisfies the fixed-source half
of the linear covering condition. -/
theorem standardFormUniversal_targetFiberHomMap_bijective
    (x₀ : Fin S.n)
    (Y : MeshCategory.RawCategory (k := k)
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData x₀))
    (X : S.FGIndecCategory) :
    Function.Bijective
      (LinearCovering.targetFiberHomMap (k := k)
        (S.standardFormUniversalIndecMeshFunctor x₀) Y X) :=
  ⟨S.standardFormUniversal_targetFiberHomMap_injective x₀ Y X,
    S.standardFormUniversal_targetFiberHomMap_surjective x₀ Y X⟩

/-- The normalized standard-form realization of the universal mesh category
is a linear covering functor. -/
theorem standardFormUniversalIndecMeshFunctor_isCovering
    (x₀ : Fin S.n) :
    LinearCovering.IsCovering (k := k)
      (S.standardFormUniversalIndecMeshFunctor x₀) where
  target_bijective := S.standardFormUniversal_targetFiberHomMap_bijective x₀
  source_bijective := S.standardFormUniversal_sourceFiberHomMap_bijective x₀

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
