import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalCovering
import MagnitudeConjecture.Algebra.RightModuleNakayamaHom
import MagnitudeConjecture.CategoryTheory.FullyFaithfulNakayamaPairing
import MagnitudeConjecture.CategoryTheory.IndecomposableOfLocalEnd
import MagnitudeConjecture.CategoryTheory.LinearCoveringSummand
import MagnitudeConjecture.CategoryTheory.TranslationQuiverMeshOrbit
import MagnitudeConjecture.LinearAlgebra.DirectSumFubini

/-!
# Riedtmann conditions for the standard-form mesh category

This file descends the covering properties of the normalized universal
realization to the standard-form mesh category.  The first step compares its
Hom spaces with the corresponding Hom spaces between the chosen
indecomposable modules by reindexing the common fibres of the universal mesh
projection and the normalized realization.
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

local instance standardFormRiedtmannQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormRiedtmannArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

abbrev SourceCategory (x₀ : Fin S.n) :=
  MeshCategory.RawCategory (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData x₀)

abbrev meshProjection (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor
    S.standardFormRightMeshData x₀ (k := k)

abbrev realization (x₀ : Fin S.n) :=
  S.standardFormUniversalIndecMeshFunctor x₀

/-- The base incoming arrow underlying an incoming arrow at a universal-cover
vertex. -/
def projectedIncomingArrow
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Star W) :
    MeshCategory.RightMeshData.IncomingArrow W.1 :=
  ⟨d.1.1,
    (MeshCategory.RightMeshData.UniversalCover.projection
      S.standardFormRightMeshData x₀).map d.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The universal mesh projection sends an incoming represented arrow to
its underlying incoming represented arrow downstairs. -/
@[simp]
theorem meshProjection_map_incomingArrowHom
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (d : Quiver.Star W) :
    (meshProjection S x₀).map
        ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData x₀).incomingArrowHom (k := k) d) =
      S.standardFormRightMeshData.incomingArrowHom (k := k)
        (projectedIncomingArrow S x₀ W d) := by
  unfold meshProjection
    MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor
    MeshCategory.RightMeshData.incomingArrowHom
  rw [(MeshCategory.RightMeshData.UniversalCover.cover
    S.standardFormRightMeshData x₀).functorUsingSourceFintype_map_quotient_pathHom]
  rfl

/-- The two universal coverings have the same fibre over a base vertex: both
conditions say that the underlying universal-cover vertex has that base
label. -/
noncomputable def targetFiberEquiv (x₀ y : Fin S.n) :
    LinearCovering.Fiber (meshProjection S x₀)
        (MeshCategory.obj (k := k) S.standardFormRightMeshData y) ≃
      LinearCovering.Fiber (realization S x₀) y where
  toFun Z := ⟨Z.1, by
    have h := congrArg
      (fun X : S.StandardFormMeshCategory ↦
        LinearPathCategory.vertex X.as) Z.2
    exact h⟩
  invFun Z := ⟨Z.1, by
    apply CategoryTheory.Quotient.ext
    exact Z.2⟩
  left_inv Z := by
    rfl
  right_inv Z := by
    rfl

/-- Reindex the fixed-source direct sum from the fibre of the universal mesh
projection to the fibre of the normalized realization. -/
noncomputable def targetFiberHomReindexLinearEquiv
    (x₀ : Fin S.n)
    (X : SourceCategory S x₀)
    (y : Fin S.n) :
    DirectSum
        (LinearCovering.Fiber (meshProjection S x₀)
          (MeshCategory.obj (k := k) S.standardFormRightMeshData y))
        (fun Z ↦ X ⟶ Z.1) ≃ₗ[k]
      DirectSum
        (LinearCovering.Fiber (realization S x₀) y)
        (fun Z ↦ X ⟶ Z.1) := by
  let e := targetFiberEquiv S x₀ y
  let M : LinearCovering.Fiber (realization S x₀) y → Type u :=
    fun Z ↦ X ⟶ Z.1
  change DirectSum _ (fun Z ↦ M (e Z)) ≃ₗ[k] DirectSum _ M
  exact (DirectSum.lequivCongrLeft k e).trans
    (MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv fun Z ↦
      LinearEquiv.cast (R := k) (M := M) (e.apply_symm_apply Z))

@[simp]
theorem targetFiberHomReindexLinearEquiv_targetFiberLof
    (x₀ : Fin S.n) (X : SourceCategory S x₀) (y : Fin S.n)
    (Z : LinearCovering.Fiber (meshProjection S x₀)
      (MeshCategory.obj (k := k) S.standardFormRightMeshData y))
    (f : X ⟶ Z.1) :
    targetFiberHomReindexLinearEquiv S x₀ X y
        (LinearCovering.targetFiberLof (k := k)
          (meshProjection S x₀) X
          (MeshCategory.obj (k := k) S.standardFormRightMeshData y) Z f) =
      LinearCovering.targetFiberLof (k := k) (realization S x₀) X y
        (targetFiberEquiv S x₀ y Z) f := by
  classical
  let e := targetFiberEquiv S x₀ y
  let M : LinearCovering.Fiber (realization S x₀) y → Type u :=
    fun V ↦ X ⟶ V.1
  change targetFiberHomReindexLinearEquiv S x₀ X y
      (DirectSum.of (fun V ↦ M (e V)) Z f) =
    DirectSum.of M (e Z) f
  unfold targetFiberHomReindexLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  exact MagnitudeConjecture.DirectSumFubini.reindexCastLinearEquiv_of
    (T := M) e Z f

/-- Fibre reindexing commutes with precomposition by a morphism in the
common universal source category. -/
theorem targetFiberHomReindexLinearEquiv_targetFiberPrecomp
    (x₀ : Fin S.n) (y : Fin S.n)
    {X' X : SourceCategory S x₀} (e : X' ⟶ X)
    (a : DirectSum
      (LinearCovering.Fiber (meshProjection S x₀)
        (MeshCategory.obj (k := k) S.standardFormRightMeshData y))
      (fun Z ↦ X ⟶ Z.1)) :
    targetFiberHomReindexLinearEquiv S x₀ X' y
        (LinearCovering.targetFiberPrecomp (k := k)
          (meshProjection S x₀)
          (MeshCategory.obj (k := k) S.standardFormRightMeshData y) e a) =
      LinearCovering.targetFiberPrecomp (k := k) (realization S x₀) y e
        (targetFiberHomReindexLinearEquiv S x₀ X y a) := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp
  | of Z f =>
      rw [← DirectSum.lof_eq_of k _ (fun V ↦ X ⟶ V.1) Z f]
      change targetFiberHomReindexLinearEquiv S x₀ X' y
          (LinearCovering.targetFiberPrecomp (k := k)
            (meshProjection S x₀)
            (MeshCategory.obj (k := k) S.standardFormRightMeshData y) e
            (LinearCovering.targetFiberLof (k := k)
              (meshProjection S x₀) X
              (MeshCategory.obj (k := k) S.standardFormRightMeshData y) Z f)) =
        LinearCovering.targetFiberPrecomp (k := k) (realization S x₀)
          (show S.FGIndecCategory from y) e
          (targetFiberHomReindexLinearEquiv S x₀ X y
            (LinearCovering.targetFiberLof (k := k)
              (meshProjection S x₀) X
              (MeshCategory.obj (k := k) S.standardFormRightMeshData y) Z f))
      rw [LinearCovering.targetFiberPrecomp_lof,
        targetFiberHomReindexLinearEquiv_targetFiberLof,
        targetFiberHomReindexLinearEquiv_targetFiberLof,
        LinearCovering.targetFiberPrecomp_lof]
      rfl
  | add a b ha hb =>
      simp only [map_add, ha, hb]

/-- Reindex the fixed-target direct sum from the fibre of the universal mesh
projection to the fibre of the normalized realization. -/
noncomputable def sourceFiberHomReindexLinearEquiv
    (x₀ x : Fin S.n)
    (Y : SourceCategory S x₀) :
    DirectSum
        (LinearCovering.Fiber (meshProjection S x₀)
          (MeshCategory.obj (k := k) S.standardFormRightMeshData x))
        (fun Z ↦ Z.1 ⟶ Y) ≃ₗ[k]
      DirectSum
        (LinearCovering.Fiber (realization S x₀) x)
        (fun Z ↦ Z.1 ⟶ Y) := by
  let e := targetFiberEquiv S x₀ x
  let M : LinearCovering.Fiber (realization S x₀) x → Type u :=
    fun Z ↦ Z.1 ⟶ Y
  change DirectSum _ (fun Z ↦ M (e Z)) ≃ₗ[k] DirectSum _ M
  exact (DirectSum.lequivCongrLeft k e).trans
    (MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv fun Z ↦
      LinearEquiv.cast (R := k) (M := M) (e.apply_symm_apply Z))

@[simp]
theorem sourceFiberHomReindexLinearEquiv_sourceFiberLof
    (x₀ x : Fin S.n) (Y : SourceCategory S x₀)
    (Z : LinearCovering.Fiber (meshProjection S x₀)
      (MeshCategory.obj (k := k) S.standardFormRightMeshData x))
    (f : Z.1 ⟶ Y) :
    sourceFiberHomReindexLinearEquiv S x₀ x Y
        (LinearCovering.sourceFiberLof (k := k)
          (meshProjection S x₀)
          (MeshCategory.obj (k := k) S.standardFormRightMeshData x) Y Z f) =
      LinearCovering.sourceFiberLof (k := k) (realization S x₀) x Y
        (targetFiberEquiv S x₀ x Z) f := by
  classical
  let e := targetFiberEquiv S x₀ x
  let M : LinearCovering.Fiber (realization S x₀) x → Type u :=
    fun V ↦ V.1 ⟶ Y
  change sourceFiberHomReindexLinearEquiv S x₀ x Y
      (DirectSum.of (fun V ↦ M (e V)) Z f) =
    DirectSum.of M (e Z) f
  unfold sourceFiberHomReindexLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  exact MagnitudeConjecture.DirectSumFubini.reindexCastLinearEquiv_of
    (T := M) e Z f

/-- Fibre reindexing commutes with postcomposition by a morphism in the
common universal source category. -/
theorem sourceFiberHomReindexLinearEquiv_sourceFiberPostcomp
    (x₀ x : Fin S.n)
    {Y Y' : SourceCategory S x₀} (e : Y ⟶ Y')
    (a : DirectSum
      (LinearCovering.Fiber (meshProjection S x₀)
        (MeshCategory.obj (k := k) S.standardFormRightMeshData x))
      (fun Z ↦ Z.1 ⟶ Y)) :
    sourceFiberHomReindexLinearEquiv S x₀ x Y'
        (LinearCovering.sourceFiberPostcomp (k := k)
          (meshProjection S x₀)
          (MeshCategory.obj (k := k) S.standardFormRightMeshData x) e a) =
      LinearCovering.sourceFiberPostcomp (k := k) (realization S x₀) x e
        (sourceFiberHomReindexLinearEquiv S x₀ x Y a) := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp
  | of Z f =>
      rw [← DirectSum.lof_eq_of k _ (fun V ↦ V.1 ⟶ Y) Z f]
      change sourceFiberHomReindexLinearEquiv S x₀ x Y'
          (LinearCovering.sourceFiberPostcomp (k := k)
            (meshProjection S x₀)
            (MeshCategory.obj (k := k) S.standardFormRightMeshData x) e
            (LinearCovering.sourceFiberLof (k := k)
              (meshProjection S x₀)
              (MeshCategory.obj (k := k) S.standardFormRightMeshData x)
              Y Z f)) =
        LinearCovering.sourceFiberPostcomp (k := k) (realization S x₀)
          (show S.FGIndecCategory from x) e
          (sourceFiberHomReindexLinearEquiv S x₀ x Y
            (LinearCovering.sourceFiberLof (k := k)
              (meshProjection S x₀)
              (MeshCategory.obj (k := k) S.standardFormRightMeshData x)
              Y Z f))
      rw [LinearCovering.sourceFiberPostcomp_lof,
        sourceFiberHomReindexLinearEquiv_sourceFiberLof,
        sourceFiberHomReindexLinearEquiv_sourceFiberLof,
        LinearCovering.sourceFiberPostcomp_lof]
      rfl
  | add a b ha hb =>
      simp only [map_add, ha, hb]

/-- Hom spaces in the base mesh category and between the corresponding
chosen indecomposable modules are linearly equivalent.  A lift of the source
vertex is enough: the two covering equivalences then have literally the same
universal Hom summands after fibre reindexing. -/
noncomputable def meshHomLinearEquivFGIndec
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (y : Fin S.n) :
    (MeshCategory.obj (k := k) S.standardFormRightMeshData W.1 ⟶
        MeshCategory.obj (k := k) S.standardFormRightMeshData y) ≃ₗ[k]
      ((show S.FGIndecCategory from W.1) ⟶
        (show S.FGIndecCategory from y)) := by
  let X := S.standardFormUniversalMeshObj x₀ W
  exact
    ((MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
        S.standardFormRightMeshData x₀ (k := k)).targetFiberHomLinearEquiv
      X (MeshCategory.obj (k := k) S.standardFormRightMeshData y)).symm |>.trans
        ((targetFiberHomReindexLinearEquiv S x₀ X y).trans
          ((S.standardFormUniversalIndecMeshFunctor_isCovering x₀).targetFiberHomLinearEquiv
            X y))

/-- The Hom comparison intertwines precomposition upstairs with
precomposition by the images under both coverings. -/
theorem meshHomLinearEquivFGIndec_precomp
    (x₀ : Fin S.n)
    (W' W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (y : Fin S.n)
    (e : S.standardFormUniversalMeshObj x₀ W' ⟶
      S.standardFormUniversalMeshObj x₀ W)
    (u : MeshCategory.obj (k := k) S.standardFormRightMeshData W.1 ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData y) :
    meshHomLinearEquivFGIndec S x₀ W' y
        ((meshProjection S x₀).map e ≫ u) =
      (realization S x₀).map e ≫
        meshHomLinearEquivFGIndec S x₀ W y u := by
  let hP :=
    MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
      S.standardFormRightMeshData x₀ (k := k)
  let hF := S.standardFormUniversalIndecMeshFunctor_isCovering x₀
  let X := S.standardFormUniversalMeshObj x₀ W
  let X' := S.standardFormUniversalMeshObj x₀ W'
  let Y := MeshCategory.obj (k := k) S.standardFormRightMeshData y
  let uP : (meshProjection S x₀).obj X ⟶ Y := u
  let a := (hP.targetFiberHomLinearEquiv X Y).symm uP
  have hinv :
      (hP.targetFiberHomLinearEquiv X' Y).symm
          ((meshProjection S x₀).map e ≫ uP) =
        LinearCovering.targetFiberPrecomp (k := k)
          (meshProjection S x₀) Y e a := by
    apply (hP.targetFiberHomLinearEquiv X' Y).injective
    rw [LinearEquiv.apply_symm_apply,
      LinearCovering.IsCovering.targetFiberHomLinearEquiv_apply,
      LinearCovering.targetFiberHomMap_targetFiberPrecomp]
    dsimp only [a]
    change (meshProjection S x₀).map e ≫ uP =
      (meshProjection S x₀).map e ≫
        hP.targetFiberHomLinearEquiv X Y
          ((hP.targetFiberHomLinearEquiv X Y).symm uP)
    rw [LinearEquiv.apply_symm_apply]
  change hF.targetFiberHomLinearEquiv X' y
      (targetFiberHomReindexLinearEquiv S x₀ X' y
        ((hP.targetFiberHomLinearEquiv X' Y).symm
          ((meshProjection S x₀).map e ≫ uP))) = _
  rw [hinv,
    targetFiberHomReindexLinearEquiv_targetFiberPrecomp,
    LinearCovering.IsCovering.targetFiberHomLinearEquiv_apply,
    LinearCovering.targetFiberHomMap_targetFiberPrecomp]
  rfl

/-- Hom spaces with a fixed lifted target are compared through the common
source fibres of the universal mesh projection and normalized realization. -/
noncomputable def meshHomLinearEquivFGIndecFixedTarget
    (x₀ x : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    (MeshCategory.obj (k := k) S.standardFormRightMeshData x ⟶
        MeshCategory.obj (k := k) S.standardFormRightMeshData W.1) ≃ₗ[k]
      ((show S.FGIndecCategory from x) ⟶
        (show S.FGIndecCategory from W.1)) := by
  let Y := S.standardFormUniversalMeshObj x₀ W
  exact
    ((MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
        S.standardFormRightMeshData x₀ (k := k)).sourceFiberHomLinearEquiv
      (MeshCategory.obj (k := k) S.standardFormRightMeshData x) Y).symm |>.trans
        ((sourceFiberHomReindexLinearEquiv S x₀ x Y).trans
          ((S.standardFormUniversalIndecMeshFunctor_isCovering x₀).sourceFiberHomLinearEquiv
            x Y))

/-- Fixed-target Hom comparison for a target supplied directly as an object
of the realization fibre.  The endpoint equalities in the two coverings are
transported explicitly, while the common source-fibre summands are unchanged. -/
noncomputable def meshHomLinearEquivFGIndecFixedTargetFiber
    (x₀ x j : Fin S.n)
    (J : LinearCovering.Fiber (realization S x₀)
      (show S.FGIndecCategory from j)) :
    (MeshCategory.obj (k := k) S.standardFormRightMeshData x ⟶
        MeshCategory.obj (k := k) S.standardFormRightMeshData j) ≃ₗ[k]
      ((show S.FGIndecCategory from x) ⟶
        (show S.FGIndecCategory from j)) := by
  let Y := J.1
  let JP := (targetFiberEquiv S x₀ j).symm J
  let hP :=
    MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
      S.standardFormRightMeshData x₀ (k := k)
  let hF := S.standardFormUniversalIndecMeshFunctor_isCovering x₀
  exact
    (CategoryTheory.Linear.homCongr k (Iso.refl _)
        (eqToIso JP.2)).symm |>.trans
      ((hP.sourceFiberHomLinearEquiv
          (MeshCategory.obj (k := k) S.standardFormRightMeshData x) Y).symm |>.trans
        ((sourceFiberHomReindexLinearEquiv S x₀ x Y).trans
          ((hF.sourceFiberHomLinearEquiv x Y).trans
            (CategoryTheory.Linear.homCongr k (Iso.refl _)
              (eqToIso J.2)))))

/-- The fixed-target Hom comparison intertwines postcomposition upstairs
with postcomposition by the images under both coverings. -/
theorem meshHomLinearEquivFGIndecFixedTarget_postcomp
    (x₀ x : Fin S.n)
    (W W' : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (e : S.standardFormUniversalMeshObj x₀ W ⟶
      S.standardFormUniversalMeshObj x₀ W')
    (u : MeshCategory.obj (k := k) S.standardFormRightMeshData x ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData W.1) :
    meshHomLinearEquivFGIndecFixedTarget S x₀ x W'
        (u ≫ (meshProjection S x₀).map e) =
      meshHomLinearEquivFGIndecFixedTarget S x₀ x W u ≫
        (realization S x₀).map e := by
  let hP :=
    MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
      S.standardFormRightMeshData x₀ (k := k)
  let hF := S.standardFormUniversalIndecMeshFunctor_isCovering x₀
  let Y := S.standardFormUniversalMeshObj x₀ W
  let Y' := S.standardFormUniversalMeshObj x₀ W'
  let X := MeshCategory.obj (k := k) S.standardFormRightMeshData x
  let uP : X ⟶ (meshProjection S x₀).obj Y := u
  let a := (hP.sourceFiberHomLinearEquiv X Y).symm uP
  have hinv :
      (hP.sourceFiberHomLinearEquiv X Y').symm
          (uP ≫ (meshProjection S x₀).map e) =
        LinearCovering.sourceFiberPostcomp (k := k)
          (meshProjection S x₀) X e a := by
    apply (hP.sourceFiberHomLinearEquiv X Y').injective
    rw [LinearEquiv.apply_symm_apply,
      LinearCovering.IsCovering.sourceFiberHomLinearEquiv_apply,
      LinearCovering.sourceFiberHomMap_sourceFiberPostcomp]
    dsimp only [a]
    change uP ≫ (meshProjection S x₀).map e =
      hP.sourceFiberHomLinearEquiv X Y
          ((hP.sourceFiberHomLinearEquiv X Y).symm uP) ≫
        (meshProjection S x₀).map e
    rw [LinearEquiv.apply_symm_apply]
  change hF.sourceFiberHomLinearEquiv x Y'
      (sourceFiberHomReindexLinearEquiv S x₀ x Y'
        ((hP.sourceFiberHomLinearEquiv X Y').symm
          (uP ≫ (meshProjection S x₀).map e))) = _
  rw [hinv,
    sourceFiberHomReindexLinearEquiv_sourceFiberPostcomp,
    LinearCovering.IsCovering.sourceFiberHomLinearEquiv_apply,
    LinearCovering.sourceFiberHomMap_sourceFiberPostcomp]
  rfl

end UniversalCover

/-- The normalized universal coverings imply finite-dimensionality of every
Hom space in the standard-form mesh category.  For each Hom space we base the
universal cover at its source vertex, so no global connectedness hypothesis
is needed. -/
theorem standardFormMeshHomFinite :
    S.StandardFormMeshHomFinite := by
  intro X Y
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  let x := LinearPathCategory.vertex X
  let y := LinearPathCategory.vertex Y
  let W := MeshCategory.RightMeshData.UniversalCover.baseVertex
    S.standardFormRightMeshData x
  change FiniteDimensional k
    (MeshCategory.obj (k := k) S.standardFormRightMeshData x ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData y)
  change FiniteDimensional k
    (MeshCategory.obj (k := k) S.standardFormRightMeshData W.1 ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData y)
  let hmodule : Module.Finite k (S.fgObj W.1 ⟶ S.fgObj y) :=
    inferInstance
  let hindec : Module.Finite k
      ((show S.FGIndecCategory from W.1) ⟶
        (show S.FGIndecCategory from y)) :=
    hmodule.equiv (InducedCategory.homLinearEquiv (R := k)).symm
  exact hindec.equiv
    (UniversalCover.meshHomLinearEquivFGIndec S x W y).symm

set_option backward.isDefEq.respectTransparency false in
/-- The right almost-split sinks in the normalized universal realization
descend to Riedtmann's incoming-detection condition in the standard-form
mesh category. -/
theorem standardFormRiedtmannConditionB :
    S.StandardFormRiedtmannConditionB (k := k) := by
  intro z y u hu
  let W := MeshCategory.RightMeshData.UniversalCover.baseVertex
    S.standardFormRightMeshData z.1
  let e := UniversalCover.meshHomLinearEquivFGIndec S z.1 W y
  let uF := e u
  have huF : uF ≠ 0 := by
    intro hzero
    apply hu
    apply e.injective
    change e u = e 0
    exact hzero.trans e.map_zero.symm
  by_contra hnone
  push Not at hnone
  have hcomp (d : Quiver.Star W) :
      (UniversalCover.realization S z.1).map
          ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
            S.standardFormRightMeshData z.1).incomingArrowHom (k := k) d) ≫
        uF = 0 := by
    rw [← UniversalCover.meshHomLinearEquivFGIndec_precomp
      S z.1 d.1 W y
      ((MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData z.1).incomingArrowHom (k := k) d) u]
    rw [UniversalCover.meshProjection_map_incomingArrowHom,
      hnone, map_zero]
  have hcompHom (d : Quiver.Star W) :
      S.standardFormUniversalNormalizedArrowMap z.1 d.2 ≫ uF.hom = 0 := by
    have h := congrArg InducedCategory.Hom.hom (hcomp d)
    rw [InducedCategory.comp_hom,
      S.standardFormUniversalIndecMeshFunctor_map_incomingArrowHom] at h
    change S.standardFormUniversalNormalizedArrowMap z.1 d.2 ≫
      uF.hom = 0 at h
    exact h
  let sink := S.standardFormUniversalRealizedSink z.1
    (S.standardFormUniversalNormalizedArrowMap z.1) W
  have hnonprojective : ¬ Projective (S.fgObj W.1) := by
    change ¬ Projective (S.fgObj z.1)
    simpa [standardFormRightMeshData, standardFormProjectiveSet] using z.2
  have hsinkEpi : Epi sink :=
    IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
      S.almostSplitSkeleton sink
        (S.standardFormUniversalNormalizedRealizedSink_isRightAlmostSplit
          z.1 W) hnonprojective
  letI : Epi sink := hsinkEpi
  have hsinkzero : sink ≫ uF.hom = 0 := by
    have hdesc :
        biproduct.desc (fun i ↦
          S.standardFormUniversalNormalizedArrowMap z.1
            (S.standardFormUniversalMiddleArrow z.1 W i)) ≫ uF.hom = 0 := by
      apply biproduct.hom_ext'
      intro i
      rw [← Category.assoc, biproduct.ι_desc, hcompHom
        ⟨S.standardFormUniversalMiddleVertex z.1 W i,
          S.standardFormUniversalMiddleArrow z.1 W i⟩, comp_zero]
    change S.standardFormUniversalRealizedSink z.1
      (S.standardFormUniversalNormalizedArrowMap z.1) W ≫ uF.hom = 0
    unfold standardFormUniversalRealizedSink
    rw [Category.assoc]
    change (FiniteTauMatrix.rightMiddleDecompositionIso
        S.finiteTauCategoryData W.1).hom ≫
      (biproduct.desc (fun i ↦
        S.standardFormUniversalNormalizedArrowMap z.1
          (S.standardFormUniversalMiddleArrow z.1 W i)) ≫ uF.hom) = 0
    exact (congrArg
      (fun f ↦ (FiniteTauMatrix.rightMiddleDecompositionIso
        S.finiteTauCategoryData W.1).hom ≫ f) hdesc).trans comp_zero
  apply huF
  apply InducedCategory.hom_ext
  change uF.hom = 0
  apply (cancel_epi sink).1
  simpa using hsinkzero

omit [IsAlgClosed k] in
/-- The Nakayama image of a projective chosen indecomposable is again
indecomposable. -/
theorem standardFormProjectiveNakayamaIndecomposable
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    Indecomposable
      (RightModule.projectiveNakayamaFGObj (k := k) (S.fgObj p)) := by
  letI : Projective (S.fgObj p) := hp
  letI : IsLocalRing (End (S.fgObj p)) := S.fgObj_end_isLocalRing p
  letI : IsLocalRing
      (End (RightModule.projectiveNakayamaFGObj (k := k) (S.fgObj p))) :=
    MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (RightModule.projectiveNakayamaEndRingEquiv
        (k := k) (S.fgObj p))
  exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _

/-- The skeleton label representing the Nakayama image of a projective
vertex. -/
noncomputable def standardFormProjectiveNakayamaVertex
    (p : Fin S.n) (hp : Projective (S.fgObj p)) : Fin S.n :=
  Classical.choose
    (S.fgObj_complete
      (RightModule.projectiveNakayamaFGObj (k := k) (S.fgObj p))
      (S.standardFormProjectiveNakayamaIndecomposable p hp))

/-- The chosen identification of the Nakayama image with its skeleton
representative. -/
noncomputable def standardFormProjectiveNakayamaIso
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    RightModule.projectiveNakayamaFGObj (k := k) (S.fgObj p) ≅
      S.fgObj (S.standardFormProjectiveNakayamaVertex p hp) :=
  Classical.choice
    (Classical.choose_spec
      (S.fgObj_complete
        (RightModule.projectiveNakayamaFGObj (k := k) (S.fgObj p))
        (S.standardFormProjectiveNakayamaIndecomposable p hp)))

/-- Nakayama--Hom duality after replacing the Nakayama image by its chosen
skeleton representative. -/
noncomputable def standardFormProjectiveNakayamaHomEquiv
    (p : Fin S.n) (hp : Projective (S.fgObj p)) (x : Fin S.n) :
    (S.fgObj x ⟶
        S.fgObj (S.standardFormProjectiveNakayamaVertex p hp)) ≃ₗ[k]
      Module.Dual k (S.fgObj p ⟶ S.fgObj x) := by
  letI : Projective (S.fgObj p) := hp
  exact
    (CategoryTheory.Linear.homCongr k (Iso.refl (S.fgObj x))
      (S.standardFormProjectiveNakayamaIso p hp).symm).trans
        (RightModule.fieldNakayamaHomEquiv (k := k)
          (S.fgObj p) (S.fgObj x))

/-- The transposed Nakayama--Hom equivalence, in the orientation of the
composition pairing in Riedtmann condition (c). -/
noncomputable def standardFormProjectiveNakayamaPairingEquiv
    (p : Fin S.n) (hp : Projective (S.fgObj p)) (x : Fin S.n) :
    (S.fgObj p ⟶ S.fgObj x) ≃ₗ[k]
      Module.Dual k
        (S.fgObj x ⟶
          S.fgObj (S.standardFormProjectiveNakayamaVertex p hp)) :=
  (Module.evalEquiv k (S.fgObj p ⟶ S.fgObj x)).trans
    (S.standardFormProjectiveNakayamaHomEquiv p hp x).dualMap

/-- The socle functional on the Hom space from a projective chosen
indecomposable to its Nakayama endpoint. -/
def standardFormProjectiveNakayamaEpsilon
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    (S.fgObj p ⟶
        S.fgObj (S.standardFormProjectiveNakayamaVertex p hp)) →ₗ[k] k where
  toFun f :=
    letI : Projective (S.fgObj p) := hp
    RightModule.fieldNakayamaHomEquiv (k := k)
      (S.fgObj p) (S.fgObj p)
      (f ≫ (S.standardFormProjectiveNakayamaIso p hp).inv) (𝟙 _)
  map_add' := by
    intro f g
    simp only [Preadditive.add_comp, map_add, LinearMap.add_apply]
  map_smul' := by
    intro c f
    simp only [CategoryTheory.Linear.smul_comp, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]

omit [IsAlgClosed k] in
/-- The transposed Nakayama equivalence is literally evaluation of the
socle functional on composition. -/
theorem standardFormProjectiveNakayamaPairingEquiv_apply
    (p : Fin S.n) (hp : Projective (S.fgObj p)) (x : Fin S.n)
    (f : S.fgObj p ⟶ S.fgObj x)
    (g : S.fgObj x ⟶
      S.fgObj (S.standardFormProjectiveNakayamaVertex p hp)) :
    S.standardFormProjectiveNakayamaPairingEquiv p hp x f g =
      S.standardFormProjectiveNakayamaEpsilon p hp (f ≫ g) := by
  letI : Projective (S.fgObj p) := hp
  change RightModule.fieldNakayamaHomEquiv (k := k)
      (S.fgObj p) (S.fgObj x)
      (g ≫ (S.standardFormProjectiveNakayamaIso p hp).inv) f =
    RightModule.fieldNakayamaHomEquiv (k := k)
      (S.fgObj p) (S.fgObj p)
      ((f ≫ g) ≫ (S.standardFormProjectiveNakayamaIso p hp).inv) (𝟙 _)
  simpa only [Category.id_comp, Category.assoc] using
    (RightModule.fieldNakayamaHomEquiv_naturality
      (k := k) (S.fgObj p) f
      (g ≫ (S.standardFormProjectiveNakayamaIso p hp).inv)
      (𝟙 (S.fgObj p))).symm

/-- The projective Nakayama pairing, transported to the full category on the
chosen indecomposable skeleton. -/
noncomputable def standardFormProjectiveNakayamaFGIndecPairingEquiv
    (p : Fin S.n) (hp : Projective (S.fgObj p)) (x : Fin S.n) :
    ((show S.FGIndecCategory from p) ⟶
        (show S.FGIndecCategory from x)) ≃ₗ[k]
      Module.Dual k
        ((show S.FGIndecCategory from x) ⟶
          (show S.FGIndecCategory from
            S.standardFormProjectiveNakayamaVertex p hp)) :=
  (InducedCategory.homLinearEquiv (R := k)).trans
    ((S.standardFormProjectiveNakayamaPairingEquiv p hp x).trans
      (InducedCategory.homLinearEquiv (R := k)).dualMap)

omit [IsAlgClosed k] in
@[simp]
theorem standardFormProjectiveNakayamaFGIndecPairingEquiv_apply
    (p : Fin S.n) (hp : Projective (S.fgObj p)) (x : Fin S.n)
    (f : (show S.FGIndecCategory from p) ⟶
      (show S.FGIndecCategory from x))
    (g : (show S.FGIndecCategory from x) ⟶
      (show S.FGIndecCategory from
        S.standardFormProjectiveNakayamaVertex p hp)) :
    S.standardFormProjectiveNakayamaFGIndecPairingEquiv p hp x f g =
      S.standardFormProjectiveNakayamaEpsilon p hp (f.hom ≫ g.hom) := by
  exact S.standardFormProjectiveNakayamaPairingEquiv_apply
    p hp x f.hom g.hom

/-- The universal realization based at a projective vertex has a lift of its
Nakayama endpoint.  This is derived from the perfect pairing and the covering
Hom equivalence, rather than from a global connectedness hypothesis. -/
theorem standardFormProjectiveNakayamaTargetFiber_nonempty
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    Nonempty
      (LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor p)
        (show S.FGIndecCategory from
          S.standardFormProjectiveNakayamaVertex p hp)) := by
  let W := MeshCategory.RightMeshData.UniversalCover.baseVertex
    S.standardFormRightMeshData p
  let X := S.standardFormUniversalMeshObj p W
  let ePair := S.standardFormProjectiveNakayamaPairingEquiv p hp p
  have hEnd : Nontrivial (S.fgObj p ⟶ S.fgObj p) := by
    rw [nontrivial_iff]
    refine ⟨𝟙 _, 0, ?_⟩
    intro hzero
    exact (S.fgObj_indecomposable p).1
      ((IsZero.iff_id_eq_zero _).2 hzero)
  have hDual : Nontrivial
      (Module.Dual k
        (S.fgObj p ⟶
          S.fgObj (S.standardFormProjectiveNakayamaVertex p hp))) :=
    ePair.toEquiv.nontrivial_congr.mp hEnd
  have hHom : Nontrivial
      (S.fgObj p ⟶
        S.fgObj (S.standardFormProjectiveNakayamaVertex p hp)) :=
    (Module.nontrivial_dual_iff k).mp hDual
  have hInduced : Nontrivial
      ((show S.FGIndecCategory from p) ⟶
        (show S.FGIndecCategory from
          S.standardFormProjectiveNakayamaVertex p hp)) :=
    (InducedCategory.homLinearEquiv (R := k)).toEquiv.nontrivial_congr.mpr hHom
  let eCover :=
    (S.standardFormUniversalIndecMeshFunctor_isCovering p).targetFiberHomLinearEquiv
      X (show S.FGIndecCategory from
        S.standardFormProjectiveNakayamaVertex p hp)
  have hSum : Nontrivial
      (DirectSum
        (LinearCovering.Fiber
          (S.standardFormUniversalIndecMeshFunctor p)
          (show S.FGIndecCategory from
            S.standardFormProjectiveNakayamaVertex p hp))
        (fun Z ↦ X ⟶ Z.1)) :=
    eCover.toEquiv.nontrivial_congr.mpr hInduced
  obtain ⟨Z, _⟩ := CoveringHom.exists_nontrivial_of_directSum_nontrivial
    (fun Z : LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor p)
        (show S.FGIndecCategory from
          S.standardFormProjectiveNakayamaVertex p hp) ↦ X ⟶ Z.1) hSum
  exact ⟨Z⟩

/-- A chosen lift of the Nakayama endpoint in the universal realization based
at the projective vertex. -/
noncomputable def standardFormProjectiveNakayamaTargetFiber
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    LinearCovering.Fiber
      (S.standardFormUniversalIndecMeshFunctor p)
      (show S.FGIndecCategory from
        S.standardFormProjectiveNakayamaVertex p hp) :=
  Classical.choice (S.standardFormProjectiveNakayamaTargetFiber_nonempty p hp)

/-- The pointwise perfect pairing on the standard-form mesh category obtained
by transporting the projective Nakayama pairing through the two covering Hom
comparisons.  Identifying this transported pairing with evaluation on
composition by one functional is the remaining descent step for Riedtmann
condition (c). -/
noncomputable def standardFormMeshNakayamaPairingEquiv
    (p : Fin S.n) (hp : Projective (S.fgObj p)) (x : Fin S.n) :
    (MeshCategory.obj (k := k) S.standardFormRightMeshData p ⟶
        MeshCategory.obj (k := k) S.standardFormRightMeshData x) ≃ₗ[k]
      Module.Dual k
        (MeshCategory.obj (k := k) S.standardFormRightMeshData x ⟶
          MeshCategory.obj (k := k) S.standardFormRightMeshData
            (S.standardFormProjectiveNakayamaVertex p hp)) :=
  (UniversalCover.meshHomLinearEquivFGIndec S p
      (MeshCategory.RightMeshData.UniversalCover.baseVertex
        S.standardFormRightMeshData p) x).trans
    ((S.standardFormProjectiveNakayamaFGIndecPairingEquiv p hp x).trans
      (UniversalCover.meshHomLinearEquivFGIndecFixedTargetFiber S p x
        (S.standardFormProjectiveNakayamaVertex p hp)
        (S.standardFormProjectiveNakayamaTargetFiber p hp)).dualMap)

/-- In particular, the transported mesh pairing is bijective at every
intermediate vertex. -/
theorem standardFormMeshNakayamaPairingEquiv_bijective
    (p : Fin S.n) (hp : Projective (S.fgObj p)) (x : Fin S.n) :
    Function.Bijective (S.standardFormMeshNakayamaPairingEquiv p hp x) :=
  (S.standardFormMeshNakayamaPairingEquiv p hp x).bijective

/-- The projective Nakayama pairings assemble naturally in the variable
object.  This is the module-valued form of the perfect composition pairing
needed for Riedtmann condition (c). -/
noncomputable def standardFormProjectiveNakayamaLinearModuleIso
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    CoveringHom.linearCoyonedaLinearModule
        (k := k) (C := S.FGIndecCategory)
        (show S.FGIndecCategory from p) ≅
      CoveringHom.dualLinearYonedaLinearModule
        (k := k) (C := S.FGIndecCategory)
        (show S.FGIndecCategory from
          S.standardFormProjectiveNakayamaVertex p hp) := by
  apply ObjectProperty.isoMk
  refine NatIso.ofComponents (fun x ↦
    (S.standardFormProjectiveNakayamaFGIndecPairingEquiv
      p hp x).toModuleIso) ?_
  intro x y q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  change
    S.standardFormProjectiveNakayamaFGIndecPairingEquiv p hp y
        (f ≫ q) g =
      S.standardFormProjectiveNakayamaFGIndecPairingEquiv p hp x
        f (q ≫ g)
  rw [S.standardFormProjectiveNakayamaFGIndecPairingEquiv_apply,
    S.standardFormProjectiveNakayamaFGIndecPairingEquiv_apply]
  exact congrArg (S.standardFormProjectiveNakayamaEpsilon p hp)
    (Category.assoc f.hom q.hom g.hom)

/-- For a fixed target downstairs, only finitely many objects in its fibre
receive a nonzero morphism from any fixed universal-cover object.  This is a
formal consequence of the covering Hom equivalence and finite-dimensionality
of Hom spaces between finitely generated modules. -/
theorem standardFormUniversalTargetFiberHomFinite
    (p : Fin S.n) (X : S.FGIndecCategory)
    (Y : UniversalCover.SourceCategory S p) :
    {J : LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor p) X |
      Nontrivial (Y ⟶ J.1)}.Finite := by
  let hmodule : Module.Finite k
      (S.fgObj
          (show Fin S.n from
            (S.standardFormUniversalIndecMeshFunctor p).obj Y) ⟶
        S.fgObj (show Fin S.n from X)) :=
    inferInstance
  let hindec : Module.Finite k
      ((S.standardFormUniversalIndecMeshFunctor p).obj Y ⟶ X) :=
    hmodule.equiv (InducedCategory.homLinearEquiv (R := k)).symm
  let hsum : Module.Finite k
      (DirectSum
        (LinearCovering.Fiber
          (S.standardFormUniversalIndecMeshFunctor p) X)
        (fun J ↦ Y ⟶ J.1)) :=
    hindec.equiv
      ((S.standardFormUniversalIndecMeshFunctor_isCovering p
        ).targetFiberHomLinearEquiv Y X).symm
  letI : FiniteDimensional k
      (DirectSum
        (LinearCovering.Fiber
          (S.standardFormUniversalIndecMeshFunctor p) X)
        (fun J ↦ Y ⟶ J.1)) := hsum
  exact LinearCovering.finite_nontrivial_of_finiteDimensional_directSum
    (k := k) (fun J : LinearCovering.Fiber
      (S.standardFormUniversalIndecMeshFunctor p) X ↦ Y ⟶ J.1)

/-- Every Hom space in the normalized universal mesh category is
finite-dimensional.  A single upstairs summand embeds in the covering direct
sum, which is equivalent to a Hom space between finitely generated modules. -/
theorem standardFormUniversalMeshHomFinite
    (p : Fin S.n) (X Y : UniversalCover.SourceCategory S p) :
    FiniteDimensional k (X ⟶ Y) := by
  classical
  let F := S.standardFormUniversalIndecMeshFunctor p
  let hF := S.standardFormUniversalIndecMeshFunctor_isCovering p
  let hmodule : Module.Finite k
      (S.fgObj (show Fin S.n from F.obj X) ⟶
        S.fgObj (show Fin S.n from F.obj Y)) :=
    inferInstance
  let hindec : Module.Finite k (F.obj X ⟶ F.obj Y) :=
    hmodule.equiv (InducedCategory.homLinearEquiv (R := k)).symm
  letI : FiniteDimensional k (F.obj X ⟶ F.obj Y) := hindec
  let P : LinearCovering.Fiber F (F.obj X) := ⟨X, rfl⟩
  let inclusion : (X ⟶ Y) →ₗ[k] (F.obj X ⟶ F.obj Y) :=
    hF.sourceFiberHomLinearEquiv (F.obj X) Y |>.toLinearMap.comp
      (LinearCovering.sourceFiberLof (k := k) F (F.obj X) Y P)
  exact FiniteDimensional.of_injective inclusion fun f g hfg ↦ by
    have hlof :
        LinearCovering.sourceFiberLof (k := k) F (F.obj X) Y P f =
          LinearCovering.sourceFiberLof (k := k) F (F.obj X) Y P g :=
      hF.sourceFiberHomLinearEquiv (F.obj X) Y |>.injective hfg
    exact DirectSum.of_injective P hlof

/-- For a fixed target upstairs, only finitely many objects in a source fibre
of the canonical universal mesh projection have a nonzero morphism to it. -/
theorem standardFormUniversalMeshProjectionSourceFiberHomFinite
    (p : Fin S.n) (X : S.StandardFormMeshCategory)
    (Y : UniversalCover.SourceCategory S p) :
    {I : LinearCovering.Fiber (UniversalCover.meshProjection S p) X |
      Nontrivial (I.1 ⟶ Y)}.Finite := by
  let hbase : Module.Finite k
      (X ⟶ (UniversalCover.meshProjection S p).obj Y) :=
    S.standardFormMeshHomFinite X
      ((UniversalCover.meshProjection S p).obj Y)
  let hsum : Module.Finite k
      (DirectSum
        (LinearCovering.Fiber (UniversalCover.meshProjection S p) X)
        (fun I ↦ I.1 ⟶ Y)) :=
    hbase.equiv
      ((MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
        S.standardFormRightMeshData p (k := k)).sourceFiberHomLinearEquiv
          X Y).symm
  letI : FiniteDimensional k
      (DirectSum
        (LinearCovering.Fiber (UniversalCover.meshProjection S p) X)
        (fun I ↦ I.1 ⟶ Y)) := hsum
  exact LinearCovering.finite_nontrivial_of_finiteDimensional_directSum
    (k := k) (fun I : LinearCovering.Fiber
      (UniversalCover.meshProjection S p) X ↦ I.1 ⟶ Y)

/-- The same source-fibre finiteness holds after taking coefficient duals. -/
theorem standardFormUniversalMeshProjectionSourceFiberDualHomFinite
    (p : Fin S.n) (X : S.StandardFormMeshCategory)
    (Y : UniversalCover.SourceCategory S p) :
    {I : LinearCovering.Fiber (UniversalCover.meshProjection S p) X |
      Nontrivial (Module.Dual k (I.1 ⟶ Y))}.Finite := by
  refine (S.standardFormUniversalMeshProjectionSourceFiberHomFinite
    p X Y).subset ?_
  intro I hI
  exact (Module.nontrivial_dual_iff k).mp hI

/-- For one universal target, only finitely many deck shifts of any source
have a nontrivial coefficient-dual Hom into that target. -/
theorem standardFormUniversalDeckShiftDualHomFinite
    (p : Fin S.n) (J Y : UniversalCover.SourceCategory S p) :
    let D :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    {b : Additive
        (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
          S.standardFormRightMeshData p) |
      Nontrivial (Module.Dual k
        (((shiftFunctor (UniversalCover.SourceCategory S p) b).obj Y) ⟶ J))}.Finite := by
  let D :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only
  let E :=
    MeshCategory.RightMeshData.UniversalCover.deckShiftTargetFiberEquiv
      S.standardFormRightMeshData p (k := k) Y
  let T : Set (LinearCovering.Fiber
      (UniversalCover.meshProjection S p)
      ((UniversalCover.meshProjection S p).obj Y)) :=
    {I | Nontrivial (Module.Dual k (I.1 ⟶ J))}
  have hT : T.Finite :=
    S.standardFormUniversalMeshProjectionSourceFiberDualHomFinite p
      ((UniversalCover.meshProjection S p).obj Y) J
  have hpre : (E ⁻¹' T).Finite :=
    hT.preimage fun _ _ _ _ h ↦ E.injective h
  have hset :
      {b : Additive
          (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
            S.standardFormRightMeshData p) |
        Nontrivial (Module.Dual k
          (((shiftFunctor (UniversalCover.SourceCategory S p) b).obj Y) ⟶ J))} =
        E ⁻¹' T := by
    ext b
    rfl
  rw [hset]
  exact hpre

/-- Every vertex of the normalized universal mesh category has a local
endomorphism ring. -/
theorem standardFormUniversalMeshEndLocal
    (p : Fin S.n) (X : UniversalCover.SourceCategory S p) :
    IsLocalRing (End X) := by
  rcases X with ⟨X⟩
  let W := LinearPathCategory.vertex X
  change IsLocalRing
    (End (MeshCategory.obj (k := k)
      (MeshCategory.RightMeshData.UniversalCover.rightMeshData
        S.standardFormRightMeshData p) W))
  letI : FiniteDimensional k
      (End (MeshCategory.obj (k := k)
        (MeshCategory.RightMeshData.UniversalCover.rightMeshData
          S.standardFormRightMeshData p) W)) :=
    S.standardFormUniversalMeshHomFinite p _ _
  exact MeshCategory.end_isLocalRing_of_finiteDimensional
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData p) W

/-- The distinguished base lift as an object of the projective source
fibre. -/
def standardFormUniversalBaseSourceFiber (p : Fin S.n) :
    LinearCovering.Fiber (S.standardFormUniversalIndecMeshFunctor p)
      (show S.FGIndecCategory from p) :=
  ⟨S.standardFormUniversalMeshObj p
      (MeshCategory.RightMeshData.UniversalCover.baseVertex
        S.standardFormRightMeshData p), rfl⟩

/-- Pulling the projective Nakayama isomorphism to the normalized universal
cover and applying the two fixed-fibre covering decompositions gives the
natural direct-sum isomorphism used in the Bongartz--Gabriel summand
argument. -/
noncomputable def standardFormUniversalNakayamaFiberSumIso
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    LinearCovering.sourceFiberRepresentableLinearModule
        (k := k) (S.standardFormUniversalIndecMeshFunctor p)
        (show S.FGIndecCategory from p) ≅
      LinearCovering.targetFiberDualCorepresentableLinearModule
        (k := k) (S.standardFormUniversalIndecMeshFunctor p)
        (show S.FGIndecCategory from
          S.standardFormProjectiveNakayamaVertex p hp) :=
  (LinearCovering.sourceFiberRepresentablePullbackIso
      (k := k) (S.standardFormUniversalIndecMeshFunctor p)
      (S.standardFormUniversalIndecMeshFunctor_isCovering p)
      (show S.FGIndecCategory from p)).trans
    ((LinearCovering.linearModulePullbackIso
      (k := k) (S.standardFormUniversalIndecMeshFunctor p)
      (S.standardFormProjectiveNakayamaLinearModuleIso p hp)).trans
    (LinearCovering.targetFiberDualCorepresentablePullbackIso
      (k := k) (S.standardFormUniversalIndecMeshFunctor p)
      (S.standardFormUniversalIndecMeshFunctor_isCovering p)
      (show S.FGIndecCategory from
        S.standardFormProjectiveNakayamaVertex p hp)
      (fun Y ↦ S.standardFormUniversalTargetFiberHomFinite p
        (show S.FGIndecCategory from
          S.standardFormProjectiveNakayamaVertex p hp) Y)).symm)

/-- The local-ring finite-support argument isolates the distinguished base
representable as one dual-corepresentable summand over the Nakayama target
fibre. -/
theorem standardFormUniversalNakayamaSummandIso
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    ∃ J : LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor p)
        (show S.FGIndecCategory from
          S.standardFormProjectiveNakayamaVertex p hp),
      Nonempty
        (CoveringHom.linearCoyonedaLinearModule (k := k)
            (S.standardFormUniversalBaseSourceFiber p).1 ≅
          CoveringHom.dualLinearYonedaLinearModule (k := k) J.1) :=
  LinearCovering.exists_dualCorepresentable_iso_of_fiberSumIso
    (k := k) (S.standardFormUniversalIndecMeshFunctor p)
    (S.standardFormUniversalBaseSourceFiber p)
    (S.standardFormUniversalNakayamaFiberSumIso p hp)
    (S.standardFormUniversalMeshHomFinite p)
    (S.standardFormUniversalMeshEndLocal p)

/-- The isolated universal Nakayama summand descends through the deck-shift
orbit.  The representable comparison is unconditional, while the dual
corepresentable comparison uses the finite deck support proved above. -/
theorem standardFormUniversalNakayamaShiftOrbitSummandIso
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    let D :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    ∃ J : LinearCovering.Fiber
        (S.standardFormUniversalIndecMeshFunctor p)
        (show S.FGIndecCategory from
          S.standardFormProjectiveNakayamaVertex p hp),
      Nonempty
        (CoveringHom.linearCoyonedaLinearModule
            (k := k)
            (C := CoveringHom.ShiftOrbitCategory
              (UniversalCover.SourceCategory S p)
              (Additive
                (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
                  S.standardFormRightMeshData p)))
            (show CoveringHom.ShiftOrbitCategory
                (UniversalCover.SourceCategory S p)
                (Additive
                  (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
                    S.standardFormRightMeshData p)) from
              (S.standardFormUniversalBaseSourceFiber p).1) ≅
          CoveringHom.dualLinearYonedaLinearModule
            (k := k)
            (C := CoveringHom.ShiftOrbitCategory
              (UniversalCover.SourceCategory S p)
              (Additive
                (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
                  S.standardFormRightMeshData p)))
            (show CoveringHom.ShiftOrbitCategory
                (UniversalCover.SourceCategory S p)
                (Additive
                  (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
                    S.standardFormRightMeshData p)) from J.1)) := by
  let D :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only
  obtain ⟨J, ⟨e⟩⟩ := S.standardFormUniversalNakayamaSummandIso p hp
  refine ⟨J, ⟨?_⟩⟩
  let Push := CoveringHom.linearModuleOrbitPushdown
    (k := k) (C := UniversalCover.SourceCategory S p)
    (A := Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p))
  let repIso :
      Push.obj (CoveringHom.linearCoyonedaLinearModule
          (k := k) (S.standardFormUniversalBaseSourceFiber p).1) ≅
        CoveringHom.linearCoyonedaLinearModule
          (k := k)
          (C := CoveringHom.ShiftOrbitCategory
            (UniversalCover.SourceCategory S p)
            (Additive
              (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
                S.standardFormRightMeshData p)))
          (show CoveringHom.ShiftOrbitCategory
              (UniversalCover.SourceCategory S p)
              (Additive
                (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
                  S.standardFormRightMeshData p)) from
            (S.standardFormUniversalBaseSourceFiber p).1) :=
    (CoveringHom.IsLinearModule
      (C := CoveringHom.ShiftOrbitCategory
        (UniversalCover.SourceCategory S p)
        (Additive
          (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
            S.standardFormRightMeshData p))) k).ι.preimageIso
      (CoveringHom.orbitPushdownLinearCoyonedaIso
        (k := k)
        (A := Additive
          (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
            S.standardFormRightMeshData p))
        (S.standardFormUniversalBaseSourceFiber p).1)
  let dualIso :
      Push.obj (CoveringHom.dualLinearYonedaLinearModule (k := k) J.1) ≅
        CoveringHom.dualLinearYonedaLinearModule
          (k := k)
          (C := CoveringHom.ShiftOrbitCategory
            (UniversalCover.SourceCategory S p)
            (Additive
              (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
                S.standardFormRightMeshData p)))
          (show CoveringHom.ShiftOrbitCategory
              (UniversalCover.SourceCategory S p)
              (Additive
                (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
                  S.standardFormRightMeshData p)) from J.1) :=
    (CoveringHom.IsLinearModule
      (C := CoveringHom.ShiftOrbitCategory
        (UniversalCover.SourceCategory S p)
        (Additive
          (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
            S.standardFormRightMeshData p))) k).ι.preimageIso
      (CoveringHom.orbitPushdownDualLinearYonedaIso
        (k := k)
        (A := Additive
          (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
            S.standardFormRightMeshData p)) J.1
        (S.standardFormUniversalDeckShiftDualHomFinite p J.1))
  exact repIso.symm.trans ((Push.mapIso e).trans dualIso)

/-- The descended Nakayama summand supplies Riedtmann's perfect composition
pairing at a projective vertex.  On the component of the base lift this is
the fully faithful image of the orbit pairing; outside that component both
Hom spaces vanish by the empty-fibre covering decompositions. -/
noncomputable def standardFormRiedtmannProjectiveDualityData
    (p : Fin S.n) (hp : Projective (S.fgObj p)) :
    S.StandardFormRiedtmannProjectiveDualityData (k := k) p := by
  let j := S.standardFormProjectiveNakayamaVertex p hp
  let D :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  have hdesc := S.standardFormUniversalNakayamaShiftOrbitSummandIso p hp
  dsimp only at hdesc
  let J := Classical.choose hdesc
  let e := Classical.choice (Classical.choose_spec hdesc)
  let H :=
    MeshCategory.RightMeshData.UniversalCover.meshShiftOrbitProjectionFunctor
      S.standardFormRightMeshData p (k := k)
  let hH :=
    MeshCategory.RightMeshData.UniversalCover.meshShiftOrbitProjectionFunctorFullyFaithful
      S.standardFormRightMeshData p (k := k)
  letI : H.Faithful := hH.faithful
  letI : H.Full := hH.full
  let OrbitCategory := CoveringHom.ShiftOrbitCategory
    (UniversalCover.SourceCategory S p)
    (Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p))
  let P : OrbitCategory := (S.standardFormUniversalBaseSourceFiber p).1
  let JO : OrbitCategory := J.1
  let P' := MeshCategory.obj (k := k) S.standardFormRightMeshData p
  let J' := MeshCategory.obj (k := k) S.standardFormRightMeshData j
  let iP : H.obj P ≅ P' := eqToIso (by rfl)
  let JP := (UniversalCover.targetFiberEquiv S p j).symm J
  let iJ : H.obj JO ≅ J' := eqToIso JP.2
  let epsilon := CoveringHom.fullyFaithfulLinearModuleIsoEpsilonCongr
    (k := k) H P JO P' J' iP iJ e
  refine
    { dualVertex := j
      epsilon := epsilon
      pairing_bijective := ?_ }
  intro x
  let X' := MeshCategory.obj (k := k) S.standardFormRightMeshData x
  by_cases hx : Nonempty
      (LinearCovering.Fiber (UniversalCover.meshProjection S p) X')
  · obtain ⟨X⟩ := hx
    let XO : OrbitCategory := X.1
    let iX : H.obj XO ≅ X' := eqToIso X.2
    let pairEquiv :=
      CoveringHom.fullyFaithfulLinearModuleIsoPairingEquivCongr
        (k := k) H P JO XO P' J' X' iP iJ iX e
    have hpair :
        S.standardFormRightMeshData.compositionDualityLinearMap
            (k := k) p x j epsilon = pairEquiv.toLinearMap := by
      apply LinearMap.ext
      intro q
      apply LinearMap.ext
      intro r
      exact
        (CoveringHom.fullyFaithfulLinearModuleIsoPairingEquivCongr_apply_apply
          (k := k) H P JO XO P' J' X' iP iJ iX e q r).symm
    rw [hpair]
    exact pairEquiv.bijective
  · let hcover :=
      MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
        S.standardFormRightMeshData p (k := k)
    have hleftImage : Subsingleton (H.obj P ⟶ X') := by
      exact LinearCovering.IsCovering.targetHom_subsingleton_of_fiber_not_nonempty
        (F := UniversalCover.meshProjection S p) hcover
        (show UniversalCover.SourceCategory S p from P) X' hx
    have hleft : Subsingleton (P' ⟶ X') :=
      (CategoryTheory.Linear.homCongr k iP (Iso.refl X')).toEquiv
        |>.subsingleton_congr.mp hleftImage
    have hrightImage : Subsingleton (X' ⟶ H.obj JO) := by
      exact LinearCovering.IsCovering.sourceHom_subsingleton_of_fiber_not_nonempty
        (F := UniversalCover.meshProjection S p) hcover X'
        (show UniversalCover.SourceCategory S p from JO) hx
    have hright : Subsingleton (X' ⟶ J') :=
      (CategoryTheory.Linear.homCongr k (Iso.refl X') iJ).toEquiv
        |>.subsingleton_congr.mp hrightImage
    letI : Subsingleton (P' ⟶ X') := hleft
    letI : Subsingleton (X' ⟶ J') := hright
    constructor
    · intro q r _
      exact Subsingleton.elim q r
    · intro phi
      exact ⟨0, Subsingleton.elim _ _⟩

/-- Riedtmann condition (c) for the standard-form mesh category. -/
theorem standardFormRiedtmannConditionC :
    S.StandardFormRiedtmannConditionC (k := k) := by
  intro p hp
  have hp' : Projective (S.fgObj p) :=
    (S.mem_standardFormProjectiveSet_iff p).mp hp
  exact ⟨S.standardFormRiedtmannProjectiveDualityData p hp'⟩

/-- All three Riedtmann inputs for the standard-form mesh category. -/
theorem standardFormRiedtmannConditions :
    S.StandardFormRiedtmannConditions (k := k) where
  homFinite := S.standardFormMeshHomFinite
  conditionB := S.standardFormRiedtmannConditionB
  conditionC := S.standardFormRiedtmannConditionC

/-- The standard-form restricted Yoneda realization is faithful.  This is
the first recovery consequence of the completed Riedtmann conditions. -/
theorem standardFormRestrictedYonedaFunctor_faithful :
    (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).Faithful :=
  S.standardFormRestrictedYonedaFunctor_faithful_of_conditions
    S.standardFormRiedtmannConditions

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
