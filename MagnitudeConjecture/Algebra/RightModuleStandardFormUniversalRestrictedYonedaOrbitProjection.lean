import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalRestrictedYonedaPushdown

/-! # The descended opposite projection on the universal standard-form cover -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalRestrictedYonedaOrbitProjectionQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalRestrictedYonedaOrbitProjectionArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The ambient universal mesh projection descended from the opposite deck-shift orbit category. -/
noncomputable def standardFormUniversalOppositeShiftOrbitProjectionFunctor (p : Fin S.n) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := D.op.hasShift
    letI := D.op.additiveShift
    letI := D.op.linearShift (k := k)
    CoveringHom.ShiftOrbitCategory (SourceCategory S p)ᵒᵖ (Additive G) ⥤
      S.StandardFormMeshCategoryᵒᵖ := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
    S.standardFormRightMeshData p (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : MulAction G (SourceCategory S p)ᵒᵖ :=
    CoveringHom.oppositeMulAction
  letI := D.op.hasShift
  letI := D.op.additiveShift
  letI := D.op.linearShift (k := k)
  letI : HasShift S.StandardFormMeshCategoryᵒᵖ (Additive G) :=
    CoveringHom.trivialHasShift _ _
  letI : (meshProjection S p).op.CommShift (Additive G) :=
    CoveringHom.opFunctorCommShiftToTrivial D (meshProjection S p)
      (MeshCategory.RightMeshData.UniversalCover.meshProjectionCommShift
        S.standardFormRightMeshData p (k := k))
  exact CoveringHom.shiftOrbitDescendedFunctor (k := k)
    (A := Additive G) (meshProjection S p).op

noncomputable instance standardFormUniversalOppositeShiftOrbitProjectionFunctor_additive (p : Fin S.n) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := D.op.hasShift
    letI := D.op.additiveShift
    (standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).Additive := by
  dsimp only [standardFormUniversalOppositeShiftOrbitProjectionFunctor]
  infer_instance

noncomputable instance standardFormUniversalOppositeShiftOrbitProjectionFunctor_linear (p : Fin S.n) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := D.op.hasShift
    letI := D.op.additiveShift
    letI := D.op.linearShift (k := k)
    (standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).Linear k := by
  dsimp only [standardFormUniversalOppositeShiftOrbitProjectionFunctor]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The inverse ambient projection shift comparison is the reverse fibre equality transport. -/
theorem standardFormUniversalMeshProjectionCommShift_inv_app
    (p : Fin S.n)
    (a : Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p))
    (Y : SourceCategory S p) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
    letI := D.hasShift
    letI : HasShift S.StandardFormMeshCategory (Additive G) :=
      CoveringHom.trivialHasShift _ _
    letI := MeshCategory.RightMeshData.UniversalCover.meshProjectionCommShift
      S.standardFormRightMeshData p (k := k)
    ((meshProjection S p).commShiftIso a).inv.app Y =
      eqToHom
        (MeshCategory.RightMeshData.UniversalCover.deckShiftTargetFiberEquiv
          S.standardFormRightMeshData p (k := k) Y a).2.symm := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
    S.standardFormRightMeshData p (k := k)
  letI := D.hasShift
  letI : HasShift S.StandardFormMeshCategory (Additive G) :=
    CoveringHom.trivialHasShift _ _
  letI := MeshCategory.RightMeshData.UniversalCover.meshProjectionCommShift
    S.standardFormRightMeshData p (k := k)
  let F := meshProjection S p
  rw [← cancel_epi ((F.commShiftIso a).hom.app Y)]
  rw [(F.commShiftIso a).hom_inv_id_app,
    MeshCategory.RightMeshData.UniversalCover.meshProjectionCommShift_hom_app]
  rw [eqToHom_trans]
  rfl

/-- Reindex an opposite shift-orbit Hom by the ambient source fibre. -/
noncomputable def standardFormUniversalOppositeShiftOrbitSourceFiberLinearEquiv (p : Fin S.n)
    (X Y : (SourceCategory S p)ᵒᵖ) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := D.op.hasShift
    letI := D.op.additiveShift
    letI := D.op.linearShift (k := k)
    CoveringHom.ShiftOrbitHom (Additive G) X Y ≃ₗ[k]
      DirectSum
        (LinearCovering.Fiber (meshProjection S p)
          ((meshProjection S p).obj Y.unop))
        (fun Z ↦ Z.1 ⟶ X.unop) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
    S.standardFormRightMeshData p (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : MulAction G (SourceCategory S p)ᵒᵖ :=
    CoveringHom.oppositeMulAction
  letI := D.op.hasShift
  letI := D.op.additiveShift
  letI := D.op.linearShift (k := k)
  let F := meshProjection S p
  let e := MeshCategory.RightMeshData.UniversalCover.deckShiftTargetFiberEquiv
    S.standardFormRightMeshData p (k := k) Y.unop
  let M : LinearCovering.Fiber F (F.obj Y.unop) → Type _ :=
    fun Z ↦ Z.1 ⟶ X.unop
  let reverseOpposite : CoveringHom.ShiftOrbitHom (Additive G) X Y ≃ₗ[k]
      DirectSum (Additive G)
        (fun a ↦ (shiftFunctor _ a).obj Y.unop ⟶ X.unop) :=
    MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv fun a ↦
      CoveringHom.oppositeHomLinearEquiv X
        ((shiftFunctor _ a).obj Y)
  let reindex : DirectSum (Additive G) (fun a ↦ M (e a)) ≃ₗ[k]
      DirectSum _ (fun Z ↦ M (e (e.symm Z))) :=
    DirectSum.lequivCongrLeft k e
  let castFibers : DirectSum _ (fun Z ↦ M (e (e.symm Z))) ≃ₗ[k]
      DirectSum _ M :=
    MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv fun Z ↦
      LinearEquiv.cast (R := k) (M := M) (e.apply_symm_apply Z)
  exact reverseOpposite.trans <| reindex.trans castFibers

set_option backward.isDefEq.respectTransparency false in
/-- The source-fibre reindexing sends one homogeneous orbit term to the corresponding fibre term. -/
@[simp]
theorem standardFormUniversalOppositeShiftOrbitSourceFiberLinearEquiv_shiftOrbitLof
    (p : Fin S.n)
    (X Y : (SourceCategory S p)ᵒᵖ)
    (a : Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p))
    (f : let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
          S.standardFormRightMeshData p
      let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
      letI : MulAction G (SourceCategory S p)ᵒᵖ :=
        CoveringHom.oppositeMulAction
      letI := D.op.hasShift
      CoveringHom.ShiftHom X Y a) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := D.op.hasShift
    letI := D.op.additiveShift
    letI := D.op.linearShift (k := k)
    standardFormUniversalOppositeShiftOrbitSourceFiberLinearEquiv S p X Y
        (CoveringHom.shiftOrbitLof (k := k) X Y a f) =
      LinearCovering.sourceFiberLof (k := k)
        (meshProjection S p) ((meshProjection S p).obj Y.unop) X.unop
        (MeshCategory.RightMeshData.UniversalCover.deckShiftTargetFiberEquiv
          S.standardFormRightMeshData p (k := k) Y.unop a) f.unop := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
    S.standardFormRightMeshData p (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : MulAction G (SourceCategory S p)ᵒᵖ :=
    CoveringHom.oppositeMulAction
  letI := D.op.hasShift
  letI := D.op.additiveShift
  letI := D.op.linearShift (k := k)
  classical
  let F := meshProjection S p
  let e := MeshCategory.RightMeshData.UniversalCover.deckShiftTargetFiberEquiv
    S.standardFormRightMeshData p (k := k) Y.unop
  let M : LinearCovering.Fiber F (F.obj Y.unop) → Type _ :=
    fun Z ↦ Z.1 ⟶ X.unop
  change standardFormUniversalOppositeShiftOrbitSourceFiberLinearEquiv S p X Y
      (DirectSum.of (fun b ↦ CoveringHom.ShiftHom X Y b) a f) =
    DirectSum.of M (e a) f.unop
  unfold standardFormUniversalOppositeShiftOrbitSourceFiberLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv_of]
  exact MagnitudeConjecture.DirectSumFubini.reindexCastLinearEquiv_of
    (T := M) e a f.unop

/-- The ambient covering identifies opposite shift-orbit Homs with downstairs opposite Homs. -/
noncomputable def standardFormUniversalOppositeShiftOrbitHomLinearEquiv (p : Fin S.n)
    (X Y : (SourceCategory S p)ᵒᵖ) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := D.op.hasShift
    letI := D.op.additiveShift
    letI := D.op.linearShift (k := k)
    CoveringHom.ShiftOrbitHom (Additive G) X Y ≃ₗ[k]
      ((meshProjection S p).op.obj X ⟶ (meshProjection S p).op.obj Y) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
    S.standardFormRightMeshData p (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : MulAction G (SourceCategory S p)ᵒᵖ :=
    CoveringHom.oppositeMulAction
  letI := D.op.hasShift
  letI := D.op.additiveShift
  letI := D.op.linearShift (k := k)
  let F := meshProjection S p
  exact (standardFormUniversalOppositeShiftOrbitSourceFiberLinearEquiv S p X Y).trans <|
    ((MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
      S.standardFormRightMeshData p (k := k)).sourceFiberHomLinearEquiv
        (F.obj Y.unop) X.unop).trans
      (CoveringHom.oppositeHomLinearEquiv
        ((meshProjection S p).op.obj X)
        ((meshProjection S p).op.obj Y)).symm

/-- The descended ambient opposite projection maps a homogeneous orbit term by the source-fibre map. -/
theorem standardFormUniversalOppositeShiftOrbitProjectionFunctor_map_shiftOrbitLof
    (p : Fin S.n)
    (X Y : (SourceCategory S p)ᵒᵖ)
    (a : Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p))
    (f : let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
          S.standardFormRightMeshData p
      let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
      letI : MulAction G (SourceCategory S p)ᵒᵖ :=
        CoveringHom.oppositeMulAction
      letI := D.op.hasShift
      CoveringHom.ShiftHom X Y a) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := D.op.hasShift
    letI := D.op.additiveShift
    letI := D.op.linearShift (k := k)
    (standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map (CoveringHom.shiftOrbitLof (k := k) X Y a f) =
      (LinearCovering.sourceFiberHomMap (k := k)
        (meshProjection S p) ((meshProjection S p).obj Y.unop) X.unop
        (LinearCovering.sourceFiberLof (k := k)
          (meshProjection S p) ((meshProjection S p).obj Y.unop) X.unop
          (MeshCategory.RightMeshData.UniversalCover.deckShiftTargetFiberEquiv
            S.standardFormRightMeshData p (k := k) Y.unop a)
          f.unop)).op := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
    S.standardFormRightMeshData p (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : MulAction G (SourceCategory S p)ᵒᵖ :=
    CoveringHom.oppositeMulAction
  letI := D.op.hasShift
  letI := D.op.additiveShift
  letI := D.op.linearShift (k := k)
  letI : HasShift S.StandardFormMeshCategory (Additive G) :=
    CoveringHom.trivialHasShift _ _
  letI := MeshCategory.RightMeshData.UniversalCover.meshProjectionCommShift
    S.standardFormRightMeshData p (k := k)
  letI : HasShift S.StandardFormMeshCategoryᵒᵖ (Additive G) :=
    CoveringHom.trivialHasShift _ _
  letI : (meshProjection S p).op.CommShift (Additive G) :=
    CoveringHom.opFunctorCommShiftToTrivial D (meshProjection S p)
      (MeshCategory.RightMeshData.UniversalCover.meshProjectionCommShift
        S.standardFormRightMeshData p (k := k))
  dsimp only
  rw [CoveringHom.shiftOrbitLof_apply]
  change (CoveringHom.shiftOrbitDescendedFunctor (k := k)
    (A := Additive G) (meshProjection S p).op).map
      (CoveringHom.shiftOrbitOf X Y a f) = _
  rw [CoveringHom.shiftOrbitDescendedFunctor_map_of,
    LinearCovering.sourceFiberHomMap_lof]
  unfold CoveringHom.shiftOrbitDescendHomogeneousMap
  apply Quiver.Hom.unop_inj
  change
    ((meshProjection S p).commShiftIso a).inv.app Y.unop ≫
        (meshProjection S p).map f.unop =
      eqToHom
          (MeshCategory.RightMeshData.UniversalCover.deckShiftTargetFiberEquiv
            S.standardFormRightMeshData p (k := k) Y.unop a).2.symm ≫
        (meshProjection S p).map f.unop
  rw [standardFormUniversalMeshProjectionCommShift_inv_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The ambient covering Hom equivalence is the Hom map of the descended projection. -/
@[simp]
theorem standardFormUniversalOppositeShiftOrbitHomLinearEquiv_apply (p : Fin S.n)
    (X Y : (SourceCategory S p)ᵒᵖ)
    (f : let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
          S.standardFormRightMeshData p
      let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
      letI : MulAction G (SourceCategory S p)ᵒᵖ :=
        CoveringHom.oppositeMulAction
      letI := D.op.hasShift
      letI := D.op.additiveShift
      CoveringHom.ShiftOrbitHom (Additive G) X Y) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := D.op.hasShift
    letI := D.op.additiveShift
    letI := D.op.linearShift (k := k)
    standardFormUniversalOppositeShiftOrbitHomLinearEquiv S p X Y f = (standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map f := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
    S.standardFormRightMeshData p (k := k)
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : MulAction G (SourceCategory S p)ᵒᵖ :=
    CoveringHom.oppositeMulAction
  letI := D.op.hasShift
  letI := D.op.additiveShift
  letI := D.op.linearShift (k := k)
  classical
  dsimp only at f ⊢
  refine DirectSum.induction_on f ?_ ?_ ?_
  · rw [map_zero, (standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map_zero]
  · intro a fa
    change standardFormUniversalOppositeShiftOrbitHomLinearEquiv S p X Y
        (CoveringHom.shiftOrbitLof (k := k) X Y a fa) =
      (standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map
        (CoveringHom.shiftOrbitLof (k := k) X Y a fa)
    unfold standardFormUniversalOppositeShiftOrbitHomLinearEquiv
    dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
    rw [standardFormUniversalOppositeShiftOrbitSourceFiberLinearEquiv_shiftOrbitLof,
      LinearCovering.IsCovering.sourceFiberHomLinearEquiv_apply,
      LinearCovering.sourceFiberHomMap_lof]
    rw [standardFormUniversalOppositeShiftOrbitProjectionFunctor_map_shiftOrbitLof]
    rw [LinearCovering.sourceFiberHomMap_lof]
    rfl
  · intro f₁ f₂ hf₁ hf₂
    rw [map_add, (standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map_add]
    exact congrArg₂ (.+.) hf₁ hf₂


end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
