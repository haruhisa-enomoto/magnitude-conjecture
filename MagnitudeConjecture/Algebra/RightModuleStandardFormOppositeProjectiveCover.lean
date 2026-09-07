import MagnitudeConjecture.Algebra.RightModuleStandardFormProjectiveCover
import MagnitudeConjecture.CategoryTheory.OppositeShiftOrbit

/-!
# The opposite projective standard-form cover

The standard-form algebra is defined from the opposite of the projective
mesh category.  This file takes the opposite of the restricted universal
projective cover and descends it through the corresponding deck orbit.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormOppositeProjectiveCoverQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormOppositeProjectiveCoverArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The fundamental group indexing the standard-form projective deck
action.  This public abbreviation gives downstream Hom constructions one
canonical exported group type. -/
abbrev StandardFormProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  StandardFormProjectiveGroup S x₀

/-- The strict deck action on the opposite lifted projective category. -/
noncomputable instance standardFormOppositeProjectiveSourceCategoryMulAction
    (x₀ : Fin S.n) :
    MulAction (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ :=
  CoveringHom.oppositeMulAction

/-- Freeness of the restricted deck action survives passage to opposites. -/
noncomputable instance standardFormOppositeProjectiveSourceCategoryIsCancelSMul
    (x₀ : Fin S.n) :
    IsCancelSMul (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ :=
  CoveringHom.oppositeIsCancelSMul

/-- The coherent deck shift on the opposite lifted projective category. -/
noncomputable def standardFormOppositeProjectiveDeckShift (x₀ : Fin S.n) :
    CoveringHom.CoherentDeckShift
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (StandardFormProjectiveGroup S x₀) :=
  (standardFormProjectiveDeckShift S x₀).op

noncomputable instance standardFormOppositeProjectiveDeckShift_additive
    (x₀ : Fin S.n) (a : Additive (ProjectiveGroup S x₀)) :
    (((standardFormOppositeProjectiveDeckShift S x₀).core.F a).Additive) := by
  dsimp only [standardFormOppositeProjectiveDeckShift]
  infer_instance

noncomputable instance standardFormOppositeProjectiveDeckShift_linear
    (x₀ : Fin S.n) (a : Additive (ProjectiveGroup S x₀)) :
    (((standardFormOppositeProjectiveDeckShift S x₀).core.F a).Linear k) := by
  dsimp only [standardFormOppositeProjectiveDeckShift]
  infer_instance

/-- The opposite of the restricted universal projective covering. -/
noncomputable abbrev standardFormOppositeProjectiveMeshFullProjection
    (x₀ : Fin S.n) :
    CategoryTheory.Functor
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
      (StandardFormProjectiveMeshFullSubcategory S)ᵒᵖ :=
  (standardFormProjectiveMeshFullProjection S x₀).op

noncomputable instance standardFormOppositeProjectiveMeshFullProjection_additive
    (x₀ : Fin S.n) :
    (standardFormOppositeProjectiveMeshFullProjection S x₀).Additive := by
  dsimp only [standardFormOppositeProjectiveMeshFullProjection]
  infer_instance

noncomputable instance standardFormOppositeProjectiveMeshFullProjection_linear
    (x₀ : Fin S.n) :
    (standardFormOppositeProjectiveMeshFullProjection S x₀).Linear k := by
  dsimp only [standardFormOppositeProjectiveMeshFullProjection]
  infer_instance

/-- A deck degree determines the corresponding object in the fibre of the
restricted projective covering. -/
noncomputable def standardFormProjectiveDeckShiftFiber
    (x₀ : Fin S.n) (Y : StandardFormProjectiveSourceCategory S x₀)
    (a : Additive (ProjectiveGroup S x₀)) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    LinearCovering.Fiber (standardFormProjectiveMeshFullProjection S x₀)
      ((standardFormProjectiveMeshFullProjection S x₀).obj Y) := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData x₀ (k := k)
  let H := standardFormProjectiveInvariantData S x₀
  let D := standardFormProjectiveDeckShift S x₀
  letI := DAmbient.hasShift
  letI := H.isStableUnderShift
  letI := D.hasShift
  refine ⟨(shiftFunctor _ a).obj Y, ?_⟩
  apply ObjectProperty.FullSubcategory.ext
  change
    ((standardFormProjectiveMeshFullProjection S x₀).obj
      ((@shiftFunctor (StandardFormProjectiveSourceCategory S x₀)
        (Additive (ProjectiveGroup S x₀)) _ _ D.hasShift a).obj Y)).obj =
      ((standardFormProjectiveMeshFullProjection S x₀).obj Y).obj
  have hshift : D.hasShift =
      ObjectProperty.hasShift (standardFormProjectiveProperty S x₀) :=
    H.hasShift_eq
  rw [hshift]
  unfold ObjectProperty.hasShift
  dsimp only [standardFormProjectiveMeshFullProjection,
    LinearCovering.fullSubcategoryRestriction]
  change
    (meshProjection S x₀).obj
        ((@shiftFunctor (SourceCategory S x₀)
          (Additive (ProjectiveGroup S x₀)) _ _ DAmbient.hasShift a).obj Y.obj) =
      (meshProjection S x₀).obj Y.obj
  change
    (meshProjection S x₀).obj
        ((MeshCategory.RightMeshData.UniversalCover.deckMeshEndofunctor
          S.standardFormRightMeshData x₀ a.toMul⁻¹ (k := k)).obj Y.obj) =
      (meshProjection S x₀).obj Y.obj
  exact
    MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_obj_deckMeshEndofunctor
      S.standardFormRightMeshData x₀ a.toMul⁻¹ (k := k) Y.obj

/-- Forgetting the projective full-subcategory wrappers sends the restricted
deck-shift fibre point to the corresponding ambient fibre point. -/
theorem standardFormProjectiveDeckShiftFiber_toAmbient
    (x₀ : Fin S.n) (Y : StandardFormProjectiveSourceCategory S x₀)
    (a : Additive (ProjectiveGroup S x₀)) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    LinearCovering.fullSubcategoryRestrictionFiberEquiv
        (meshProjection S x₀) (standardFormProjectiveMeshProperty S)
        ((standardFormProjectiveMeshFullProjection S x₀).obj Y)
        (standardFormProjectiveDeckShiftFiber S x₀ Y a) =
      MeshCategory.RightMeshData.UniversalCover.deckShiftTargetFiberEquiv
        S.standardFormRightMeshData x₀ (k := k) Y.obj a := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData x₀ (k := k)
  let H := standardFormProjectiveInvariantData S x₀
  let D := standardFormProjectiveDeckShift S x₀
  letI := DAmbient.hasShift
  letI := H.isStableUnderShift
  letI := D.hasShift
  apply Subtype.ext
  change
    ((@shiftFunctor (StandardFormProjectiveSourceCategory S x₀)
      (Additive (ProjectiveGroup S x₀)) _ _ D.hasShift a).obj Y).obj =
      (MeshCategory.RightMeshData.UniversalCover.deckMeshEndofunctor
        S.standardFormRightMeshData x₀ a.toMul⁻¹ (k := k)).obj Y.obj
  have hshift : D.hasShift =
      ObjectProperty.hasShift (standardFormProjectiveProperty S x₀) :=
    H.hasShift_eq
  rw [hshift]
  unfold ObjectProperty.hasShift
  rfl

/-- Deck degrees parametrize exactly the fibre of the restricted projective
covering. -/
noncomputable def standardFormProjectiveDeckShiftFiberEquiv
    (x₀ : Fin S.n) (Y : StandardFormProjectiveSourceCategory S x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    Additive (ProjectiveGroup S x₀) ≃
      LinearCovering.Fiber (standardFormProjectiveMeshFullProjection S x₀)
        ((standardFormProjectiveMeshFullProjection S x₀).obj Y) := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  let eRestrict :=
    LinearCovering.fullSubcategoryRestrictionFiberEquiv
      (meshProjection S x₀) (standardFormProjectiveMeshProperty S)
      ((standardFormProjectiveMeshFullProjection S x₀).obj Y)
  let eAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckShiftTargetFiberEquiv
      S.standardFormRightMeshData x₀ (k := k) Y.obj
  refine Equiv.ofBijective (standardFormProjectiveDeckShiftFiber S x₀ Y) ?_
  constructor
  · intro a b hab
    apply eAmbient.injective
    rw [← standardFormProjectiveDeckShiftFiber_toAmbient S x₀ Y a,
      ← standardFormProjectiveDeckShiftFiber_toAmbient S x₀ Y b,
      hab]
  · intro Z
    obtain ⟨a, ha⟩ := eAmbient.surjective (eRestrict Z)
    refine ⟨a, ?_⟩
    apply eRestrict.injective
    rw [standardFormProjectiveDeckShiftFiber_toAmbient]
    exact ha

set_option backward.isDefEq.respectTransparency false in
/-- The restricted projective commutation isomorphism is the equality
transport carried by its deck-shift fibre point. -/
theorem standardFormProjectiveMeshFullProjectionCommShift_hom_app
    (x₀ : Fin S.n) (a : Additive (ProjectiveGroup S x₀))
    (Y : StandardFormProjectiveSourceCategory S x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI : HasShift (StandardFormProjectiveMeshFullSubcategory S)
        (Additive (ProjectiveGroup S x₀)) :=
      CoveringHom.trivialHasShift _ _
    letI := standardFormProjectiveMeshFullProjectionCommShift S x₀
    ((standardFormProjectiveMeshFullProjection S x₀).commShiftIso a).hom.app Y =
      eqToHom (standardFormProjectiveDeckShiftFiber S x₀ Y a).2 := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData x₀ (k := k)
  let H := standardFormProjectiveInvariantData S x₀
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := DAmbient.hasShift
  letI : HasShift (StandardFormProjectiveMeshFullSubcategory S)
      (Additive (ProjectiveGroup S x₀)) :=
    CoveringHom.trivialHasShift _ _
  letI : HasShift S.StandardFormMeshCategory
      (Additive (ProjectiveGroup S x₀)) :=
    CoveringHom.trivialHasShift _ _
  let sourceInclusion := (standardFormProjectiveProperty S x₀).ι
  let targetInclusion := (standardFormProjectiveMeshProperty S).ι
  let ambientProjection := meshProjection S x₀
  let restrictedProjection := standardFormProjectiveMeshFullProjection S x₀
  letI : sourceInclusion.CommShift (Additive (ProjectiveGroup S x₀)) :=
    H.inclusionCommShift
  letI : ambientProjection.CommShift (Additive (ProjectiveGroup S x₀)) :=
    MeshCategory.RightMeshData.UniversalCover.meshProjectionCommShift
      S.standardFormRightMeshData x₀ (k := k)
  letI : targetInclusion.CommShift (Additive (ProjectiveGroup S x₀)) :=
    CoveringHom.trivialFunctorCommShift targetInclusion
  let e : restrictedProjection ⋙ targetInclusion ≅
      sourceInclusion ⋙ ambientProjection := Iso.refl _
  letI : restrictedProjection.CommShift (Additive (ProjectiveGroup S x₀)) :=
    Functor.CommShift.ofComp e (Additive (ProjectiveGroup S x₀))
  have hTargetHom :
      (targetInclusion.commShiftIso a).hom.app (restrictedProjection.obj Y) =
        𝟙 _ :=
    CoveringHom.trivialFunctorCommShift_hom_app
      targetInclusion a (restrictedProjection.obj Y)
  have hTargetInv :
      (targetInclusion.commShiftIso a).inv.app (restrictedProjection.obj Y) =
        𝟙 (targetInclusion.obj (restrictedProjection.obj Y)) := by
    rw [← cancel_epi
      ((targetInclusion.commShiftIso a).hom.app (restrictedProjection.obj Y))]
    rw [(targetInclusion.commShiftIso a).hom_inv_id_app, hTargetHom]
    simpa only [Category.comp_id]
  have hSource := H.inclusionCommShift_hom_app a Y
  change (restrictedProjection.commShiftIso a).hom.app Y = _
  change (Functor.CommShift.OfComp.iso e a).hom.app Y = _
  apply targetInclusion.map_injective
  rw [Functor.CommShift.OfComp.map_iso_hom_app]
  rw [Functor.commShiftIso_comp_hom_app]
  rw [MeshCategory.RightMeshData.UniversalCover.meshProjectionCommShift_hom_app]
  rw [hTargetInv]
  rw [hSource]
  apply eq_of_heq
  simp [e]
  rw [eqToHom_map, eqToHom_map]
  dsimp [CoveringHom.trivialHasShift, CoveringHom.trivialShiftMkCore,
    ShiftMkCore.shiftFunctor_eq]
  simp only [← eqToHom_refl, eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse restricted commutation component is the reverse equality
transport of the same deck-shift fibre point. -/
theorem standardFormProjectiveMeshFullProjectionCommShift_inv_app
    (x₀ : Fin S.n) (a : Additive (ProjectiveGroup S x₀))
    (Y : StandardFormProjectiveSourceCategory S x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI : HasShift (StandardFormProjectiveMeshFullSubcategory S)
        (Additive (ProjectiveGroup S x₀)) :=
      CoveringHom.trivialHasShift _ _
    letI := standardFormProjectiveMeshFullProjectionCommShift S x₀
    ((standardFormProjectiveMeshFullProjection S x₀).commShiftIso a).inv.app Y =
      eqToHom (standardFormProjectiveDeckShiftFiber S x₀ Y a).2.symm := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI : HasShift (StandardFormProjectiveMeshFullSubcategory S)
      (Additive (ProjectiveGroup S x₀)) :=
    CoveringHom.trivialHasShift _ _
  letI := standardFormProjectiveMeshFullProjectionCommShift S x₀
  let F := standardFormProjectiveMeshFullProjection S x₀
  rw [← cancel_epi ((F.commShiftIso a).hom.app Y)]
  rw [(F.commShiftIso a).hom_inv_id_app,
    standardFormProjectiveMeshFullProjectionCommShift_hom_app]
  rw [eqToHom_trans]
  rfl

/-- The opposite restricted covering commutes with the opposite deck shift
and the trivial shift downstairs. -/
@[implicit_reducible]
noncomputable def standardFormOppositeProjectiveMeshFullProjectionCommShift
    (x₀ : Fin S.n) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI : HasShift (StandardFormProjectiveMeshFullSubcategory S)ᵒᵖ
        (Additive (ProjectiveGroup S x₀)) :=
      CoveringHom.trivialHasShift _ _
    (standardFormOppositeProjectiveMeshFullProjection S x₀).CommShift
      (Additive (ProjectiveGroup S x₀)) := by
  exact CoveringHom.opFunctorCommShiftToTrivial
    (standardFormProjectiveDeckShift S x₀)
    (standardFormProjectiveMeshFullProjection S x₀)
    (standardFormProjectiveMeshFullProjectionCommShift S x₀)

/-- The opposite restricted projective cover descended to its concrete deck
orbit. -/
noncomputable def standardFormOppositeProjectiveShiftOrbitProjectionFunctor
    (x₀ : Fin S.n) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CategoryTheory.Functor
      (CoveringHom.ShiftOrbitCategory
        (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
        (Additive (ProjectiveGroup S x₀)))
      (StandardFormProjectiveMeshFullSubcategory S)ᵒᵖ := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI : HasShift (StandardFormProjectiveMeshFullSubcategory S)ᵒᵖ
      (Additive (ProjectiveGroup S x₀)) :=
    CoveringHom.trivialHasShift _ _
  letI := standardFormOppositeProjectiveMeshFullProjectionCommShift S x₀
  exact CoveringHom.shiftOrbitDescendedFunctor (k := k)
    (A := Additive (ProjectiveGroup S x₀))
    (standardFormOppositeProjectiveMeshFullProjection S x₀)

noncomputable instance
    standardFormOppositeProjectiveShiftOrbitProjectionFunctor_additive
    (x₀ : Fin S.n) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).Additive := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  dsimp only [standardFormOppositeProjectiveShiftOrbitProjectionFunctor]
  infer_instance

noncomputable instance
    standardFormOppositeProjectiveShiftOrbitProjectionFunctor_linear
    (x₀ : Fin S.n) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).Linear k := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only [standardFormOppositeProjectiveShiftOrbitProjectionFunctor]
  infer_instance

/-- Reversing opposite morphisms and reindexing deck degrees by the
restricted projective fibre identifies the opposite orbit Hom direct sum
with the fixed-source covering direct sum. -/
noncomputable def standardFormOppositeProjectiveShiftOrbitSourceFiberLinearEquiv
    (x₀ : Fin S.n)
    (X Y : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringHom.ShiftOrbitHom (Additive (ProjectiveGroup S x₀)) X Y ≃ₗ[k]
      DirectSum
        (LinearCovering.Fiber (standardFormProjectiveMeshFullProjection S x₀)
          ((standardFormProjectiveMeshFullProjection S x₀).obj Y.unop))
        (fun Z ↦ Z.1 ⟶ X.unop) := by
  let DOriginal := standardFormProjectiveDeckShift S x₀
  letI := DOriginal.hasShift
  letI := DOriginal.additiveShift
  letI := DOriginal.linearShift (k := k)
  let DOpposite := standardFormOppositeProjectiveDeckShift S x₀
  letI := DOpposite.hasShift
  letI := DOpposite.additiveShift
  letI := DOpposite.linearShift (k := k)
  let F := standardFormProjectiveMeshFullProjection S x₀
  let e := standardFormProjectiveDeckShiftFiberEquiv S x₀ Y.unop
  let M : LinearCovering.Fiber F (F.obj Y.unop) → Type _ :=
    fun Z ↦ Z.1 ⟶ X.unop
  let reverseOpposite : CoveringHom.ShiftOrbitHom
      (Additive (ProjectiveGroup S x₀)) X Y ≃ₗ[k]
      DirectSum (Additive (ProjectiveGroup S x₀))
        (fun a ↦ (shiftFunctor _ a).obj Y.unop ⟶ X.unop) :=
    MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv fun a ↦
      CoveringHom.oppositeHomLinearEquiv X
        ((shiftFunctor _ a).obj Y)
  let reindex : DirectSum (Additive (ProjectiveGroup S x₀))
      (fun a ↦ M (e a)) ≃ₗ[k]
      DirectSum _ (fun Z ↦ M (e (e.symm Z))) :=
    DirectSum.lequivCongrLeft k e
  let castFibers : DirectSum _ (fun Z ↦ M (e (e.symm Z))) ≃ₗ[k]
      DirectSum _ M :=
    MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv fun Z ↦
      LinearEquiv.cast (R := k) (M := M) (e.apply_symm_apply Z)
  exact reverseOpposite.trans <| reindex.trans castFibers

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem standardFormOppositeProjectiveShiftOrbitSourceFiberLinearEquiv_shiftOrbitLof
    (x₀ : Fin S.n)
    (X Y : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    (a : Additive (ProjectiveGroup S x₀))
    (f : let D := standardFormOppositeProjectiveDeckShift S x₀
      letI := D.hasShift
      CoveringHom.ShiftHom X Y a) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    standardFormOppositeProjectiveShiftOrbitSourceFiberLinearEquiv
        S x₀ X Y (CoveringHom.shiftOrbitLof (k := k) X Y a f) =
      LinearCovering.sourceFiberLof (k := k)
        (standardFormProjectiveMeshFullProjection S x₀)
        ((standardFormProjectiveMeshFullProjection S x₀).obj Y.unop)
        X.unop (standardFormProjectiveDeckShiftFiberEquiv S x₀ Y.unop a)
        f.unop := by
  let DOriginal := standardFormProjectiveDeckShift S x₀
  letI := DOriginal.hasShift
  letI := DOriginal.additiveShift
  letI := DOriginal.linearShift (k := k)
  let DOpposite := standardFormOppositeProjectiveDeckShift S x₀
  letI := DOpposite.hasShift
  letI := DOpposite.additiveShift
  letI := DOpposite.linearShift (k := k)
  classical
  let F := standardFormProjectiveMeshFullProjection S x₀
  let e := standardFormProjectiveDeckShiftFiberEquiv S x₀ Y.unop
  let M : LinearCovering.Fiber F (F.obj Y.unop) → Type _ :=
    fun Z ↦ Z.1 ⟶ X.unop
  change standardFormOppositeProjectiveShiftOrbitSourceFiberLinearEquiv
      S x₀ X Y (DirectSum.of (fun b ↦ CoveringHom.ShiftHom X Y b) a f) =
    DirectSum.of M (e a) f.unop
  unfold standardFormOppositeProjectiveShiftOrbitSourceFiberLinearEquiv
  dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [MagnitudeConjecture.DirectSumFubini.mapRangeLinearEquiv_of]
  exact MagnitudeConjecture.DirectSumFubini.reindexCastLinearEquiv_of
    (T := M) e a f.unop

/-- Reindexing opposite deck degrees by the restricted projective fibre and
then applying the fixed-source covering decomposition gives the Hom-space
equivalence for the opposite descended cover. -/
noncomputable def standardFormOppositeProjectiveShiftOrbitHomLinearEquiv
    (x₀ : Fin S.n)
    (X Y : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringHom.ShiftOrbitHom (Additive (ProjectiveGroup S x₀)) X Y ≃ₗ[k]
      ((standardFormOppositeProjectiveMeshFullProjection S x₀).obj X ⟶
        (standardFormOppositeProjectiveMeshFullProjection S x₀).obj Y) := by
  let DOriginal := standardFormProjectiveDeckShift S x₀
  letI := DOriginal.hasShift
  letI := DOriginal.additiveShift
  letI := DOriginal.linearShift (k := k)
  let DOpposite := standardFormOppositeProjectiveDeckShift S x₀
  letI := DOpposite.hasShift
  letI := DOpposite.additiveShift
  letI := DOpposite.linearShift (k := k)
  let F := standardFormProjectiveMeshFullProjection S x₀
  exact (standardFormOppositeProjectiveShiftOrbitSourceFiberLinearEquiv
    S x₀ X Y).trans <|
      ((standardFormProjectiveMeshFullProjection_isCovering S x₀).sourceFiberHomLinearEquiv
        (F.obj Y.unop) X.unop).trans
          (CoveringHom.oppositeHomLinearEquiv
            ((standardFormOppositeProjectiveMeshFullProjection S x₀).obj X)
            ((standardFormOppositeProjectiveMeshFullProjection S x₀).obj Y)).symm

/-- On a homogeneous opposite deck degree, the descended projection is the
opposite of the corresponding fixed-source covering summand. -/
theorem standardFormOppositeProjectiveShiftOrbitProjectionFunctor_map_shiftOrbitLof
    (x₀ : Fin S.n)
    (X Y : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    (a : Additive (ProjectiveGroup S x₀))
    (f : let D := standardFormOppositeProjectiveDeckShift S x₀
      letI := D.hasShift
      CoveringHom.ShiftHom X Y a) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).map
        (CoveringHom.shiftOrbitLof (k := k) X Y a f) =
      (LinearCovering.sourceFiberHomMap (k := k)
        (standardFormProjectiveMeshFullProjection S x₀)
        ((standardFormProjectiveMeshFullProjection S x₀).obj Y.unop)
        X.unop
        (LinearCovering.sourceFiberLof (k := k)
          (standardFormProjectiveMeshFullProjection S x₀)
          ((standardFormProjectiveMeshFullProjection S x₀).obj Y.unop)
          X.unop (standardFormProjectiveDeckShiftFiber S x₀ Y.unop a)
          f.unop)).op := by
  let DOriginal := standardFormProjectiveDeckShift S x₀
  letI := DOriginal.hasShift
  letI := DOriginal.additiveShift
  letI := DOriginal.linearShift (k := k)
  let DOpposite := standardFormOppositeProjectiveDeckShift S x₀
  letI := DOpposite.hasShift
  letI := DOpposite.additiveShift
  letI := DOpposite.linearShift (k := k)
  letI : HasShift (StandardFormProjectiveMeshFullSubcategory S)
      (Additive (ProjectiveGroup S x₀)) :=
    CoveringHom.trivialHasShift _ _
  letI := standardFormProjectiveMeshFullProjectionCommShift S x₀
  letI : HasShift (StandardFormProjectiveMeshFullSubcategory S)ᵒᵖ
      (Additive (ProjectiveGroup S x₀)) :=
    CoveringHom.trivialHasShift _ _
  letI := standardFormOppositeProjectiveMeshFullProjectionCommShift S x₀
  dsimp only
  rw [CoveringHom.shiftOrbitLof_apply]
  change
    (CoveringHom.shiftOrbitDescendedFunctor (k := k)
      (A := Additive (ProjectiveGroup S x₀))
      (standardFormOppositeProjectiveMeshFullProjection S x₀)).map
        (CoveringHom.shiftOrbitOf X Y a f) = _
  rw [CoveringHom.shiftOrbitDescendedFunctor_map_of,
    LinearCovering.sourceFiberHomMap_lof]
  unfold CoveringHom.shiftOrbitDescendHomogeneousMap
  apply Quiver.Hom.unop_inj
  change
    ((standardFormProjectiveMeshFullProjection S x₀).commShiftIso a).inv.app
          Y.unop ≫
        (standardFormProjectiveMeshFullProjection S x₀).map f.unop =
      eqToHom (standardFormProjectiveDeckShiftFiber S x₀ Y.unop a).2.symm ≫
        (standardFormProjectiveMeshFullProjection S x₀).map f.unop
  rw [standardFormProjectiveMeshFullProjectionCommShift_inv_app]
  rfl

/-- The explicit opposite covering Hom equivalence is exactly the Hom map of
the descended opposite orbit projection. -/
@[simp]
theorem standardFormOppositeProjectiveShiftOrbitHomLinearEquiv_apply
    (x₀ : Fin S.n)
    (X Y : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    (f : let D := standardFormOppositeProjectiveDeckShift S x₀
      letI := D.hasShift
      letI := D.additiveShift
      CoveringHom.ShiftOrbitHom (Additive (ProjectiveGroup S x₀)) X Y) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    standardFormOppositeProjectiveShiftOrbitHomLinearEquiv S x₀ X Y f =
      (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).map f := by
  let DOriginal := standardFormProjectiveDeckShift S x₀
  letI := DOriginal.hasShift
  letI := DOriginal.additiveShift
  letI := DOriginal.linearShift (k := k)
  let DOpposite := standardFormOppositeProjectiveDeckShift S x₀
  letI := DOpposite.hasShift
  letI := DOpposite.additiveShift
  letI := DOpposite.linearShift (k := k)
  classical
  dsimp only at f ⊢
  refine DirectSum.induction_on f ?_ ?_ ?_
  · rw [map_zero,
      (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).map_zero]
    rfl
  · intro a fa
    change
      standardFormOppositeProjectiveShiftOrbitHomLinearEquiv S x₀ X Y
          (CoveringHom.shiftOrbitLof (k := k) X Y a fa) =
        (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).map
          (CoveringHom.shiftOrbitLof (k := k) X Y a fa)
    unfold standardFormOppositeProjectiveShiftOrbitHomLinearEquiv
    dsimp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
    rw [standardFormOppositeProjectiveShiftOrbitSourceFiberLinearEquiv_shiftOrbitLof,
      LinearCovering.IsCovering.sourceFiberHomLinearEquiv_apply,
      LinearCovering.sourceFiberHomMap_lof]
    rw [standardFormOppositeProjectiveShiftOrbitProjectionFunctor_map_shiftOrbitLof]
    rw [LinearCovering.sourceFiberHomMap_lof]
    rfl
  · intro f₁ f₂ hf₁ hf₂
    rw [map_add,
      (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).map_add]
    exact congrArg₂ (.+.) hf₁ hf₂

/-- The descended opposite orbit projection is bijective on every Hom
space. -/
theorem standardFormOppositeProjectiveShiftOrbitProjectionFunctor_map_bijective
    (x₀ : Fin S.n)
    (X Y : (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Bijective
      ((standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).map :
        CoveringHom.ShiftOrbitHom (Additive (ProjectiveGroup S x₀)) X Y →
          ((standardFormOppositeProjectiveMeshFullProjection S x₀).obj X ⟶
            (standardFormOppositeProjectiveMeshFullProjection S x₀).obj Y)) := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let e := standardFormOppositeProjectiveShiftOrbitHomLinearEquiv S x₀ X Y
  constructor
  · intro f g hfg
    apply e.injective
    rw [standardFormOppositeProjectiveShiftOrbitHomLinearEquiv_apply,
      standardFormOppositeProjectiveShiftOrbitHomLinearEquiv_apply, hfg]
  · intro f
    refine ⟨e.symm f, ?_⟩
    rw [← standardFormOppositeProjectiveShiftOrbitHomLinearEquiv_apply,
      e.apply_symm_apply]

/-- The descended opposite orbit projection is fully faithful. -/
noncomputable def
    standardFormOppositeProjectiveShiftOrbitProjectionFunctorFullyFaithful
    (x₀ : Fin S.n) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).FullyFaithful := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀
  letI : F.Faithful :=
    ⟨fun h ↦
      (standardFormOppositeProjectiveShiftOrbitProjectionFunctor_map_bijective
        S x₀ _ _).injective h⟩
  letI : F.Full :=
    ⟨(standardFormOppositeProjectiveShiftOrbitProjectionFunctor_map_bijective
      S x₀ _ _).surjective⟩
  exact Functor.FullyFaithful.ofFullyFaithful F

/-- Based connectedness makes the descended opposite projective projection
surjective on objects. -/
theorem standardFormOppositeProjectiveShiftOrbitProjectionFunctor_obj_surjective
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Surjective
      (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).obj := by
  let DOriginal := standardFormProjectiveDeckShift S x₀
  letI := DOriginal.hasShift
  letI := DOriginal.additiveShift
  letI := DOriginal.linearShift (k := k)
  let DOpposite := standardFormOppositeProjectiveDeckShift S x₀
  letI := DOpposite.hasShift
  letI := DOpposite.additiveShift
  letI := DOpposite.linearShift (k := k)
  dsimp only
  intro Y
  obtain ⟨X, hX⟩ :=
    standardFormProjectiveShiftOrbitProjectionFunctor_obj_surjective
      S x₀ hconnected Y.unop
  refine ⟨Opposite.op X, ?_⟩
  exact congrArg Opposite.op hX

/-- For a connected standard-form translation quiver, the descended
opposite projective orbit projection is an equivalence. -/
theorem standardFormOppositeProjectiveShiftOrbitProjectionFunctor_isEquivalence
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀).IsEquivalence := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀
  let hff :=
    standardFormOppositeProjectiveShiftOrbitProjectionFunctorFullyFaithful S x₀
  exact
    { faithful := hff.faithful
      full := hff.full
      essSurj := F.essSurj_of_surj
        (standardFormOppositeProjectiveShiftOrbitProjectionFunctor_obj_surjective
          S x₀ hconnected) }

/-- The explicit equivalence from the opposite lifted-projective shift orbit
to the literal opposite downstairs projective full subcategory. -/
noncomputable def standardFormOppositeProjectiveShiftOrbitEquivalence
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringHom.ShiftOrbitCategory
        (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
        (Additive (ProjectiveGroup S x₀)) ≌
      (StandardFormProjectiveMeshFullSubcategory S)ᵒᵖ := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := standardFormOppositeProjectiveShiftOrbitProjectionFunctor S x₀
  letI : F.IsEquivalence :=
    standardFormOppositeProjectiveShiftOrbitProjectionFunctor_isEquivalence
      S x₀ hconnected
  exact F.asEquivalence

/-- The strict opposite projective deck-orbit skeleton is equivalent to the
literal opposite projective full subcategory downstairs. -/
noncomputable def standardFormOppositeProjectiveDeckOrbitEquivalence
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringHom.DeckOrbitSkeleton
        (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
        (ProjectiveGroup S x₀) ≌
      (StandardFormProjectiveMeshFullSubcategory S)ᵒᵖ := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact D.deckOrbitSkeletonEquivalence.trans
    (standardFormOppositeProjectiveShiftOrbitEquivalence S x₀ hconnected)

/-- The strict opposite projective deck-orbit skeleton is equivalent to the
indexed opposite projective mesh category used in the definition of the
standard-form algebra. -/
noncomputable def standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringHom.DeckOrbitSkeleton
        (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
        (ProjectiveGroup S x₀) ≌
      S.StandardFormProjectiveMeshCategoryᵒᵖ := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact
    (standardFormOppositeProjectiveDeckOrbitEquivalence S x₀ hconnected).trans
      (standardFormProjectiveMeshReindexEquivalence S).op

/-- The final opposite projective deck-orbit equivalence is additive. -/
noncomputable instance
    standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_functor_additive
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
      S x₀ hconnected).functor.Additive := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let eRep := D.deckOrbitSkeletonEquivalence
  let eOrbit := standardFormOppositeProjectiveShiftOrbitEquivalence
    S x₀ hconnected
  let eReindex := (standardFormProjectiveMeshReindexEquivalence S).op
  letI : eRep.functor.Additive :=
    CoveringHom.CoherentDeckShift.deckOrbitSkeletonEquivalence_functor_additive D
  letI : eOrbit.functor.Additive := by
    change (standardFormOppositeProjectiveShiftOrbitProjectionFunctor
      S x₀).Additive
    infer_instance
  letI : eReindex.functor.Additive := by
    change (standardFormProjectiveMeshReindex S).op.Additive
    infer_instance
  change ((eRep.functor ⋙ eOrbit.functor) ⋙ eReindex.functor).Additive
  constructor
  intro X Y f g
  change eReindex.functor.map
      (eOrbit.functor.map (eRep.functor.map (f + g))) = _
  rw [eRep.functor.map_add, eOrbit.functor.map_add,
    eReindex.functor.map_add]
  rfl

/-- The final opposite projective deck-orbit equivalence is linear. -/
noncomputable instance
    standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_functor_linear
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
      S x₀ hconnected).functor.Linear k := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let eRep := D.deckOrbitSkeletonEquivalence
  let eOrbit := standardFormOppositeProjectiveShiftOrbitEquivalence
    S x₀ hconnected
  let eReindex := (standardFormProjectiveMeshReindexEquivalence S).op
  letI : eRep.functor.Linear k :=
    CoveringHom.CoherentDeckShift.deckOrbitSkeletonEquivalence_functor_linear D
  letI : eOrbit.functor.Linear k := by
    change (standardFormOppositeProjectiveShiftOrbitProjectionFunctor
      S x₀).Linear k
    infer_instance
  letI : eReindex.functor.Linear k := by
    change (standardFormProjectiveMeshReindex S).op.Linear k
    infer_instance
  change ((eRep.functor ⋙ eOrbit.functor) ⋙ eReindex.functor).Linear k
  constructor
  intro X Y f r
  change eReindex.functor.map
      (eOrbit.functor.map (eRep.functor.map (r • f))) = _
  rw [eRep.functor.map_smul, eOrbit.functor.map_smul,
    eReindex.functor.map_smul]
  rfl

/-- The final deck-orbit equivalence sends a strict orbit to the projective
mesh vertex of its chosen representative. -/
@[simp]
theorem standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_functor_obj
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (Q : MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
        S x₀ hconnected).functor.obj Q =
      Opposite.op ((standardFormProjectiveMeshReindex S).obj
        ((standardFormProjectiveMeshFullProjection S x₀).obj
          (CoveringHom.deckOrbitRepresentative
            (C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
            (G := ProjectiveGroup S x₀) Q).unop)) := by
  rfl

/-- Distinct strict deck orbits have distinct images in the indexed
projective mesh category. -/
theorem standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_obj_injective
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Injective
      (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
        S x₀ hconnected).functor.obj := by
  let DOriginal := standardFormProjectiveDeckShift S x₀
  letI := DOriginal.hasShift
  letI := DOriginal.additiveShift
  letI := DOriginal.linearShift (k := k)
  let DOpposite := standardFormOppositeProjectiveDeckShift S x₀
  letI := DOpposite.hasShift
  letI := DOpposite.additiveShift
  letI := DOpposite.linearShift (k := k)
  dsimp only
  intro Q R hQR
  let X := (CoveringHom.deckOrbitRepresentative
    (C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    (G := ProjectiveGroup S x₀) Q).unop
  let Y := (CoveringHom.deckOrbitRepresentative
    (C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
    (G := ProjectiveGroup S x₀) R).unop
  let F := standardFormProjectiveMeshFullProjection S x₀
  have hReindex :
      (standardFormProjectiveMeshReindex S).obj (F.obj X) =
        (standardFormProjectiveMeshReindex S).obj (F.obj Y) := by
    apply congrArg Opposite.unop
    simpa only [
      standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_functor_obj]
      using hQR
  have hF : F.obj X = F.obj Y :=
    standardFormProjectiveMeshReindex_obj_injective S hReindex
  let Z : LinearCovering.Fiber F (F.obj X) := ⟨Y, hF.symm⟩
  let e := standardFormProjectiveDeckShiftFiberEquiv S x₀ X
  obtain ⟨a, ha⟩ := e.surjective Z
  have hShift : (shiftFunctor _ a).obj X = Y :=
    congrArg Subtype.val ha
  have hSmul : a.toMul⁻¹ • X = Y :=
    (standardFormProjectiveShiftFunctor_obj_eq_smul S x₀ a X).symm.trans
      hShift
  have hSmulOp :
      a.toMul⁻¹ • Opposite.op X = Opposite.op Y := by
    exact congrArg Opposite.op hSmul
  have hOrbitYX :
      (Quotient.mk'' (Opposite.op Y) :
        MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
          (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) =
        Quotient.mk'' (Opposite.op X) := by
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply]
    exact ⟨a.toMul⁻¹, hSmulOp⟩
  exact
    (CoveringHom.deckOrbitRepresentative_mk
      (C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
      (G := ProjectiveGroup S x₀) Q).symm |>.trans <|
      hOrbitYX.symm.trans <|
        CoveringHom.deckOrbitRepresentative_mk
          (C := (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ)
          (G := ProjectiveGroup S x₀) R

/-- Every indexed opposite projective mesh vertex is the literal image of a
strict deck orbit. -/
theorem standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_obj_surjective
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Surjective
      (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
        S x₀ hconnected).functor.obj := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only
  let E := standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
    S x₀ hconnected
  intro Y
  obtain ⟨X, ⟨e⟩⟩ :=
    (inferInstance : E.functor.EssSurj).mem_essImage Y
  exact ⟨X, S.standardFormProjectiveMeshCategoryOppositeSkeletal ⟨e⟩⟩

/-- The final deck-orbit equivalence has a literally bijective object map. -/
theorem standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_obj_bijective
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Bijective
      (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
        S x₀ hconnected).functor.obj := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact
    ⟨standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_obj_injective
        S x₀ hconnected,
      standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_obj_surjective
        S x₀ hconnected⟩

/-- The object-level equivalence underlying the strict deck-orbit
identification. -/
noncomputable def standardFormOppositeProjectiveIndexedDeckOrbitObjectEquiv
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringHom.DeckOrbitSkeleton
        (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ
        (ProjectiveGroup S x₀) ≃
      S.StandardFormProjectiveMeshCategoryᵒᵖ := by
  let D := standardFormOppositeProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact Equiv.ofBijective
    (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
      S x₀ hconnected).functor.obj
    (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence_obj_bijective
      S x₀ hconnected)

@[simp]
theorem standardFormOppositeProjectiveIndexedDeckOrbitObjectEquiv_apply
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (Q : MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)ᵒᵖ) :
    let D := standardFormOppositeProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    standardFormOppositeProjectiveIndexedDeckOrbitObjectEquiv
        S x₀ hconnected Q =
      (standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
        S x₀ hconnected).functor.obj Q := by
  rfl

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
