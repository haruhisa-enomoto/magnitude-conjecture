import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalRestrictedYonedaProjectiveShift

/-! # Compatibility with the lifted-projective projection -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalRestrictedYonedaProjectionMapQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalRestrictedYonedaProjectionMapArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

set_option backward.isDefEq.respectTransparency false in
/-- Ambient opposite projection after inclusion agrees with the included restricted projective projection. -/
theorem standardFormUniversalOppositeProjectiveProjection_map
    (p : Fin S.n)
    (X Y : (StandardFormProjectiveSourceCategory S p)ᵒᵖ)
    (g : let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
          S.standardFormRightMeshData p
      let D := standardFormOppositeProjectiveDeckShift S p
      letI := D.hasShift
      letI := D.additiveShift
      CoveringHom.ShiftOrbitHom (Additive G) X Y) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let DAmbient :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    let DProjectiveOpposite := standardFormOppositeProjectiveDeckShift S p
    let DAmbientOpposite := DAmbient.op
    let J := (standardFormProjectiveProperty S p).ι
    let F : (StandardFormProjectiveSourceCategory S p)ᵒᵖ ⥤
        (SourceCategory S p)ᵒᵖ := J.op
    letI : MulAction G (SourceCategory S p)ᵒᵖ :=
      CoveringHom.oppositeMulAction
    letI := DProjectiveOpposite.hasShift
    letI := DProjectiveOpposite.additiveShift
    letI := DProjectiveOpposite.linearShift (k := k)
    letI := DAmbientOpposite.hasShift
    letI := DAmbientOpposite.additiveShift
    letI := DAmbientOpposite.linearShift (k := k)
    letI : F.CommShift (Additive G) :=
      standardFormUniversalOppositeProjectiveInclusionCommShift S p
    ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map
      ((CoveringHom.shiftOrbitMapFunctor
        (k := k) (A := Additive G) F).map g)).unop =
      (standardFormProjectiveMeshProperty S).ι.map
        ((standardFormOppositeProjectiveShiftOrbitProjectionFunctor S p).map
          g).unop := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let DProjectiveOpposite := standardFormOppositeProjectiveDeckShift S p
  let DAmbientOpposite := DAmbient.op
  let J := (standardFormProjectiveProperty S p).ι
  let F : (StandardFormProjectiveSourceCategory S p)ᵒᵖ ⥤
      (SourceCategory S p)ᵒᵖ := J.op
  letI : MulAction G (SourceCategory S p)ᵒᵖ :=
    CoveringHom.oppositeMulAction
  letI := DProjectiveOpposite.hasShift
  letI := DProjectiveOpposite.additiveShift
  letI := DProjectiveOpposite.linearShift (k := k)
  letI := DAmbientOpposite.hasShift
  letI := DAmbientOpposite.additiveShift
  letI := DAmbientOpposite.linearShift (k := k)
  letI : F.CommShift (Additive G) :=
    standardFormUniversalOppositeProjectiveInclusionCommShift S p
  classical
  change ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map
      ((CoveringHom.shiftOrbitMapFunctor
        (k := k) (A := Additive G) F).map g)).unop =
    (standardFormProjectiveMeshProperty S).ι.map
      ((standardFormOppositeProjectiveShiftOrbitProjectionFunctor S p).map
        g).unop
  refine DirectSum.induction_on g ?_ ?_ ?_
  · rw [(CoveringHom.shiftOrbitMapFunctor
        (k := k) (A := Additive G) F).map_zero,
      (standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map_zero,
      (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S p).map_zero,
      CategoryTheory.Limits.unop_zero]
    simpa only [CategoryTheory.Limits.unop_zero] using
      ((standardFormProjectiveMeshProperty S).ι.map_zero
        ((standardFormProjectiveMeshFullProjection S p).obj Y.unop)
        ((standardFormProjectiveMeshFullProjection S p).obj X.unop)).symm
  · intro a fa
    change ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map
        (CoveringHom.shiftOrbitDescendMapLinear (k := k) F
          (CoveringHom.shiftOrbitOf X Y a fa))).unop =
      (standardFormProjectiveMeshProperty S).ι.map
        ((standardFormOppositeProjectiveShiftOrbitProjectionFunctor S p).map
          (CoveringHom.shiftOrbitLof (k := k) X Y a fa)).unop
    rw [CoveringHom.shiftOrbitDescendMapLinear_of]
    change ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map
        (CoveringHom.shiftOrbitLof (k := k) _ _ a
          (CoveringHom.shiftOrbitDescendHomogeneousMap F a fa))).unop = _
    rw [standardFormUniversalOppositeShiftOrbitProjectionFunctor_map_shiftOrbitLof,
      standardFormOppositeProjectiveShiftOrbitProjectionFunctor_map_shiftOrbitLof,
      LinearCovering.sourceFiberHomMap_lof,
      LinearCovering.sourceFiberHomMap_lof]
    unfold CoveringHom.shiftOrbitDescendHomogeneousMap
    simp only [Quiver.Hom.unop_op, unop_comp]
    rw [(meshProjection S p).map_comp,
      (standardFormProjectiveMeshProperty S).ι.map_comp]
    rw [← Category.assoc]
    apply congrArg₂ (· ≫ ·)
    · exact
        standardFormUniversalProjectiveInclusion_shift_inv_comp_projection
          S p Y a
    · rfl
  · intro g₁ g₂ hg₁ hg₂
    rw [(CoveringHom.shiftOrbitMapFunctor
        (k := k) (A := Additive G) F).map_add,
      (standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map_add,
      (standardFormOppositeProjectiveShiftOrbitProjectionFunctor S p).map_add]
    simp only [CategoryTheory.unop_add,
      (standardFormProjectiveMeshProperty S).ι.map_add, hg₁, hg₂]

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
