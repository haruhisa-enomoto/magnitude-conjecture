import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalRestrictedYonedaDownstairsValue

/-! # Naturality of the downstairs restricted-Yoneda comparison -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalRestrictedYonedaDownstairsIsoQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalRestrictedYonedaDownstairsIsoArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

set_option maxHeartbeats 400000 in
/-- The ambient orbit representable on projective orbit representatives is
naturally downstairs restricted Yoneda. -/
theorem standardFormUniversalOrbitRepresentableDownstairsRestrictedYonedaIsoNonempty
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X : SourceCategory S p) :
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
    let Rep := CoveringHom.deckOrbitRepresentativeFunctor
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) (G := G)
    let Map := CoveringHom.shiftOrbitMapFunctor
      (k := k) (A := Additive G) F
    let R := (linearCoyoneda k
      (CoveringHom.ShiftOrbitCategory
        (SourceCategory S p)ᵒᵖ (Additive G))).obj
          (Opposite.op
            (show CoveringHom.ShiftOrbitCategory
                (SourceCategory S p)ᵒᵖ (Additive G) from
              Opposite.op X))
    let E := standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
      S p hconnected
    let N := (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).obj ((meshProjection S p).obj X)
    Nonempty (Rep ⋙ Map ⋙ R ≅ E.functor ⋙ N.obj.obj) := by
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
  let Rep := CoveringHom.deckOrbitRepresentativeFunctor
    (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) (G := G)
  let Map := CoveringHom.shiftOrbitMapFunctor
    (k := k) (A := Additive G) F
  let R := (linearCoyoneda k
    (CoveringHom.ShiftOrbitCategory
      (SourceCategory S p)ᵒᵖ (Additive G))).obj
        (Opposite.op
          (show CoveringHom.ShiftOrbitCategory
              (SourceCategory S p)ᵒᵖ (Additive G) from
            Opposite.op X))
  let E := standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
    S p hconnected
  let N := (S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite).obj ((meshProjection S p).obj X)
  refine ⟨NatIso.ofComponents
    (fun Q ↦ (standardFormUniversalOrbitRepresentableDownstairsRestrictedYonedaValueLinearEquiv S p hconnected X Q).toModuleIso) ?_⟩
  intro Q Q' f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  change standardFormUniversalOppositeShiftOrbitOriginalHomLinearEquiv S p (Opposite.op X) (F.obj (Rep.obj Q'))
      (q ≫ Map.map (Rep.map f)) =
    (N.obj.obj.map (E.functor.map f)).hom
      (standardFormUniversalOppositeShiftOrbitOriginalHomLinearEquiv S p (Opposite.op X) (F.obj (Rep.obj Q)) q)
  rw [standardFormUniversalOppositeShiftOrbitOriginalHomLinearEquiv_apply, standardFormUniversalOppositeShiftOrbitOriginalHomLinearEquiv_apply,
    (standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map_comp]
  rw [unop_comp]
  change ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map (Map.map (Rep.map f))).unop ≫
      ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map q).unop =
    S.standardFormProjectiveMeshInclusion.map (E.functor.map f).unop ≫
      ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map q).unop
  apply congrArg (fun h ↦ h ≫ ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map q).unop)
  change ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map (Map.map (Rep.map f))).unop =
    (standardFormProjectiveMeshProperty S).ι.map
      ((standardFormOppositeProjectiveShiftOrbitProjectionFunctor S p).map
        (Rep.map f)).unop
  exact standardFormUniversalOppositeProjectiveProjection_map S p (Rep.obj Q) (Rep.obj Q') (Rep.map f)


end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
