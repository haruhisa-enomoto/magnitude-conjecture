import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalRestrictedYonedaDownstairsIso

/-! # Descent of universal restricted Yoneda -/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalRestrictedYonedaDownstairsFinalQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalRestrictedYonedaDownstairsFinalArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- Skeletal pushdown of universal restricted Yoneda is naturally the
downstairs restricted Yoneda module of the projected object. -/
noncomputable def
    standardFormUniversalRestrictedYonedaOrbitSkeletonPushdownDownstairsIso
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
    let E := standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
      S p hconnected
    let N := (S.standardFormRestrictedYonedaFunctor
      S.standardFormMeshHomFinite).obj ((meshProjection S p).obj X)
    CoveringHom.orbitSkeletonPushdown (G := G)
        (CoveringHom.restrictedLinearYoneda (k := k) J X) ≅
      E.functor ⋙ N.obj.obj := by
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
  exact
    standardFormUniversalRestrictedYonedaOrbitSkeletonPushdownRepresentableIso
        S p X ≪≫
      Classical.choice
        (standardFormUniversalOrbitRepresentableDownstairsRestrictedYonedaIsoNonempty
          S p hconnected X)

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
