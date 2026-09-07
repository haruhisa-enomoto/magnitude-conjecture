import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalRestrictedYonedaProjectiveProjection

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

local instance standardFormUniversalRestrictedYonedaDownstairsQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalRestrictedYonedaDownstairsArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

noncomputable def standardFormUniversalOrbitRepresentableDownstairsRestrictedYonedaValueLinearEquiv
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X : SourceCategory S p)
    (Q : MulAction.orbitRel.Quotient
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p)
      (StandardFormProjectiveSourceCategory S p)ᵒᵖ) :
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
    ((Rep ⋙ Map ⋙ R).obj Q) ≃ₗ[k] ((E.functor ⋙ N.obj.obj).obj Q) := by
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
  exact standardFormUniversalOppositeShiftOrbitOriginalHomLinearEquiv S p (Opposite.op X) (F.obj (Rep.obj Q))


end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
