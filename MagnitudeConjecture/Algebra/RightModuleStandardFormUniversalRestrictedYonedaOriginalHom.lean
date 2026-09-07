import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalRestrictedYonedaOrbitProjection

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

local instance standardFormUniversalRestrictedYonedaProjectiveProjectionQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance
    standardFormUniversalRestrictedYonedaProjectiveProjectionArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- Unopposed form of the ambient opposite shift-orbit Hom equivalence. -/
noncomputable def standardFormUniversalOppositeShiftOrbitOriginalHomLinearEquiv (p : Fin S.n)
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
      ((meshProjection S p).obj Y.unop ⟶
        (meshProjection S p).obj X.unop) := by
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
  exact (standardFormUniversalOppositeShiftOrbitSourceFiberLinearEquiv S p X Y).trans
    ((MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
      S.standardFormRightMeshData p (k := k)).sourceFiberHomLinearEquiv
        (F.obj Y.unop) X.unop)

set_option backward.isDefEq.respectTransparency false in
/-- The unopposed Hom equivalence is the unop of the descended projection map. -/
@[simp]
theorem standardFormUniversalOppositeShiftOrbitOriginalHomLinearEquiv_apply
    (p : Fin S.n)
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
    standardFormUniversalOppositeShiftOrbitOriginalHomLinearEquiv S p X Y f = ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map f).unop := by
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
  have h := congrArg Quiver.Hom.unop (standardFormUniversalOppositeShiftOrbitHomLinearEquiv_apply S p X Y f)
  dsimp only [standardFormUniversalOppositeShiftOrbitHomLinearEquiv, standardFormUniversalOppositeShiftOrbitOriginalHomLinearEquiv, LinearEquiv.trans_apply] at h
  change standardFormUniversalOppositeShiftOrbitOriginalHomLinearEquiv S p X Y f = ((standardFormUniversalOppositeShiftOrbitProjectionFunctor S p).map f).unop at h
  exact h


end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
