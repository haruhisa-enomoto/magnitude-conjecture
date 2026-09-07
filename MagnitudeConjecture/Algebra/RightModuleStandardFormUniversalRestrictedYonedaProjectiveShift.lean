import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalRestrictedYonedaOriginalHom

/-!
# Compatibility of the universal projective shift with projection
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

local instance standardFormUniversalProjectiveShiftQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalProjectiveShiftArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

set_option backward.isDefEq.respectTransparency false in
/-- The inverse shift comparison on the lifted-projective inclusion agrees
with the equality transport used by the two covering projections. -/
theorem standardFormUniversalProjectiveInclusion_shift_inv_comp_projection
    (p : Fin S.n)
    (Y : (StandardFormProjectiveSourceCategory S p)ᵒᵖ)
    (a : Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p)) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let DAmbient :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    let H := standardFormProjectiveInvariantData S p
    let DOriginal := standardFormProjectiveDeckShift S p
    let J := (standardFormProjectiveProperty S p).ι
    letI := H.isStableUnderShift
    letI := DOriginal.hasShift
    letI := DAmbient.hasShift
    letI : J.CommShift (Additive G) := H.inclusionCommShift
    eqToHom
          (MeshCategory.RightMeshData.UniversalCover.deckShiftTargetFiberEquiv
            S.standardFormRightMeshData p (k := k) Y.unop.obj a).2.symm ≫
        (meshProjection S p).map ((J.commShiftIso a).inv.app Y.unop) =
      (standardFormProjectiveMeshProperty S).ι.map
        (eqToHom
          (standardFormProjectiveDeckShiftFiber S p Y.unop a).2.symm) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let H := standardFormProjectiveInvariantData S p
  let DOriginal := standardFormProjectiveDeckShift S p
  let J := (standardFormProjectiveProperty S p).ι
  letI := H.isStableUnderShift
  letI := DOriginal.hasShift
  letI := DAmbient.hasShift
  letI : J.CommShift (Additive G) := H.inclusionCommShift
  dsimp only
  let hShift :
      ((@shiftFunctor (StandardFormProjectiveSourceCategory S p)
        (Additive G) _ _ DOriginal.hasShift a).obj Y.unop).obj =
        (@shiftFunctor (SourceCategory S p) (Additive G) _ _
          DAmbient.hasShift a).obj Y.unop.obj := by
    have hshift : DOriginal.hasShift =
        ObjectProperty.hasShift (standardFormProjectiveProperty S p) :=
      H.hasShift_eq
    rw [hshift]
    unfold ObjectProperty.hasShift
    rfl
  have hinv :
      (J.commShiftIso a).inv.app Y.unop = eqToHom hShift.symm := by
    rw [← cancel_epi ((J.commShiftIso a).hom.app Y.unop)]
    rw [(J.commShiftIso a).hom_inv_id_app,
      H.inclusionCommShift_hom_app]
    rw [eqToHom_trans]
    rfl
  rw [hinv, eqToHom_map, eqToHom_map]
  rw [eqToHom_trans]

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
