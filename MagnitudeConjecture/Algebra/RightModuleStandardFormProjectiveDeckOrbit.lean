import MagnitudeConjecture.Algebra.RightModuleStandardFormOppositeProjectiveCover

/-!
# The projective strict deck orbit of the standard-form cover

The non-opposite projective source category already descends to the indexed
projective mesh category through its shift-orbit presentation.  This file
restricts that equivalence to one representative of every strict deck orbit
and proves that its object map is literally bijective.  It is the left-module
counterpart of the opposite-projective identification used by the
standard-form algebra.
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

local instance standardFormProjectiveDeckOrbitQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormProjectiveDeckOrbitArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

private abbrev ProjectiveGroup (x₀ : Fin S.n) :=
  MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀

/-- The strict projective deck-orbit skeleton is equivalent to the indexed
projective mesh category. -/
noncomputable def standardFormProjectiveIndexedDeckOrbitEquivalence
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringHom.DeckOrbitSkeleton
        (StandardFormProjectiveSourceCategory S x₀)
        (ProjectiveGroup S x₀) ≌
      S.StandardFormProjectiveMeshCategory := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact D.deckOrbitSkeletonEquivalence.trans
    (standardFormProjectiveIndexedShiftOrbitEquivalence S x₀ hconnected)

noncomputable instance
    standardFormProjectiveIndexedDeckOrbitEquivalence_functor_additive
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormProjectiveIndexedDeckOrbitEquivalence
      S x₀ hconnected).functor.Additive := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let eRep := D.deckOrbitSkeletonEquivalence
  let eTarget := standardFormProjectiveIndexedShiftOrbitEquivalence
    S x₀ hconnected
  letI : eRep.functor.Additive :=
    CoveringHom.CoherentDeckShift.deckOrbitSkeletonEquivalence_functor_additive D
  letI : eTarget.functor.Additive := by
    change (standardFormProjectiveShiftOrbitProjectionFunctor S x₀ ⋙
      standardFormProjectiveMeshReindex S).Additive
    infer_instance
  change (eRep.functor ⋙ eTarget.functor).Additive
  constructor
  intro X Y f g
  change eTarget.functor.map (eRep.functor.map (f + g)) = _
  rw [eRep.functor.map_add, eTarget.functor.map_add]
  rfl

noncomputable instance
    standardFormProjectiveIndexedDeckOrbitEquivalence_functor_linear
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormProjectiveIndexedDeckOrbitEquivalence
      S x₀ hconnected).functor.Linear k := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let eRep := D.deckOrbitSkeletonEquivalence
  let eTarget := standardFormProjectiveIndexedShiftOrbitEquivalence
    S x₀ hconnected
  letI : eRep.functor.Linear k :=
    CoveringHom.CoherentDeckShift.deckOrbitSkeletonEquivalence_functor_linear D
  letI : eTarget.functor.Linear k := by
    change (standardFormProjectiveShiftOrbitProjectionFunctor S x₀ ⋙
      standardFormProjectiveMeshReindex S).Linear k
    infer_instance
  change (eRep.functor ⋙ eTarget.functor).Linear k
  constructor
  intro X Y f r
  change eTarget.functor.map (eRep.functor.map (r • f)) = _
  rw [eRep.functor.map_smul, eTarget.functor.map_smul]
  rfl

@[simp]
theorem standardFormProjectiveIndexedDeckOrbitEquivalence_functor_obj
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀)
    (Q : MulAction.orbitRel.Quotient (ProjectiveGroup S x₀)
      (StandardFormProjectiveSourceCategory S x₀)) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormProjectiveIndexedDeckOrbitEquivalence
      S x₀ hconnected).functor.obj Q =
      (standardFormProjectiveMeshReindex S).obj
        ((standardFormProjectiveMeshFullProjection S x₀).obj
          (CoveringHom.deckOrbitRepresentative
            (C := StandardFormProjectiveSourceCategory S x₀)
            (G := ProjectiveGroup S x₀) Q)) := by
  rfl

/-- Distinct strict deck orbits have distinct indexed projective images. -/
theorem standardFormProjectiveIndexedDeckOrbitEquivalence_obj_injective
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Injective
      (standardFormProjectiveIndexedDeckOrbitEquivalence
        S x₀ hconnected).functor.obj := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only
  intro Q R hQR
  let X := CoveringHom.deckOrbitRepresentative
    (C := StandardFormProjectiveSourceCategory S x₀)
    (G := ProjectiveGroup S x₀) Q
  let Y := CoveringHom.deckOrbitRepresentative
    (C := StandardFormProjectiveSourceCategory S x₀)
    (G := ProjectiveGroup S x₀) R
  let F := standardFormProjectiveMeshFullProjection S x₀
  have hReindex :
      (standardFormProjectiveMeshReindex S).obj (F.obj X) =
        (standardFormProjectiveMeshReindex S).obj (F.obj Y) := by
    simpa only [
      standardFormProjectiveIndexedDeckOrbitEquivalence_functor_obj] using hQR
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
  have hOrbitYX :
      (Quotient.mk'' Y : MulAction.orbitRel.Quotient
        (ProjectiveGroup S x₀) (StandardFormProjectiveSourceCategory S x₀)) =
        Quotient.mk'' X := by
    apply Quotient.sound'
    rw [MulAction.orbitRel_apply]
    exact ⟨a.toMul⁻¹, hSmul⟩
  exact
    (CoveringHom.deckOrbitRepresentative_mk
      (C := StandardFormProjectiveSourceCategory S x₀)
      (G := ProjectiveGroup S x₀) Q).symm |>.trans <|
      hOrbitYX.symm.trans <|
        CoveringHom.deckOrbitRepresentative_mk
          (C := StandardFormProjectiveSourceCategory S x₀)
          (G := ProjectiveGroup S x₀) R

/-- Every indexed projective mesh vertex is the literal image of a strict
deck orbit. -/
theorem standardFormProjectiveIndexedDeckOrbitEquivalence_obj_surjective
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Surjective
      (standardFormProjectiveIndexedDeckOrbitEquivalence
        S x₀ hconnected).functor.obj := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  dsimp only
  let E := standardFormProjectiveIndexedDeckOrbitEquivalence
    S x₀ hconnected
  intro Y
  obtain ⟨X, ⟨e⟩⟩ := (inferInstance : E.functor.EssSurj).mem_essImage Y
  exact ⟨X, S.standardFormProjectiveMeshCategorySkeletal ⟨e⟩⟩

/-- The non-opposite projective strict-orbit equivalence has a literally
bijective object map. -/
theorem standardFormProjectiveIndexedDeckOrbitEquivalence_obj_bijective
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Bijective
      (standardFormProjectiveIndexedDeckOrbitEquivalence
        S x₀ hconnected).functor.obj := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact
    ⟨standardFormProjectiveIndexedDeckOrbitEquivalence_obj_injective
        S x₀ hconnected,
      standardFormProjectiveIndexedDeckOrbitEquivalence_obj_surjective
        S x₀ hconnected⟩

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
