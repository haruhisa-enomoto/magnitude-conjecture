import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalLocalRepresentationFinite
import MagnitudeConjecture.CategoryTheory.MeshProjectiveDetection
import MagnitudeConjecture.CategoryTheory.RepresentableDeckShift

/-!
# Universal restricted-Yoneda comparison

Projective detection gives faithfulness of the universal restricted-Yoneda
realization.  Deck-shift compatibility and skeletal push-down compare its
indecomposables and Hom spaces with the downstairs standard-form category.
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

local instance standardFormUniversalDirectedQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormUniversalDirectedArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- A lifted projective vertex detects every nonzero morphism in the raw
universal mesh category. -/
theorem exists_standardFormUniversal_projective_precomposition_ne_zero
    (p : Fin S.n) {X Y : SourceCategory S p} (f : X ⟶ Y) (hf : f ≠ 0) :
    ∃ (P : StandardFormProjectiveSourceCategory S p)
      (g : (standardFormProjectiveProperty S p).ι.obj P ⟶ X),
      g ≫ f ≠ 0 := by
  classical
  let F := meshProjection S p
  let hF :=
    MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
      S.standardFormRightMeshData p (k := k)
  let f₀ := F.map f
  have hFf : f₀ ≠ 0 := by
    exact fun hzero ↦ hf (hF.map_injective X Y (by simpa using hzero))
  let x : Fin S.n := LinearPathCategory.vertex (F.obj X).as
  let y : Fin S.n := LinearPathCategory.vertex (F.obj Y).as
  change
    MeshCategory.obj (k := k) S.standardFormRightMeshData x ⟶
      MeshCategory.obj (k := k) S.standardFormRightMeshData y at f₀
  obtain ⟨q, hq, d, hd⟩ :=
    S.standardFormRightMeshData.exists_projective_precomposition_ne_zero
      (fun a b ↦ S.standardFormMeshHomFinite
        (MeshCategory.obj (k := k) S.standardFormRightMeshData a)
        (MeshCategory.obj (k := k) S.standardFormRightMeshData b))
      S.standardFormRiedtmannConditionB f₀ hFf
  let Q := MeshCategory.obj (k := k) S.standardFormRightMeshData q
  let a := (hF.sourceFiberHomLinearEquiv Q X).symm d
  have ha : LinearCovering.sourceFiberHomMap (k := k) F Q X a = d := by
    rw [← LinearCovering.IsCovering.sourceFiberHomLinearEquiv_apply]
    exact (hF.sourceFiberHomLinearEquiv Q X).apply_symm_apply d
  have hpost : LinearCovering.sourceFiberPostcomp (k := k) F Q f a ≠ 0 := by
    intro hzero
    apply hd
    rw [← ha]
    change
      LinearCovering.sourceFiberHomMap (k := k) F Q X a ≫ F.map f = 0
    rw [← LinearCovering.sourceFiberHomMap_sourceFiberPostcomp
      (k := k) F Q f a]
    rw [hzero, map_zero]
  obtain ⟨V, hV⟩ : ∃ V : LinearCovering.Fiber F Q,
      a V ≫ f ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hpost
    apply DirectSum.ext_component k
    intro V
    change
      LinearCovering.sourceFiberPostcomp (k := k) F Q f a V = 0
    rw [LinearCovering.sourceFiberPostcomp_apply]
    exact hnone V
  have hVprojective : standardFormProjectiveProperty S p V.1 := by
    change standardFormProjectiveMeshProperty S (F.obj V.1)
    rw [V.2]
    exact (S.mem_standardFormProjectiveSet_iff q).mp hq
  exact ⟨⟨V.1, hVprojective⟩, a V, hV⟩

/-- The universal restricted Yoneda realization is faithful. -/
theorem standardFormUniversalRestrictedYonedaFunctor_faithful
    (p : Fin S.n) :
    (standardFormUniversalRestrictedYonedaFunctor S p).Faithful := by
  apply
    CoveringHom.finiteSupportRestrictedLinearYonedaFunctor_faithful_of_sourceDetection
  intro X Y f hf
  exact exists_standardFormUniversal_projective_precomposition_ne_zero
    S p f hf

/-- Deck translation of a universal restricted representable is represented
by the same deck translation of its ambient universal-mesh object. -/
noncomputable def standardFormUniversalRestrictedYonedaShiftIso
    (p : Fin S.n)
    (a : Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData p))
    (X : SourceCategory S p) :
    let DAmbient :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData p (k := k)
    let DProjectiveOpposite := standardFormOppositeProjectiveDeckShift S p
    letI := DProjectiveOpposite.finiteDimensionalModuleCategoryHasShift
      (k := k)
    ((standardFormUniversalRestrictedYonedaFunctor S p).obj X)⟦a⟧ ≅
      (standardFormUniversalRestrictedYonedaFunctor S p).obj
        ((DAmbient.core.F a).obj X) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let DProjectiveOpposite := standardFormOppositeProjectiveDeckShift S p
  let DAmbientOpposite := DAmbient.op
  let J := (standardFormProjectiveProperty S p).ι
  let F : CategoryTheory.Functor
      (StandardFormProjectiveSourceCategory S p)ᵒᵖ
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
  letI := CoveringHom.linearModuleCategoryHasShift
    (k := k) DProjectiveOpposite.core
  letI := DProjectiveOpposite.isFiniteDimensionalModule_stableUnderShift
    (k := k)
  letI := DProjectiveOpposite.finiteDimensionalModuleCategoryHasShift
    (k := k)
  apply ObjectProperty.isoMk
  exact DProjectiveOpposite.finiteDimensionalModuleShiftUnderlyingIso
      (k := k) ((standardFormUniversalRestrictedYonedaFunctor S p).obj X) a ≪≫
    (shiftFunctor
      (CoveringHom.LinearModuleCategory
        (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k) a).mapIso
      (standardFormUniversalRestrictedYonedaAmbientOppositeLinearModuleIso
        S p X) ≪≫
    DProjectiveOpposite.linearCoyonedaRestrictionShiftIso
      (k := k) DAmbientOpposite F inferInstance a (Opposite.op X) ≪≫
    (standardFormUniversalRestrictedYonedaAmbientOppositeLinearModuleIso
      S p ((DAmbient.core.F a).obj X)).symm

/-- Every indecomposable finite module is represented by an object of the
universal mesh category, not merely by a formal translate of a chosen
prototype. -/
theorem exists_standardFormUniversalRestrictedYoneda_iso
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (M : CoveringHom.FiniteDimensionalModuleCategory
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k)
    (hM : Indecomposable M) :
    ∃ X : SourceCategory S p, Nonempty
      ((standardFormUniversalRestrictedYonedaFunctor S p).obj X ≅ M) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData p (k := k)
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := CoveringHom.isLinearModule_stableUnderShift (k := k) D.core
  letI := CoveringHom.linearModuleCategoryHasShift (k := k) D.core
  letI := CoveringHom.linearModuleCategoryAdditiveShift (R := k) D.core
  letI := CoveringHom.linearModuleCategoryLinearShift (R := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  obtain ⟨i, g, ⟨e⟩⟩ :=
    exists_standardFormUniversalRestrictedYonedaPrototype_shift_iso
      S p hconnected M hM
  let X₀ := standardFormUniversalLiftObject S p hconnected i
  let a := Additive.ofMul g
  let X := (DAmbient.core.F a).obj X₀
  refine ⟨X, ⟨?_⟩⟩
  exact (standardFormUniversalRestrictedYonedaShiftIso S p a X₀).symm ≪≫ e

/-- Finite-module form of the comparison between push-down of universal
restricted Yoneda and downstairs restricted Yoneda. -/
noncomputable def
    standardFormUniversalRestrictedYonedaPushdownDownstairsIso
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (X : SourceCategory S p) :
    let D := standardFormOppositeProjectiveDeckShift S p
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        ((standardFormUniversalRestrictedYonedaFunctor S p).obj X) ≅
      (standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence
        S p hconnected).functor.obj
          ((S.standardFormRestrictedYonedaFunctor
            S.standardFormMeshHomFinite).obj ((meshProjection S p).obj X)) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let U := (standardFormUniversalRestrictedYonedaFunctor S p).obj X
  let R := (S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite).obj ((meshProjection S p).obj X)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let EF := standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence
    S p hconnected
  let E := standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
    S p hconnected
  let eRaw :=
    standardFormUniversalRestrictedYonedaOrbitSkeletonPushdownDownstairsIso
      S p hconnected X
  have eRaw' : (P.obj U).obj.obj ≅ (EF.functor.obj R).obj.obj := by
    change CoveringHom.orbitSkeletonPushdown (G := G)
        (CoveringHom.restrictedLinearYoneda
          (k := k) (standardFormProjectiveProperty S p).ι X) ≅
      E.functor ⋙ R.obj.obj
    exact eRaw
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ eRaw')

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

