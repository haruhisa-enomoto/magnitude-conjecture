import MagnitudeConjecture.Algebra.RightModuleStandardFormRecovery
import MagnitudeConjecture.Algebra.RightModuleStandardFormUniversalRestrictedYoneda
import MagnitudeConjecture.CategoryTheory.DeckOrbitTowerModuleEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraEquivalence
import MagnitudeConjecture.CategoryTheory.FiniteOrbitLocalRepresentationFinite
import MagnitudeConjecture.CategoryTheory.FiniteOrbitPushdownReflectsOrbits
import MagnitudeConjecture.CategoryTheory.IrreducibleFiniteCoreFunctor

/-!
# Local representation-finiteness of the universal standard-form cover

Choose one universal lift of each vertex of the finite standard mesh and
restrict its representable to the lifted projective vertices.  These finitely
many modules form orbit representatives for all indecomposable finite modules
upstairs: decompose a push-down downstairs, recover each summand by restricted
Yoneda, lift the resulting push-down isomorphism, and isolate one shifted
summand by the local-ring and Krull--Schmidt argument.

Since every prototype has finite support and the deck action on objects is
free, only finitely many of its translates can be nonzero at a fixed object.
This proves the manuscript's local representation-finiteness clause without
using torsion-freeness of the fundamental group.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalLocalRepQuiverInstance :
    Quiver (Fin S.n) := S.standardFormQuiver

noncomputable local instance standardFormUniversalLocalRepArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The vertex label underlying an arbitrary raw standard-mesh object. -/
def standardFormMeshObjectLabel (X : S.StandardFormMeshCategory) : Fin S.n :=
  LinearPathCategory.vertex X.as

theorem standardFormMeshObject_eq_obj_label
    (X : S.StandardFormMeshCategory) :
    X = MeshCategory.obj (k := k) S.standardFormRightMeshData
      (standardFormMeshObjectLabel S X) := by
  apply CategoryTheory.Quotient.ext
  rfl

/-- A chosen universal-cover vertex above each finite standard-form mesh
vertex. -/
noncomputable def standardFormUniversalLiftVertex
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (i : Fin S.n) :
    MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData p :=
  Classical.choose
    (MeshCategory.RightMeshData.UniversalCover.vertex_surjective
      S.standardFormRightMeshData p hconnected i)

@[simp]
theorem standardFormUniversalLiftVertex_vertex
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (i : Fin S.n) :
    (standardFormUniversalLiftVertex S p hconnected i).1 = i :=
  Classical.choose_spec
    (MeshCategory.RightMeshData.UniversalCover.vertex_surjective
      S.standardFormRightMeshData p hconnected i)

/-- The chosen lift as an object of the universal mesh category. -/
noncomputable def standardFormUniversalLiftObject
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (i : Fin S.n) : SourceCategory S p :=
  MeshCategory.obj (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData p)
    (standardFormUniversalLiftVertex S p hconnected i)

@[simp]
theorem standardFormUniversalLiftObject_projection
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (i : Fin S.n) :
    (meshProjection S p).obj
        (standardFormUniversalLiftObject S p hconnected i) =
      MeshCategory.obj (k := k) S.standardFormRightMeshData i := by
  apply CategoryTheory.Quotient.ext
  exact standardFormUniversalLiftVertex_vertex S p hconnected i

/-- The finite family of universal restricted-Yoneda modules obtained from
the chosen lifts of all downstairs mesh vertices. -/
noncomputable def standardFormUniversalRestrictedYonedaPrototype
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (i : Fin S.n) :
    CoveringHom.FiniteDimensionalModuleCategory
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k :=
  (standardFormUniversalRestrictedYonedaFunctor S p).obj
    (standardFormUniversalLiftObject S p hconnected i)

/-- Change of base along the indexed deck-orbit equivalence, on finite
modules. -/
noncomputable def
    standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
    let D := standardFormOppositeProjectiveDeckShift S p
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    S.StandardFormProjectiveVertexModuleCategory (k := k) ≌
      CoveringHom.FiniteDimensionalModuleCategory
        (C := CoveringHom.DeckOrbitSkeleton
          (StandardFormProjectiveSourceCategory S p)ᵒᵖ G) k := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let E := standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
    S p hconnected
  let Eobj := standardFormOppositeProjectiveIndexedDeckOrbitObjectEquiv
    S p hconnected
  exact CoveringHom.finiteDimensionalModuleCongrEquivalence
    (k := k) E Eobj
      (standardFormOppositeProjectiveIndexedDeckOrbitObjectEquiv_apply
        S p hconnected)

/-- Push-down of a chosen universal restricted-Yoneda prototype is the
change-of-base image of the corresponding downstairs restricted-Yoneda
module. -/
noncomputable def standardFormUniversalRestrictedYonedaPrototypePushdownIso
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (i : Fin S.n) :
    let D := standardFormOppositeProjectiveDeckShift S p
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)).obj
        (standardFormUniversalRestrictedYonedaPrototype S p hconnected i) ≅
      (standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence
        S p hconnected).functor.obj
          ((S.standardFormRestrictedYonedaFunctor
            S.standardFormMeshHomFinite).obj
              (MeshCategory.obj (k := k) S.standardFormRightMeshData i)) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let U := standardFormUniversalRestrictedYonedaPrototype
    S p hconnected i
  let R := (S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite).obj
      (MeshCategory.obj (k := k) S.standardFormRightMeshData i)
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let EF := standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence
    S p hconnected
  let E := standardFormOppositeProjectiveIndexedDeckOrbitEquivalence
    S p hconnected
  let eRaw :=
    standardFormUniversalRestrictedYonedaOrbitSkeletonPushdownDownstairsIso
      S p hconnected (standardFormUniversalLiftObject S p hconnected i)
  have eRaw' : (P.obj U).obj.obj ≅ (EF.functor.obj R).obj.obj := by
    change CoveringHom.orbitSkeletonPushdown (G := G)
        (CoveringHom.restrictedLinearYoneda
          (k := k) (standardFormProjectiveProperty S p).ι
            (standardFormUniversalLiftObject S p hconnected i)) ≅
      E.functor ⋙ R.obj.obj
    simpa only [R, standardFormUniversalLiftObject_projection] using eRaw
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ eRaw')

/-- Every chosen universal restricted-Yoneda prototype is indecomposable. -/
theorem standardFormUniversalRestrictedYonedaPrototype_indecomposable
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (i : Fin S.n) :
    Indecomposable
      (standardFormUniversalRestrictedYonedaPrototype S p hconnected i) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let R := (S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite).obj
      (MeshCategory.obj (k := k) S.standardFormRightMeshData i)
  let Y := S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite
  letI : Y.Faithful := S.standardFormRestrictedYonedaFunctor_faithful
  letI : Y.Linear k := by
    dsimp only [Y, standardFormRestrictedYonedaFunctor]
    infer_instance
  let EF := standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence
    S p hconnected
  letI : EF.functor.Additive := by
    dsimp only [EF,
      standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence]
    infer_instance
  have hlocalX : IsLocalRing
      (End (MeshCategory.obj (k := k) S.standardFormRightMeshData i)) := by
    letI : FiniteDimensional k
        (End (MeshCategory.obj (k := k) S.standardFormRightMeshData i)) :=
      S.standardFormMeshHomFinite _ _
    exact MeshCategory.end_isLocalRing_of_finiteDimensional
      S.standardFormRightMeshData i
  have hlocalR : IsLocalRing (End R) := by
    letI : IsLocalRing
        (End (MeshCategory.obj (k := k) S.standardFormRightMeshData i)) :=
      hlocalX
    exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm
      (MagnitudeConjecture.CategoryTheory.Functor.endAlgEquivOfFullyFaithful
        (k := k)
        (S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite)
        (MeshCategory.obj (k := k) S.standardFormRightMeshData i)).toRingEquiv
  have hR : Indecomposable R := by
    letI : IsLocalRing (End R) := hlocalR
    exact MagnitudeConjecture.CategoryTheory.indecomposable_of_local_end _
  have hEFR : Indecomposable (EF.functor.obj R) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      EF.functor R).mpr hR
  let U := standardFormUniversalRestrictedYonedaPrototype S p hconnected i
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let e := standardFormUniversalRestrictedYonedaPrototypePushdownIso
    S p hconnected i
  have hPU : Indecomposable (P.obj U) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).mpr hEFR
  letI : P.Faithful :=
    D.finiteDimensionalModuleOrbitSkeletonPushdown_faithful (k := k)
  exact MagnitudeConjecture.indecomposable_of_faithful_additive P U hPU

/-- Every indecomposable finite module on the lifted projective category is
a deck translate of one of the chosen universal restricted-Yoneda
prototypes. -/
theorem exists_standardFormUniversalRestrictedYonedaPrototype_shift_iso
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p)
    (M : CoveringHom.FiniteDimensionalModuleCategory
      (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) k)
    (hM : Indecomposable M) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData p
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
    ∃ i : Fin S.n, ∃ g : G, Nonempty
      (standardFormUniversalRestrictedYonedaPrototype
        S p hconnected i⟦Additive.ofMul g⟧ ≅ M) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData p
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
  let P := D.finiteDimensionalModuleOrbitSkeletonPushdown (k := k)
  let EF := standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence
    S p hconnected
  let Y := S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite
  letI : Y.Faithful := S.standardFormRestrictedYonedaFunctor_faithful
  letI : EF.functor.Additive := by
    dsimp only [EF,
      standardFormOppositeProjectiveIndexedDeckOrbitModuleEquivalence]
    infer_instance
  letI : EF.inverse.Additive := by
    infer_instance
  obtain ⟨d⟩ := CoveringHom.finiteDimensionalModule_finiteIndecomposableDecomposition
    (P.obj M)
  let Q (j : Fin d.n) := EF.inverse.obj (d.summand j)
  have hQ (j : Fin d.n) : Indecomposable (Q j) :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
      EF.inverse (d.summand j)).mpr (d.indecomposable j)
  choose X eX using fun j ↦
    S.standardFormRestrictedYonedaFunctor_indec_dense
      (k := k) (Q j) (hQ j)
  let label (j : Fin d.n) : Fin S.n := standardFormMeshObjectLabel S (X j)
  let L (j : Fin d.n) :=
    standardFormUniversalRestrictedYonedaPrototype S p hconnected (label j)
  have hL (j : Fin d.n) : Indecomposable (L j) :=
    standardFormUniversalRestrictedYonedaPrototype_indecomposable
      S p hconnected (label j)
  have eL (j : Fin d.n) : P.obj (L j) ≅ d.summand j := by
    let eProto :=
      standardFormUniversalRestrictedYonedaPrototypePushdownIso
        S p hconnected (label j)
    let eLabel :
        Y.obj (MeshCategory.obj (k := k) S.standardFormRightMeshData
          (label j)) ≅ Y.obj (X j) :=
      Y.mapIso (eqToIso (standardFormMeshObject_eq_obj_label S (X j)).symm)
    exact eProto ≪≫ EF.functor.mapIso eLabel ≪≫
      EF.functor.mapIso (Classical.choice (eX j)) ≪≫
        EF.counitIso.app (d.summand j)
  let ePush : P.obj M ≅ P.obj (⨁ L) :=
    d.isoBiproduct ≪≫
      biproduct.mapIso (fun j ↦ (eL j).symm) ≪≫
        (P.mapBiproduct L).symm
  obtain ⟨a, j, ⟨eMj⟩⟩ :=
    D.exists_shift_iso_finBiproduct_component_of_pushdown_iso
      (k := k) M hM d.n L hL ⟨ePush⟩
  exact ⟨label j, a.toMul, ⟨eMj.symm⟩⟩

/-- The opposite lifted-projective category in the universal standard-form
cover is locally representation-finite. -/
theorem standardFormOppositeProjectiveSourceCategoryIsLocallyRepresentationFinite
    (p : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData p) :
    CoveringHom.IsLocallyRepresentationFinite
      (k := k) (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) := by
  let D := standardFormOppositeProjectiveDeckShift S p
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := CoveringHom.isLinearModule_stableUnderShift (k := k) D.core
  letI := CoveringHom.linearModuleCategoryHasShift (k := k) D.core
  letI := D.isFiniteDimensionalModule_stableUnderShift (k := k)
  letI := D.finiteDimensionalModuleCategoryHasShift (k := k)
  letI := D.finiteDimensionalModuleCategoryAdditiveShift (k := k)
  apply D.isLocallyRepresentationFinite_of_finite_shift_orbit_representatives
    (k := k) S.n
    (standardFormUniversalRestrictedYonedaPrototype S p hconnected)
    (standardFormUniversalRestrictedYonedaPrototype_indecomposable
      S p hconnected)
  intro M hM
  exact exists_standardFormUniversalRestrictedYonedaPrototype_shift_iso
    S p hconnected M hM

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
