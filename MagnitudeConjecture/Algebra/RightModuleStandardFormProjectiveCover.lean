import MagnitudeConjecture.Algebra.RightModuleStandardFormRiedtmann
import MagnitudeConjecture.CategoryTheory.FullSubcategoryLinearCovering
import MagnitudeConjecture.CategoryTheory.InvariantFullSubcategoryDeckShift

/-!
# The projective part of the standard-form universal mesh cover

The standard-form algebra is the category algebra of the projective full
subcategory of the finite mesh category.  This file isolates its inverse
image in the universal mesh category and restricts the fundamental-group deck
action to that full subcategory.
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

local instance standardFormProjectiveCoverQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormProjectiveCoverArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

namespace UniversalCover

/-- The projective objects inside the downstairs standard-form mesh
category. -/
def standardFormProjectiveMeshProperty :
    ObjectProperty S.StandardFormMeshCategory :=
  fun X ↦ Projective
    (S.fgObj (MagnitudeConjecture.LinearPathCategory.vertex X.as))

/-- The literal full-subcategory presentation of the projective part of the
downstairs mesh category. -/
abbrev StandardFormProjectiveMeshFullSubcategory :=
  (standardFormProjectiveMeshProperty S).FullSubcategory

/-- A universal-mesh object lies over a projective vertex when its downstairs
label represents a projective indecomposable module. -/
def standardFormProjectiveProperty (x₀ : Fin S.n) :
    ObjectProperty (SourceCategory S x₀) :=
  LinearCovering.pullbackProperty (meshProjection S x₀)
    (standardFormProjectiveMeshProperty S)

/-- The full subcategory of the universal mesh category on the lifts of
projective vertices. -/
abbrev StandardFormProjectiveSourceCategory (x₀ : Fin S.n) :=
  (standardFormProjectiveProperty S x₀).FullSubcategory

/-- Both the fundamental-group action and its chosen shift functors preserve
the property of lying over a projective vertex. -/
theorem standardFormProjectiveInvariantData (x₀ : Fin S.n) :
    let D :=
      MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
        S.standardFormRightMeshData x₀ (k := k)
    CoveringHom.CoherentDeckShift.InvariantFullSubcategoryData D
      (standardFormProjectiveProperty S x₀) := by
  let D :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData x₀ (k := k)
  exact
    { smul_mem := by
        intro g X hX
        change Projective
          (S.fgObj (MagnitudeConjecture.LinearPathCategory.vertex X.as).1)
        exact hX
      shift_mem := by
        intro a X hX
        change Projective
          (S.fgObj (MagnitudeConjecture.LinearPathCategory.vertex X.as).1)
        exact hX }

/-- The restricted fundamental-group action on lifted projective vertices. -/
noncomputable instance standardFormProjectiveSourceCategoryMulAction
    (x₀ : Fin S.n) :
    MulAction
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀)
      (StandardFormProjectiveSourceCategory S x₀) :=
  (standardFormProjectiveInvariantData S x₀).mulAction

/-- The restricted deck action remains free. -/
noncomputable instance standardFormProjectiveSourceCategoryIsCancelSMul
    (x₀ : Fin S.n) :
    IsCancelSMul
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀)
      (StandardFormProjectiveSourceCategory S x₀) :=
  (standardFormProjectiveInvariantData S x₀).isCancelSMul

/-- The coherent fundamental-group deck shift restricted to the lifted
projective full subcategory. -/
noncomputable def standardFormProjectiveDeckShift (x₀ : Fin S.n) :
    CoveringHom.CoherentDeckShift
      (StandardFormProjectiveSourceCategory S x₀)
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀) :=
  (standardFormProjectiveInvariantData S x₀).coherentDeckShift

noncomputable instance standardFormProjectiveDeckShift_additive
    (x₀ : Fin S.n)
    (a : Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀)) :
    (((standardFormProjectiveDeckShift S x₀).core.F a).Additive) := by
  dsimp only [standardFormProjectiveDeckShift]
  infer_instance

noncomputable instance standardFormProjectiveDeckShift_linear
    (x₀ : Fin S.n)
    (a : Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀)) :
    (((standardFormProjectiveDeckShift S x₀).core.F a).Linear k) := by
  dsimp only [standardFormProjectiveDeckShift]
  infer_instance

/-- On objects, the restricted projective shift is literally the inverse
deck action dictated by the ambient universal-mesh convention. -/
theorem standardFormProjectiveShiftFunctor_obj_eq_smul
    (x₀ : Fin S.n)
    (a : Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀))
    (X : StandardFormProjectiveSourceCategory S x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    (shiftFunctor _ a).obj X = a.toMul⁻¹ • X := by
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData x₀ (k := k)
  let H := standardFormProjectiveInvariantData S x₀
  let D := standardFormProjectiveDeckShift S x₀
  letI := DAmbient.hasShift
  letI := H.isStableUnderShift
  letI := D.hasShift
  apply ObjectProperty.FullSubcategory.ext
  have hshift : D.hasShift =
      ObjectProperty.hasShift (standardFormProjectiveProperty S x₀) :=
    H.hasShift_eq
  rw [hshift]
  unfold ObjectProperty.hasShift
  change
    (MeshCategory.RightMeshData.UniversalCover.deckMeshEndofunctor
      S.standardFormRightMeshData x₀ a.toMul⁻¹ (k := k)).obj X.obj =
      a.toMul⁻¹ • X.obj
  exact
    MeshCategory.RightMeshData.UniversalCover.deckMeshEndofunctor_obj_eq_smul
      S.standardFormRightMeshData x₀ a.toMul⁻¹ (k := k) X.obj

/-- The universal mesh covering restricted to the inverse image of the
downstairs projective full subcategory. -/
noncomputable abbrev standardFormProjectiveMeshFullProjection
    (x₀ : Fin S.n) :
    StandardFormProjectiveSourceCategory S x₀ ⥤
      StandardFormProjectiveMeshFullSubcategory S :=
  LinearCovering.fullSubcategoryRestriction (meshProjection S x₀)
    (standardFormProjectiveMeshProperty S)

noncomputable instance standardFormProjectiveMeshFullProjection_additive
    (x₀ : Fin S.n) :
    (standardFormProjectiveMeshFullProjection S x₀).Additive :=
  LinearCovering.fullSubcategoryRestriction_additive
    (meshProjection S x₀) (standardFormProjectiveMeshProperty S)

noncomputable instance standardFormProjectiveMeshFullProjection_linear
    (x₀ : Fin S.n) :
    (standardFormProjectiveMeshFullProjection S x₀).Linear k :=
  LinearCovering.fullSubcategoryRestriction_linear
    (meshProjection S x₀) (standardFormProjectiveMeshProperty S)

/-- Restriction to lifted projective vertices preserves the linear-covering
property. -/
theorem standardFormProjectiveMeshFullProjection_isCovering
    (x₀ : Fin S.n) :
    LinearCovering.IsCovering (k := k)
      (standardFormProjectiveMeshFullProjection S x₀) :=
  LinearCovering.fullSubcategoryRestriction_isCovering
    (meshProjection S x₀)
    (MeshCategory.RightMeshData.UniversalCover.meshProjectionFunctor_isCovering
      S.standardFormRightMeshData x₀ (k := k))
    (standardFormProjectiveMeshProperty S)

/-- The restricted projective covering commutes with the restricted deck
shift when its downstairs projective category is trivially shifted. -/
@[implicit_reducible]
noncomputable def standardFormProjectiveMeshFullProjectionCommShift
    (x₀ : Fin S.n) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData x₀
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI : HasShift (StandardFormProjectiveMeshFullSubcategory S)
        (Additive G) :=
      CoveringHom.trivialHasShift _ _
    (standardFormProjectiveMeshFullProjection S x₀).CommShift
      (Additive G) := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData x₀ (k := k)
  let H := standardFormProjectiveInvariantData S x₀
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := DAmbient.hasShift
  letI : HasShift S.StandardFormMeshCategory (Additive G) :=
    CoveringHom.trivialHasShift _ _
  letI : HasShift (StandardFormProjectiveMeshFullSubcategory S)
      (Additive G) := CoveringHom.trivialHasShift _ _
  let sourceInclusion := (standardFormProjectiveProperty S x₀).ι
  let targetInclusion := (standardFormProjectiveMeshProperty S).ι
  let ambientProjection := meshProjection S x₀
  let restrictedProjection := standardFormProjectiveMeshFullProjection S x₀
  letI : sourceInclusion.CommShift (Additive G) :=
    H.inclusionCommShift
  letI : ambientProjection.CommShift (Additive G) :=
    MeshCategory.RightMeshData.UniversalCover.meshProjectionCommShift
      S.standardFormRightMeshData x₀ (k := k)
  letI : targetInclusion.CommShift (Additive G) :=
    CoveringHom.trivialFunctorCommShift targetInclusion
  let e : restrictedProjection ⋙ targetInclusion ≅
      sourceInclusion ⋙ ambientProjection := Iso.refl _
  exact Functor.CommShift.ofComp e (Additive G)

/-- The restricted projective covering descended to the concrete shift-orbit
category of lifted projective vertices. -/
noncomputable def standardFormProjectiveShiftOrbitProjectionFunctor
    (x₀ : Fin S.n) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData x₀
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringHom.ShiftOrbitCategory
        (StandardFormProjectiveSourceCategory S x₀) (Additive G) ⥤
      StandardFormProjectiveMeshFullSubcategory S := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData x₀ (k := k)
  let H := standardFormProjectiveInvariantData S x₀
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := DAmbient.hasShift
  letI := DAmbient.additiveShift
  letI := DAmbient.linearShift (k := k)
  let sourceInclusion := (standardFormProjectiveProperty S x₀).ι
  letI : sourceInclusion.CommShift (Additive G) :=
    H.inclusionCommShift
  let orbitInclusion := CoveringHom.shiftOrbitMapFunctor
    (k := k) (A := Additive G) sourceInclusion
  let ambientOrbitProjection :=
    MeshCategory.RightMeshData.UniversalCover.meshShiftOrbitProjectionFunctor
      S.standardFormRightMeshData x₀ (k := k)
  exact ObjectProperty.lift (standardFormProjectiveMeshProperty S)
    (orbitInclusion ⋙ ambientOrbitProjection) (fun X ↦ X.property)

noncomputable instance
    standardFormProjectiveShiftOrbitProjectionFunctor_additive
    (x₀ : Fin S.n) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    (standardFormProjectiveShiftOrbitProjectionFunctor S x₀).Additive := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  dsimp only [standardFormProjectiveShiftOrbitProjectionFunctor]
  infer_instance

noncomputable instance
    standardFormProjectiveShiftOrbitProjectionFunctor_linear
    (x₀ : Fin S.n) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormProjectiveShiftOrbitProjectionFunctor S x₀).Linear k := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData x₀ (k := k)
  let H := standardFormProjectiveInvariantData S x₀
  letI := DAmbient.hasShift
  letI := DAmbient.additiveShift
  letI := DAmbient.linearShift (k := k)
  let sourceInclusion := (standardFormProjectiveProperty S x₀).ι
  letI : sourceInclusion.CommShift
      (Additive (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀)) := H.inclusionCommShift
  let orbitInclusion := CoveringHom.shiftOrbitMapFunctor
    (k := k)
    (A := Additive
      (MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
        S.standardFormRightMeshData x₀)) sourceInclusion
  let ambientOrbitProjection :=
    MeshCategory.RightMeshData.UniversalCover.meshShiftOrbitProjectionFunctor
      S.standardFormRightMeshData x₀ (k := k)
  let M := orbitInclusion ⋙ ambientOrbitProjection
  let F := standardFormProjectiveShiftOrbitProjectionFunctor S x₀
  let J := (standardFormProjectiveMeshProperty S).ι
  let e : F ⋙ J ≅ M := Iso.refl _
  have hcomp : (F ⋙ J).Linear k := Functor.linear_of_iso k e.symm
  refine { map_smul := fun {X Y} f r ↦ ?_ }
  apply J.map_injective
  change J.map (F.map (r • f)) = J.map (r • F.map f)
  rw [J.map_smul]
  exact hcomp.map_smul f r

/-- The descended projection from the projective part of the universal deck
orbit is fully faithful. -/
noncomputable def
    standardFormProjectiveShiftOrbitProjectionFunctorFullyFaithful
    (x₀ : Fin S.n) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormProjectiveShiftOrbitProjectionFunctor S x₀).FullyFaithful := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData x₀ (k := k)
  let H := standardFormProjectiveInvariantData S x₀
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := DAmbient.hasShift
  letI := DAmbient.additiveShift
  letI := DAmbient.linearShift (k := k)
  let sourceInclusion := (standardFormProjectiveProperty S x₀).ι
  letI : sourceInclusion.CommShift (Additive G) := H.inclusionCommShift
  let orbitInclusion := CoveringHom.shiftOrbitMapFunctor
    (k := k) (A := Additive G) sourceInclusion
  let ambientOrbitProjection :=
    MeshCategory.RightMeshData.UniversalCover.meshShiftOrbitProjectionFunctor
      S.standardFormRightMeshData x₀ (k := k)
  let hAmbient :=
    MeshCategory.RightMeshData.UniversalCover.meshShiftOrbitProjectionFunctorFullyFaithful
      S.standardFormRightMeshData x₀ (k := k)
  letI : ambientOrbitProjection.Faithful := hAmbient.faithful
  letI : ambientOrbitProjection.Full := hAmbient.full
  let M := orbitInclusion ⋙ ambientOrbitProjection
  letI : M.Faithful := inferInstance
  letI : M.Full := inferInstance
  let F := standardFormProjectiveShiftOrbitProjectionFunctor S x₀
  letI : F.Faithful := by
    dsimp only [F, standardFormProjectiveShiftOrbitProjectionFunctor]
    infer_instance
  letI : F.Full := by
    dsimp only [F, standardFormProjectiveShiftOrbitProjectionFunctor]
    infer_instance
  exact Functor.FullyFaithful.ofFullyFaithful F

/-- Based connectedness makes the projective part of the descended orbit
projection surjective on objects. -/
theorem standardFormProjectiveShiftOrbitProjectionFunctor_obj_surjective
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    Function.Surjective
      (standardFormProjectiveShiftOrbitProjectionFunctor S x₀).obj := by
  let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
    S.standardFormRightMeshData x₀
  let DAmbient :=
    MeshCategory.RightMeshData.UniversalCover.deckMeshCoherentDeckShift
      S.standardFormRightMeshData x₀ (k := k)
  let H := standardFormProjectiveInvariantData S x₀
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  letI := DAmbient.hasShift
  letI := DAmbient.additiveShift
  letI := DAmbient.linearShift (k := k)
  let sourceInclusion := (standardFormProjectiveProperty S x₀).ι
  letI : sourceInclusion.CommShift (Additive G) := H.inclusionCommShift
  dsimp only
  intro Y
  obtain ⟨X, hX⟩ :=
    MeshCategory.RightMeshData.UniversalCover.meshShiftOrbitProjectionFunctor_obj_surjective
      S.standardFormRightMeshData x₀ (k := k) hconnected Y.obj
  let XSource : SourceCategory S x₀ := X
  have hXSource : (meshProjection S x₀).obj XSource = Y.obj := by
    exact hX
  have hProjective : standardFormProjectiveProperty S x₀ XSource := by
    rw [standardFormProjectiveProperty, LinearCovering.pullbackProperty]
    rw [hXSource]
    exact Y.property
  refine ⟨⟨XSource, hProjective⟩, ?_⟩
  apply ObjectProperty.FullSubcategory.ext
  exact hXSource

/-- For a connected standard-form translation quiver, the descended
projective orbit projection is an equivalence. -/
theorem standardFormProjectiveShiftOrbitProjectionFunctor_isEquivalence
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    (standardFormProjectiveShiftOrbitProjectionFunctor S x₀).IsEquivalence := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := standardFormProjectiveShiftOrbitProjectionFunctor S x₀
  let hff :=
    standardFormProjectiveShiftOrbitProjectionFunctorFullyFaithful S x₀
  exact
    { faithful := hff.faithful
      full := hff.full
      essSurj := F.essSurj_of_surj
        (standardFormProjectiveShiftOrbitProjectionFunctor_obj_surjective
          S x₀ hconnected) }

/-- The explicit equivalence between the projective part of the universal
deck orbit and the literal downstairs projective full subcategory. -/
noncomputable def standardFormProjectiveShiftOrbitEquivalence
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData x₀
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringHom.ShiftOrbitCategory
        (StandardFormProjectiveSourceCategory S x₀) (Additive G) ≌
      StandardFormProjectiveMeshFullSubcategory S := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  let F := standardFormProjectiveShiftOrbitProjectionFunctor S x₀
  letI : F.IsEquivalence :=
    standardFormProjectiveShiftOrbitProjectionFunctor_isEquivalence
      S x₀ hconnected
  exact F.asEquivalence

/-- Forget the full-subcategory object wrapper, retaining the same projective
label in the indexed projective mesh category used to define the standard
form algebra. -/
noncomputable def standardFormProjectiveMeshReindex :
    StandardFormProjectiveMeshFullSubcategory S ⥤
      S.StandardFormProjectiveMeshCategory where
  obj X :=
    ⟨MagnitudeConjecture.LinearPathCategory.vertex X.obj.as, X.property⟩
  map f := InducedCategory.homMk f.hom
  map_id X := by
    apply InducedCategory.hom_ext
    rfl
  map_comp f g := by
    apply InducedCategory.hom_ext
    rfl

noncomputable instance standardFormProjectiveMeshReindex_additive :
    (standardFormProjectiveMeshReindex S).Additive where
  map_add := by
    intro X Y f g
    apply InducedCategory.hom_ext
    rfl

noncomputable instance standardFormProjectiveMeshReindex_linear :
    (standardFormProjectiveMeshReindex S).Linear k where
  map_smul f r := by
    apply InducedCategory.hom_ext
    rfl

/-- Reindexing is bijective on every Hom space because both categories are
full subcategories of the same mesh category. -/
theorem standardFormProjectiveMeshReindex_map_bijective
    (X Y : StandardFormProjectiveMeshFullSubcategory S) :
    Function.Bijective
      ((standardFormProjectiveMeshReindex S).map :
        (X ⟶ Y) →
          ((standardFormProjectiveMeshReindex S).obj X ⟶
            (standardFormProjectiveMeshReindex S).obj Y)) := by
  constructor
  · intro f g hfg
    apply ObjectProperty.hom_ext
    exact congrArg
      (fun q : ((standardFormProjectiveMeshReindex S).obj X ⟶
        (standardFormProjectiveMeshReindex S).obj Y) ↦ q.hom) hfg
  · intro f
    exact ⟨ObjectProperty.homMk f.hom, by
      apply InducedCategory.hom_ext
      rfl⟩

/-- Every indexed projective vertex has its literal full-subcategory
representative. -/
theorem standardFormProjectiveMeshReindex_obj_surjective :
    Function.Surjective (standardFormProjectiveMeshReindex S).obj := by
  rintro X
  refine ⟨⟨MeshCategory.obj (k := k) S.standardFormRightMeshData X.1,
    X.2⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- Reindexing remembers the projective mesh vertex literally, so its object
map is injective as well as surjective. -/
theorem standardFormProjectiveMeshReindex_obj_injective :
    Function.Injective (standardFormProjectiveMeshReindex S).obj := by
  intro X Y hXY
  apply ObjectProperty.FullSubcategory.ext
  apply CategoryTheory.Quotient.ext
  exact congrArg Subtype.val hXY

/-- The full-subcategory and indexed presentations have literally bijective
object maps. -/
theorem standardFormProjectiveMeshReindex_obj_bijective :
    Function.Bijective (standardFormProjectiveMeshReindex S).obj :=
  ⟨standardFormProjectiveMeshReindex_obj_injective S,
    standardFormProjectiveMeshReindex_obj_surjective S⟩

/-- The two presentations of the downstairs projective mesh category are
linearly equivalent. -/
noncomputable def standardFormProjectiveMeshReindexEquivalence :
    StandardFormProjectiveMeshFullSubcategory S ≌
      S.StandardFormProjectiveMeshCategory := by
  let F := standardFormProjectiveMeshReindex S
  letI : F.Faithful :=
    ⟨fun h ↦ (standardFormProjectiveMeshReindex_map_bijective
      S _ _).injective h⟩
  letI : F.Full :=
    ⟨(standardFormProjectiveMeshReindex_map_bijective
      S _ _).surjective⟩
  letI : F.EssSurj := F.essSurj_of_surj
    (standardFormProjectiveMeshReindex_obj_surjective S)
  letI : F.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact F.asEquivalence

/-- On a connected standard-form translation quiver, the projective part of
the universal deck orbit is explicitly equivalent to the indexed projective
mesh category used to define the standard-form algebra. -/
noncomputable def standardFormProjectiveIndexedShiftOrbitEquivalence
    (x₀ : Fin S.n)
    (hconnected :
      MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
        S.standardFormRightMeshData x₀) :
    let G := MeshCategory.RightMeshData.UniversalCover.FundamentalGroup
      S.standardFormRightMeshData x₀
    let D := standardFormProjectiveDeckShift S x₀
    letI := D.hasShift
    letI := D.additiveShift
    letI := D.linearShift (k := k)
    CoveringHom.ShiftOrbitCategory
        (StandardFormProjectiveSourceCategory S x₀) (Additive G) ≌
      S.StandardFormProjectiveMeshCategory := by
  let D := standardFormProjectiveDeckShift S x₀
  letI := D.hasShift
  letI := D.additiveShift
  letI := D.linearShift (k := k)
  exact (standardFormProjectiveShiftOrbitEquivalence S x₀ hconnected).trans
    (standardFormProjectiveMeshReindexEquivalence S)

/-- The universal mesh projection restricted to lifted projective vertices. -/
noncomputable abbrev standardFormProjectiveMeshProjection (x₀ : Fin S.n) :
    StandardFormProjectiveSourceCategory S x₀ ⥤
      S.StandardFormProjectiveMeshCategory :=
  standardFormProjectiveMeshFullProjection S x₀ ⋙
    standardFormProjectiveMeshReindex S

noncomputable instance standardFormProjectiveMeshProjection_additive
    (x₀ : Fin S.n) :
    (standardFormProjectiveMeshProjection S x₀).Additive := by
  dsimp only [standardFormProjectiveMeshProjection]
  infer_instance

noncomputable instance standardFormProjectiveMeshProjection_linear
    (x₀ : Fin S.n) :
    (standardFormProjectiveMeshProjection S x₀).Linear k := by
  dsimp only [standardFormProjectiveMeshProjection]
  infer_instance

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
