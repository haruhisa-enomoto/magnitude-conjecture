import MagnitudeConjecture.Algebra.RightModuleStandardFormProjectiveCover
import MagnitudeConjecture.CategoryTheory.LocallyBoundedOpposite

/-!
# Local boundedness of the concrete standard-form cover

The normalized universal mesh realization is a covering of a finite category.
Its fixed-fibre Hom decompositions therefore make both the incoming and the
outgoing support of every upstairs object finite.  Restricting to lifts of
projective vertices and then passing to the opposite gives the locally bounded
category used by the standard covering average.
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

local instance standardFormCoverLocallyBoundedQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance standardFormCoverLocallyBoundedArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance standardFormCoverFGIndecFintype :
    Fintype S.FGIndecCategory := by
  change Fintype (Fin S.n)
  infer_instance

noncomputable local instance standardFormCoverMeshCategoryFinite :
    Finite S.StandardFormMeshCategory :=
  Finite.of_injective
    (fun X : S.StandardFormMeshCategory ↦
      MagnitudeConjecture.LinearPathCategory.vertex X.as)
    (by
      intro X Y hXY
      apply CategoryTheory.Quotient.ext
      exact hXY)

namespace UniversalCover

/-- Only finitely many objects of the universal mesh category receive a
nonzero morphism from a fixed object. -/
theorem standardFormUniversalOutgoingSupportFinite
    (p : Fin S.n) (Y : SourceCategory S p) :
    {J : SourceCategory S p | Nontrivial (Y ⟶ J)}.Finite := by
  let F := S.standardFormUniversalIndecMeshFunctor p
  let U : S.FGIndecCategory → Set (SourceCategory S p) :=
    fun X ↦ (fun J : LinearCovering.Fiber F X ↦ J.1) ''
      {J | Nontrivial (Y ⟶ J.1)}
  have hU : ∀ X, (U X).Finite := by
    intro X
    exact (S.standardFormUniversalTargetFiberHomFinite p X Y).image _
  refine (Set.finite_iUnion hU).subset ?_
  intro J hJ
  apply Set.mem_iUnion.mpr
  refine ⟨F.obj J, ?_⟩
  exact ⟨⟨J, rfl⟩, hJ, rfl⟩

/-- Only finitely many objects of the universal mesh category admit a
nonzero morphism to a fixed object. -/
theorem standardFormUniversalIncomingSupportFinite
    (p : Fin S.n) (Y : SourceCategory S p) :
    {I : SourceCategory S p | Nontrivial (I ⟶ Y)}.Finite := by
  let F := meshProjection S p
  let U : S.StandardFormMeshCategory → Set (SourceCategory S p) :=
    fun X ↦ (fun I : LinearCovering.Fiber F X ↦ I.1) ''
      {I | Nontrivial (I.1 ⟶ Y)}
  have hU : ∀ X, (U X).Finite := by
    intro X
    exact
      (S.standardFormUniversalMeshProjectionSourceFiberHomFinite p X Y).image _
  refine (Set.finite_iUnion hU).subset ?_
  intro I hI
  apply Set.mem_iUnion.mpr
  refine ⟨F.obj I, ?_⟩
  exact ⟨⟨I, rfl⟩, hI, rfl⟩

/-- Restriction to the projective-vertex full subcategory preserves finite
outgoing support. -/
theorem standardFormProjectiveSourceOutgoingSupportFinite
    (p : Fin S.n) (X : StandardFormProjectiveSourceCategory S p) :
    {Y : StandardFormProjectiveSourceCategory S p |
      Nontrivial (X ⟶ Y)}.Finite := by
  let T : Set (SourceCategory S p) :=
    {Y | Nontrivial (X.obj ⟶ Y)}
  have hT : T.Finite :=
    standardFormUniversalOutgoingSupportFinite S p X.obj
  have hpre :
      ((fun Y : StandardFormProjectiveSourceCategory S p ↦ Y.obj) ⁻¹' T).Finite :=
    hT.preimage fun Y _ Z _ hYZ ↦
      ObjectProperty.FullSubcategory.ext hYZ
  refine hpre.subset ?_
  intro Y hY
  change Nontrivial (X ⟶ Y) at hY
  change Nontrivial (X.obj ⟶ Y.obj)
  exact (InducedCategory.homEquiv :
    (X ⟶ Y) ≃ (X.obj ⟶ Y.obj)).nontrivial_congr.mp hY

/-- Restriction to the projective-vertex full subcategory preserves finite
incoming support. -/
theorem standardFormProjectiveSourceIncomingSupportFinite
    (p : Fin S.n) (X : StandardFormProjectiveSourceCategory S p) :
    {Y : StandardFormProjectiveSourceCategory S p |
      Nontrivial (Y ⟶ X)}.Finite := by
  let T : Set (SourceCategory S p) :=
    {Y | Nontrivial (Y ⟶ X.obj)}
  have hT : T.Finite :=
    standardFormUniversalIncomingSupportFinite S p X.obj
  have hpre :
      ((fun Y : StandardFormProjectiveSourceCategory S p ↦ Y.obj) ⁻¹' T).Finite :=
    hT.preimage fun Y _ Z _ hYZ ↦
      ObjectProperty.FullSubcategory.ext hYZ
  refine hpre.subset ?_
  intro Y hY
  change Nontrivial (Y ⟶ X) at hY
  change Nontrivial (Y.obj ⟶ X.obj)
  exact (InducedCategory.homEquiv :
    (Y ⟶ X) ≃ (Y.obj ⟶ X.obj)).nontrivial_congr.mp hY

/-- The full subcategory on lifts of projective vertices is skeletal. -/
theorem standardFormProjectiveSourceCategorySkeletal
    (p : Fin S.n) :
    Skeletal (StandardFormProjectiveSourceCategory S p) := by
  intro X Y hXY
  obtain ⟨e⟩ := hXY
  let F := (standardFormProjectiveProperty S p).ι
  apply ObjectProperty.FullSubcategory.ext
  exact MeshCategory.rawCategory_skeletal
    (k := k)
    (MeshCategory.RightMeshData.UniversalCover.rightMeshData
      S.standardFormRightMeshData p)
    ⟨F.mapIso e⟩

/-- The concrete projective part of the normalized universal mesh category
is locally bounded. -/
theorem standardFormProjectiveSourceCategoryIsLocallyBounded
    (p : Fin S.n) :
    CoveringHom.IsLocallyBounded
      (k := k) (C := StandardFormProjectiveSourceCategory S p) where
  skeletal := standardFormProjectiveSourceCategorySkeletal S p
  finiteCovariantRepresentables := by
    intro X
    constructor
    · intro Y
      change FiniteDimensional k (X ⟶ Y)
      letI : FiniteDimensional k (X.obj ⟶ Y.obj) :=
        S.standardFormUniversalMeshHomFinite p X.obj Y.obj
      exact FiniteDimensional.of_injective
        InducedCategory.homLinearEquiv.toLinearMap
        InducedCategory.homLinearEquiv.injective
    · exact standardFormProjectiveSourceOutgoingSupportFinite S p X
  finiteDualCorepresentables := by
    intro X
    constructor
    · intro Y
      change FiniteDimensional k (Module.Dual k (Y ⟶ X))
      letI : FiniteDimensional k (Y.obj ⟶ X.obj) :=
        S.standardFormUniversalMeshHomFinite p Y.obj X.obj
      letI : FiniteDimensional k (Y ⟶ X) :=
        FiniteDimensional.of_injective
          InducedCategory.homLinearEquiv.toLinearMap
          InducedCategory.homLinearEquiv.injective
      infer_instance
    · refine (standardFormProjectiveSourceIncomingSupportFinite S p X).subset ?_
      intro Y hY
      change Nontrivial (Module.Dual k (Y ⟶ X)) at hY
      change Nontrivial (Y ⟶ X)
      exact (Module.nontrivial_dual_iff k).mp hY
  localEndomorphismRings := by
    intro X
    letI : IsLocalRing (End X.obj) :=
      S.standardFormUniversalMeshEndLocal p X.obj
    let e : End X ≃+* End X.obj :=
      { InducedCategory.endEquiv with
        map_add' := fun _ _ ↦ rfl }
    exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm e.symm

/-- The opposite projective source category appearing in the category-algebra
and covering-average interfaces is locally bounded. -/
theorem standardFormOppositeProjectiveSourceCategoryIsLocallyBounded
    (p : Fin S.n) :
    CoveringHom.IsLocallyBounded
      (k := k) (C := (StandardFormProjectiveSourceCategory S p)ᵒᵖ) :=
  (standardFormProjectiveSourceCategoryIsLocallyBounded S p).op

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
