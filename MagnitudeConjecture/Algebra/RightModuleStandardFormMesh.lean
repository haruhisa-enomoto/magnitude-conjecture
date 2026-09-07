import MagnitudeConjecture.Algebra.RightModuleTranslationMultiplicity
import MagnitudeConjecture.CategoryTheory.AdmissibleModuleCategory
import MagnitudeConjecture.CategoryTheory.FiniteCategoryProjectiveGenerator
import MagnitudeConjecture.CategoryTheory.FiniteMeshEndLocal
import MagnitudeConjecture.CategoryTheory.MeshProjectiveDetection
import MagnitudeConjecture.CategoryTheory.MeshRiedtmann
import MagnitudeConjecture.CategoryTheory.RestrictedYoneda
import Mathlib.Data.Fintype.EquivFin

/-!
# The polarized AR mesh underlying the standard form

The standard form in the manuscript is the category algebra of the
projective full subcategory of the mesh category of the Auslander--Reiten
translation quiver.  This file constructs that finite polarized translation
quiver from an arbitrary finite indecomposable right-module skeleton.  In
particular, it does not assume that the module category is directed.

An arrow `x ⟶ y` in the quiver below is written in the path-category
orientation and therefore represents one occurrence of an irreducible module
map `y ⟶ x`.  The polarization is the translation identity for official AR
arrow multiplicities.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Reversed AR-quiver arrows, indexed canonically by the official
middle-term multiplicity. -/
abbrev StandardFormArrow (x y : Fin S.n) :=
  Fin (FiniteTauMatrix.arrowMultiplicity
    S.finiteTauCategoryData.toFiniteRightTauCategoryData y x)

omit [IsAlgClosed k] in
@[simp]
theorem natCard_standardFormArrow (x y : Fin S.n) :
    Nat.card (S.StandardFormArrow x y) =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData y x :=
  Nat.card_fin _

/-- The reversed Auslander--Reiten quiver used to form the standard mesh
category. -/
@[reducible] def standardFormQuiver : Quiver (Fin S.n) where
  Hom := S.StandardFormArrow

/-- Every standard-form arrow type is finite. -/
@[reducible] noncomputable def standardFormArrowFintype (x y : Fin S.n) :
    Fintype (@Quiver.Hom (Fin S.n) S.standardFormQuiver x y) := by
  change Fintype (S.StandardFormArrow x y)
  infer_instance

/-- The projective vertices in the standard-form translation quiver. -/
def standardFormProjectiveSet : Set (Fin S.n) :=
  {x | Projective (S.fgObj x)}

omit [IsAlgClosed k] [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] in
@[simp]
theorem mem_standardFormProjectiveSet_iff (x : Fin S.n) :
    x ∈ S.standardFormProjectiveSet ↔ Projective (S.fgObj x) :=
  Iff.rfl

/-- Auslander--Reiten translation on a nonprojective standard-form vertex. -/
def standardFormTau
    (z : {x : Fin S.n // x ∉ S.standardFormProjectiveSet}) : Fin S.n :=
  (S.rightTranslationEquiv
    ⟨z.1, by simpa [standardFormProjectiveSet] using z.2⟩).1

/-- Translation and the equality of the two arrow multiplicities across an
AR mesh supply a polarization of the standard-form quiver. -/
def standardFormRightMeshData :
    @MeshCategory.RightMeshData (Fin S.n) S.standardFormQuiver := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  exact
    { projective := S.standardFormProjectiveSet
      tau := S.standardFormTau
      arrowEquiv := fun z y ↦ by
        let znp : {x : Fin S.n // ¬ Projective (S.fgObj x)} :=
          ⟨z.1, by simpa [standardFormProjectiveSet] using z.2⟩
        let x := S.rightTranslationEquiv znp
        change Fin (FiniteTauMatrix.arrowMultiplicity
            S.finiteTauCategoryData.toFiniteRightTauCategoryData y z.1) ≃
          Fin (FiniteTauMatrix.arrowMultiplicity
            S.finiteTauCategoryData.toFiniteRightTauCategoryData
              (S.standardFormTau z) y)
        have hcount : FiniteTauMatrix.arrowMultiplicity
            S.finiteTauCategoryData.toFiniteRightTauCategoryData y z.1 =
          FiniteTauMatrix.arrowMultiplicity
            S.finiteTauCategoryData.toFiniteRightTauCategoryData
              (S.standardFormTau z) y := by
          have hback : ((S.rightTranslationEquiv).symm x).1 = z.1 :=
            congrArg Subtype.val (S.rightTranslationEquiv.symm_apply_apply znp)
          have htau : x.1 = S.standardFormTau z := by
            rfl
          calc
            _ = FiniteTauMatrix.arrowMultiplicity
                  S.finiteTauCategoryData.toFiniteRightTauCategoryData x.1 y := by
              simpa only [hback] using
                (S.arrowMultiplicity_eq_inverseTranslation x y).symm
            _ = _ := by rw [htau]
        exact Equiv.cast (congrArg Fin hcount)
      }

section AdditiveHull

local instance standardFormAdditiveHullQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver
local instance standardFormAdditiveHullArrowFintype (x y : Fin S.n) :
    Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

/-- The finite additive hull of the raw standard-form mesh category.  This is
the additive category in which the manuscript's mesh sequences become weak
kernel diagrams. -/
abbrev StandardFormMeshAdditiveHull :=
  S.standardFormRightMeshData.AdditiveHull (k := k)

/-- The additive-hull mesh ending at a nonprojective standard-form vertex. -/
abbrev standardFormAdditiveRightMesh
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    ShortComplex S.StandardFormMeshAdditiveHull :=
  S.standardFormRightMeshData.additiveRightMesh (k := k) z

/-- Riedtmann condition (b) for the standard-form mesh: every nonzero
morphism out of a nonprojective vertex is detected by one arrow entering
that vertex. -/
def StandardFormRiedtmannConditionB : Prop :=
  S.standardFormRightMeshData.RiedtmannConditionB (k := k)

/-- The perfect-composition-pairing witness in Riedtmann condition (c) at a
standard-form projective vertex. -/
abbrev StandardFormRiedtmannProjectiveDualityData (p : Fin S.n) :=
  S.standardFormRightMeshData.RiedtmannProjectiveDualityData (k := k) p

/-- Riedtmann condition (c) for the standard-form mesh. -/
def StandardFormRiedtmannConditionC : Prop :=
  S.standardFormRightMeshData.RiedtmannConditionC (k := k)

/-- In the standard-form additive hull, Riedtmann condition (b) is exactly
epimorphy of every nonprojective incoming-arrow matrix. -/
theorem standardFormRiedtmannConditionB_iff_incoming_epi :
    S.StandardFormRiedtmannConditionB (k := k) ↔
      ∀ z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet},
        Epi (S.standardFormRightMeshData.additiveIncomingMap
          (k := k) z.1) :=
  S.standardFormRightMeshData.riedtmannConditionB_iff_epi_additiveIncomingMap
    (k := k)

/-- The nonprojective standard-form mesh is a weak-kernel diagram in the
finite additive hull.  This is the categorical right-exactness input in the
Auslander-category recovery; it does not assert that the translation map is
monic. -/
theorem standardFormAdditiveRightMesh_isWeakKernel
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    QuotientSubmoduleEquidistribution.Iyama.ShortComplex.IsWeakKernel
      (S.standardFormAdditiveRightMesh (k := k) z) :=
  S.standardFormRightMeshData.additiveRightMesh_isWeakKernel (k := k) z

/-- At a projective standard-form vertex, the incoming-arrow matrix is
monic.  This is the projective boundary case of the mesh-presentation
argument. -/
theorem standardFormAdditiveIncomingMap_mono_of_projective
    (z : Fin S.n) (hz : z ∈ S.standardFormProjectiveSet) :
    Mono (S.standardFormRightMeshData.additiveIncomingMap (k := k) z) :=
  S.standardFormRightMeshData.additiveIncomingMap_mono_of_projective
    (k := k) z hz

end AdditiveHull

/-- Labels of projective vertices in the AR translation quiver. -/
abbrev StandardFormProjectiveVertex :=
  {x : Fin S.n // Projective (S.fgObj x)}

/-- The whole mesh category of the finite Auslander--Reiten translation
quiver underlying the standard form. -/
abbrev StandardFormMeshCategory := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  exact MeshCategory.RawCategory (k := k) S.standardFormRightMeshData

/-- The full subcategory of the standard mesh category on the projective
vertices.  Its category algebra is the manuscript's standard form once the
Bretscher--Gabriel finite-dimensionality and AR-identification layer is
established. -/
abbrev StandardFormProjectiveMeshCategory := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  exact
    InducedCategory
      S.StandardFormMeshCategory
      (fun x : S.StandardFormProjectiveVertex ↦
        MeshCategory.obj (k := k) S.standardFormRightMeshData x.1)

/-- The projective full subcategory has finitely many objects. -/
noncomputable instance standardFormProjectiveMeshCategoryFintype :
    Fintype S.StandardFormProjectiveMeshCategory := by
  change Fintype S.StandardFormProjectiveVertex
  exact Fintype.ofFinite _

/-- The opposite projective mesh category is finite as well. -/
noncomputable instance standardFormProjectiveMeshCategoryOppositeFintype :
    Fintype S.StandardFormProjectiveMeshCategoryᵒᵖ :=
  Fintype.ofEquiv _ Opposite.equivToOpposite

/-- Inclusion of the projective vertices into the whole standard-form mesh
category. -/
def standardFormProjectiveMeshInclusion :
    S.StandardFormProjectiveMeshCategory ⥤ S.StandardFormMeshCategory := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  exact inducedFunctor (fun x : S.StandardFormProjectiveVertex ↦
    MeshCategory.obj (k := k) S.standardFormRightMeshData x.1)

noncomputable instance standardFormProjectiveMeshInclusion_additive :
    S.standardFormProjectiveMeshInclusion.Additive := by
  dsimp only [standardFormProjectiveMeshInclusion]
  infer_instance

noncomputable instance standardFormProjectiveMeshInclusion_linear :
    S.standardFormProjectiveMeshInclusion.Linear k := by
  dsimp only [standardFormProjectiveMeshInclusion]
  infer_instance

/-- The remaining finiteness assertion in the mesh-category construction of
the standard form.  It is separated from the already constructed finite
polarized translation quiver because finite-dimensionality of all mesh Hom
spaces is the local finite-dimensionality input in the Bongartz--Gabriel
Auslander-category argument. -/
def StandardFormMeshHomFinite : Prop :=
  ∀ X Y : S.StandardFormMeshCategory,
    FiniteDimensional k (X ⟶ Y)

/-- The three source-facing inputs in the Riedtmann mesh-Auslander
criterion: local finite-dimensionality, incoming detection at every
nonprojective vertex, and the perfect pairings based at projective
vertices. -/
structure StandardFormRiedtmannConditions : Prop where
  homFinite : S.StandardFormMeshHomFinite
  conditionB : S.StandardFormRiedtmannConditionB (k := k)
  conditionC : S.StandardFormRiedtmannConditionC (k := k)

/-- Finite-dimensional covariant representables on the projective full mesh
subcategory, obtained from finite-dimensionality of its Hom spaces and its
finite object set. -/
theorem standardFormFiniteCovariantRepresentables
    (hfinite : S.StandardFormMeshHomFinite) :
    ∀ X : S.StandardFormProjectiveMeshCategory,
      CoveringHom.IsFiniteDimensionalModule
        (C := S.StandardFormProjectiveMeshCategory) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  intro X
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    letI : FiniteDimensional k
        (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1 ⟶
          MeshCategory.obj (k := k) S.standardFormRightMeshData Y.1) := hfinite
      (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1)
      (MeshCategory.obj (k := k) S.standardFormRightMeshData Y.1)
    exact FiniteDimensional.of_injective
      InducedCategory.homLinearEquiv.toLinearMap
      InducedCategory.homLinearEquiv.injective
  · exact Set.toFinite _

/-- Finite-dimensional coefficient-dual corepresentables on the projective
full mesh subcategory. -/
theorem standardFormFiniteDualCorepresentables
    (hfinite : S.StandardFormMeshHomFinite) :
    ∀ X : S.StandardFormProjectiveMeshCategory,
      CoveringHom.IsFiniteDimensionalModule
        (C := S.StandardFormProjectiveMeshCategory) k
        (CoveringHom.dualLinearYonedaLinearModule (k := k) X) := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  intro X
  constructor
  · intro Y
    change FiniteDimensional k (Module.Dual k (Y ⟶ X))
    letI : FiniteDimensional k
        (MeshCategory.obj (k := k) S.standardFormRightMeshData Y.1 ⟶
          MeshCategory.obj (k := k) S.standardFormRightMeshData X.1) := hfinite
      (MeshCategory.obj (k := k) S.standardFormRightMeshData Y.1)
      (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1)
    letI : FiniteDimensional k (Y ⟶ X) :=
      FiniteDimensional.of_injective
        InducedCategory.homLinearEquiv.toLinearMap
        InducedCategory.homLinearEquiv.injective
    infer_instance
  · exact Set.toFinite _

/-- The manuscript's restricted Yoneda realization
`X ↦ Hom(-, X)|_P`, from the whole mesh category to finite-dimensional
contravariant modules on its projective full subcategory. -/
def standardFormRestrictedYonedaFunctor
    (hfinite : S.StandardFormMeshHomFinite) :
    S.StandardFormMeshCategory ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  exact CoveringHom.finiteRestrictedLinearYonedaFunctor
    (k := k) S.standardFormProjectiveMeshInclusion
    (fun X Y ↦ hfinite
      ((S.standardFormProjectiveMeshInclusion).obj Y) X)

/-- The projective vertices detect every morphism by Riedtmann condition
(b), so the standard-form restricted Yoneda realization is faithful. -/
theorem standardFormRestrictedYonedaFunctor_faithful_of_conditions
    (H : S.StandardFormRiedtmannConditions (k := k)) :
    (S.standardFormRestrictedYonedaFunctor H.homFinite).Faithful := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  apply CoveringHom.finiteRestrictedLinearYonedaFunctor_faithful_of_sourceDetection
  intro X Y f hf
  let x : Fin S.n := LinearPathCategory.vertex X.as
  let y : Fin S.n := LinearPathCategory.vertex Y.as
  change MeshCategory.obj (k := k) S.standardFormRightMeshData x ⟶
    MeshCategory.obj (k := k) S.standardFormRightMeshData y at f
  obtain ⟨p, hp, g, hgf⟩ :=
    S.standardFormRightMeshData.exists_projective_precomposition_ne_zero
      (fun a b ↦ H.homFinite
        (MeshCategory.obj (k := k) S.standardFormRightMeshData a)
        (MeshCategory.obj (k := k) S.standardFormRightMeshData b))
      H.conditionB f hf
  have hp' : Projective (S.fgObj p) :=
    (S.mem_standardFormProjectiveSet_iff p).mp hp
  let P : S.StandardFormProjectiveMeshCategory := ⟨p, hp'⟩
  exact ⟨P, g, hgf⟩

/-- Covariant representables on the opposite projective mesh category are
the contravariant projective modules used by `mod P` in the manuscript. -/
theorem standardFormFiniteRightRepresentables
    (hfinite : S.StandardFormMeshHomFinite) :
    ∀ X : S.StandardFormProjectiveMeshCategoryᵒᵖ,
      CoveringHom.IsFiniteDimensionalModule
        (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k
        (CoveringHom.linearCoyonedaLinearModule (k := k) X) := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  intro X
  constructor
  · intro Y
    change FiniteDimensional k (X ⟶ Y)
    letI : FiniteDimensional k
        (MeshCategory.obj (k := k) S.standardFormRightMeshData Y.unop.1 ⟶
          MeshCategory.obj (k := k) S.standardFormRightMeshData X.unop.1) :=
      hfinite
        (MeshCategory.obj (k := k) S.standardFormRightMeshData Y.unop.1)
        (MeshCategory.obj (k := k) S.standardFormRightMeshData X.unop.1)
    letI : FiniteDimensional k (Y.unop ⟶ X.unop) :=
      FiniteDimensional.of_injective
        InducedCategory.homLinearEquiv.toLinearMap
        InducedCategory.homLinearEquiv.injective
    exact FiniteDimensional.of_injective
      (CoveringHom.oppositeHomLinearEquiv X Y).toLinearMap
      (CoveringHom.oppositeHomLinearEquiv X Y).injective
  · exact Set.toFinite _

/-- Finite-dimensional mesh Hom spaces make every projective standard-form
vertex have a local endomorphism ring.  This is the local-boundedness part of
the Bongartz--Gabriel mesh-Auslander layer. -/
theorem standardFormProjectiveMeshCategoryEndLocal
    (hfinite : S.StandardFormMeshHomFinite)
    (X : S.StandardFormProjectiveMeshCategory) : IsLocalRing (End X) := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  let eLinear : End X ≃ₗ[k]
      End (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1) :=
    InducedCategory.homLinearEquiv
  letI : FiniteDimensional k
      (End (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1)) :=
    hfinite ((S.standardFormProjectiveMeshInclusion).obj X)
      ((S.standardFormProjectiveMeshInclusion).obj X)
  letI : FiniteDimensional k (End X) :=
    FiniteDimensional.of_injective eLinear.toLinearMap eLinear.injective
  letI : IsLocalRing
      (End (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1)) :=
    MeshCategory.end_isLocalRing_of_finiteDimensional
      S.standardFormRightMeshData X.1
  let e : End X ≃+*
      End (MeshCategory.obj (k := k) S.standardFormRightMeshData X.1) :=
    { InducedCategory.endEquiv with
      map_add' := fun _ _ ↦ rfl }
  exact MagnitudeConjecture.RingEquiv.isLocalRing_noncomm e.symm

/-- The projective full mesh subcategory is skeletal: the path-length grading
prevents distinct mesh vertices from becoming isomorphic. -/
theorem standardFormProjectiveMeshCategorySkeletal :
    Skeletal S.StandardFormProjectiveMeshCategory := by
  letI : Quiver (Fin S.n) := S.standardFormQuiver
  letI : ∀ x y : Fin S.n, Fintype (x ⟶ y) :=
    fun x y ↦ S.standardFormArrowFintype x y
  intro X Y hXY
  obtain ⟨e⟩ := hXY
  let F := fun x : S.StandardFormProjectiveVertex ↦
    MeshCategory.obj (k := k) S.standardFormRightMeshData x.1
  have hlabel : X.1 = Y.1 :=
    MeshCategory.eq_of_obj_iso (k := k) S.standardFormRightMeshData
      ((inducedFunctor F).mapIso e)
  exact Subtype.ext hlabel

/-- The opposite projective mesh category is skeletal as well. -/
theorem standardFormProjectiveMeshCategoryOppositeSkeletal :
    Skeletal S.StandardFormProjectiveMeshCategoryᵒᵖ := by
  intro X Y hXY
  obtain ⟨e⟩ := hXY
  exact congrArg Opposite.op
    (S.standardFormProjectiveMeshCategorySkeletal ⟨e.unop.symm⟩)

/-- Once its mesh Hom spaces are finite-dimensional, the projective full
subcategory satisfies the complete locally bounded package used by the
covering formalization. -/
theorem standardFormProjectiveMeshCategoryIsLocallyBounded
    (hfinite : S.StandardFormMeshHomFinite) :
    CoveringHom.IsLocallyBounded
      (k := k) (C := S.StandardFormProjectiveMeshCategory) where
  skeletal := S.standardFormProjectiveMeshCategorySkeletal
  finiteCovariantRepresentables :=
    S.standardFormFiniteCovariantRepresentables hfinite
  finiteDualCorepresentables :=
    S.standardFormFiniteDualCorepresentables hfinite
  localEndomorphismRings :=
    S.standardFormProjectiveMeshCategoryEndLocal hfinite

/-- The category algebra of the projective full subcategory of the AR mesh
category.  The opposite is deliberate: covariant modules on `Pᵒᵖ` are the
contravariant modules `mod P` used by the manuscript, so the right-module
category-algebra bridge is applied at `Pᵒᵖ`. -/
abbrev standardFormAlgebra
    (hfinite : S.StandardFormMeshHomFinite) : Type u :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra
    (S.standardFormFiniteRightRepresentables hfinite)

/-- The standard-form category algebra is finite-dimensional. -/
theorem standardFormAlgebra_finiteDimensional
    (hfinite : S.StandardFormMeshHomFinite) :
    FiniteDimensional k (S.standardFormAlgebra hfinite) :=
  CoveringHom.finiteCategoryProjectiveGenerator.algebra_finiteDimensional
    (S.standardFormFiniteRightRepresentables hfinite)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
