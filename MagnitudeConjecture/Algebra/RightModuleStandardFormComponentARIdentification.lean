import MagnitudeConjecture.Algebra.RightModuleStandardFormARIdentification
import MagnitudeConjecture.Algebra.RightModuleStandardFormComponentARSurplus
import MagnitudeConjecture.CategoryTheory.FiniteTauOccurrences
import MagnitudeConjecture.CategoryTheory.TranslationQuiverOrdinaryConnected

/-!
# Arrowwise Auslander--Reiten identification for component algebras

The component projective-generator equivalence carries the chosen component
right-almost-split source, with every displayed label retained, to a minimal
right-almost-split source over the component category algebra.  Occurrence
bases over an algebraically closed field therefore identify every component
algebra arrow multiplicity with the corresponding component-module
multiplicity, not merely their total incoming arities.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open MagnitudeConjecture.CoveringHom

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance componentARIdentificationQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance componentARIdentificationArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance componentARIdentificationDecidableEq :
    DecidableEq S.StandardFormWalkComponent :=
  Classical.decEq _

noncomputable local instance componentARIdentificationAlgebraFiniteDimensional
    (c : S.StandardFormWalkComponent) :
    FiniteDimensional k (S.standardFormComponentAlgebra (k := k) c) :=
  S.standardFormComponentAlgebra_finiteDimensional (k := k) c

local instance componentARIdentificationAlgebraNoetherian
    (c : S.StandardFormWalkComponent) :
    IsNoetherianRing (S.standardFormComponentAlgebra (k := k) c)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

noncomputable local instance componentARIdentificationGlobalFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance componentARIdentificationGlobalNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The component category algebra retains every individual incoming-arrow
multiplicity of the component module skeleton under the fixed vertex
enumeration. -/
theorem standardFormComponentAlgebra_arrowMultiplicity_eq_componentModule
    (c : S.StandardFormWalkComponent)
    [EnoughProjectives
      (FiniteDimensionalModuleCategory
        (C := (S.StandardFormComponentProjectiveMeshCategory
          (k := k) c)ᵒᵖ) k)]
    (source target :
      Fin (S.standardFormComponentProjectiveVertexModuleIndecomposableSkeleton
        (k := k) c).n) :
    FiniteTauMatrix.arrowMultiplicity
        (S.standardFormComponentAlgebraIndecomposableSkeleton
          (k := k) c).finiteTauCategoryData.toFiniteRightTauCategoryData
          source target =
      FiniteTauMatrix.arrowMultiplicity
        (S.standardFormComponentProjectiveVertexModuleIndecomposableSkeleton
          (k := k) c).toFiniteRightTauCategoryData source target := by
  let Csk :=
    S.standardFormComponentProjectiveVertexModuleIndecomposableSkeleton
      (k := k) c
  let TC := Csk.toFiniteRightTauCategoryData
  let EA := S.standardFormComponentProjectiveVertexModuleAlgebraEquivalence
    (k := k) c
  let Ask := S.standardFormComponentAlgebraIndecomposableSkeleton
    (k := k) c
  let TA := Ask.finiteTauCategoryData.toFiniteRightTauCategoryData
  let B := S.standardFormComponentAlgebra (k := k) c
  letI : ∀ i : Fin Ask.n, Module k (Ask.almostSplitSkeleton.obj i) :=
    fun i ↦ Module.restrictScalars k Bᵐᵒᵖ
      (Ask.almostSplitSkeleton.obj i)
  letI : ∀ i : Fin Ask.n, IsScalarTower k Bᵐᵒᵖ
      (Ask.almostSplitSkeleton.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k Bᵐᵒᵖ
      (Ask.almostSplitSkeleton.obj i)
  let e (i : Fin Csk.n) : Ask.fgObj i ≅ EA.functor.obj (Csk.obj i) :=
    pushforwardRightModuleIndecomposableSkeletonObjIso EA Csk i
  let d := FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition
    TC target
  let m := (TC.rightMesh (TC.obj target)).g ≫
    (TC.rightTermIso (TC.obj target)).hom
  let R : Ask.almostSplitSkeleton.MinimalRightAlmostSplitDecomposition
      target :=
    { middle := EA.functor.obj (TC.rightMesh (TC.obj target)).X₂
      finiteLength := fgModule_isFiniteLength
        (k := k) (A := S.standardFormComponentAlgebra (k := k) c) _
      map := EA.functor.map m ≫ (e target).inv
      rightAlmostSplit :=
        (FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit TC target
          |>.map_equivalence EA).postcomp_iso (e target).symm
      rightMinimal :=
        (FiniteTauMatrix.rightMesh_terminal_isRightMinimal TC target
          |>.map_equivalence EA).postcomp_iso (e target).symm
      index := FintypeCat.of (Fin (FiniteTauMatrix.rightMiddleArity TC target))
      label := FiniteTauMatrix.rightMiddleLabel TC target
      decomposition :=
        EA.functor.mapIso d.isoBiproduct ≪≫
          EA.functor.mapBiproduct d.summand ≪≫
            biproduct.mapIso (fun i ↦
              (e (FiniteTauMatrix.rightMiddleLabel TC target i)).symm) }
  let C := Ask.meshRightAlmostSplitAt target
  calc
    FiniteTauMatrix.arrowMultiplicity TA source target =
        Nat.card (Ask.MeshArrow target source) :=
      (Ask.natCard_meshArrow_eq_arrowMultiplicity target source).symm
    _ = Module.finrank k
          (Ask.almostSplitSkeleton.irreducibleHomSpace
            (K := k) source target) :=
      (Ask.almostSplitSkeleton
        |>.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
          C source).symm
    _ = Nat.card (Ask.almostSplitSkeleton.RightAROccurrence R source) :=
      Ask.almostSplitSkeleton
        |>.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
          R source
    _ = FiniteTauMatrix.arrowMultiplicity TC source target := by
      change Nat.card
          {i : Fin (FiniteTauMatrix.rightMiddleArity TC target) //
            FiniteTauMatrix.rightMiddleLabel TC target i = source} = _
      rw [FiniteTauMatrix.arrowMultiplicity, Nat.card_eq_fintype_card,
        Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : FiniteTauMatrix.rightMiddleLabel TC target i = source <;>
        simp [hi]

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Under the fixed component enumeration, every component-algebra AR arrow
multiplicity is the corresponding entry of the original standard-form AR
matrix.  Thus the intrinsic reversed AR quiver of the component algebra has
exactly the ordinary arrows induced on that augmented-walk component. -/
theorem standardFormComponentAlgebra_arrowMultiplicity_eq_original
    (c : S.StandardFormWalkComponent)
    (source target :
      Fin (S.standardFormComponentProjectiveVertexModuleIndecomposableSkeleton
        (k := k) c).n) :
    FiniteTauMatrix.arrowMultiplicity
        (S.standardFormComponentAlgebraIndecomposableSkeleton
          (k := k) c).finiteTauCategoryData.toFiniteRightTauCategoryData
          source target =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData
          (S.standardFormComponentVertexEquivFin c source).1
          (S.standardFormComponentVertexEquivFin c target).1 := by
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory
        (C := (S.StandardFormComponentProjectiveMeshCategory
          (k := k) c)ᵒᵖ) k) :=
    enoughProjectives_of_finiteRepresentables
      (S.standardFormComponentFiniteRightRepresentables (k := k) c)
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory
        (C := S.StandardFormProjectiveMeshCategoryᵒᵖ) k) :=
    enoughProjectives_of_finiteRepresentables
      (S.standardFormFiniteRightRepresentables S.standardFormMeshHomFinite)
  let Csk :=
    S.standardFormComponentProjectiveVertexModuleIndecomposableSkeleton
      (k := k) c
  let TC := Csk.toFiniteRightTauCategoryData
  let E := S.standardFormComponentModuleExtensionByZero (k := k) c
  let Gsk := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
    (k := k)
  let TG := Gsk.toFiniteRightTauCategoryData
  let EA := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
  let Ask := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let TA := Ask.finiteTauCategoryData.toFiniteRightTauCategoryData
  let B := S.standardFormAlgebra S.standardFormMeshHomFinite
  let F := E ⋙ EA.functor
  let vertex := S.standardFormComponentVertexEquivFin c
  letI : ∀ i : Fin Ask.n, Module k (Ask.almostSplitSkeleton.obj i) :=
    fun i ↦ Module.restrictScalars k Bᵐᵒᵖ
      (Ask.almostSplitSkeleton.obj i)
  letI : ∀ i : Fin Ask.n, IsScalarTower k Bᵐᵒᵖ
      (Ask.almostSplitSkeleton.obj i) :=
    fun i ↦ IsScalarTower.restrictScalars k Bᵐᵒᵖ
      (Ask.almostSplitSkeleton.obj i)
  let eComponent (i : Fin Csk.n) : E.obj (TC.obj i) ≅
      TG.obj (vertex i).1 := by
    change E.obj
        ((S.standardFormComponentRestrictedYonedaFunctor
          (k := k) c).obj (vertex i)) ≅
      (S.standardFormRestrictedYonedaFunctor
        S.standardFormMeshHomFinite).obj
          ((S.standardFormComponentMeshInclusion (k := k) c).obj (vertex i))
    exact (S.standardFormComponentRestrictedYonedaExtensionNatIso
      (k := k) c).app (vertex i)
  let eAlgebra (j : Fin Gsk.n) : Ask.fgObj j ≅
      EA.functor.obj (TG.obj j) :=
    pushforwardRightModuleIndecomposableSkeletonObjIso EA Gsk j
  let eEnd (i : Fin Csk.n) : F.obj (TC.obj i) ≅
      Ask.fgObj (vertex i).1 :=
    EA.functor.mapIso (eComponent i) ≪≫ (eAlgebra (vertex i).1).symm
  let d := FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition
    TC target
  let m := (TC.rightMesh (TC.obj target)).g ≫
    (TC.rightTermIso (TC.obj target)).hom
  have hmAS : IsRightAlmostSplit m :=
    FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit TC target
  have hmMin : IsRightMinimal m :=
    FiniteTauMatrix.rightMesh_terminal_isRightMinimal TC target
  have hclosed : IsLocallyIndecomposableRightObjectClosedAt E
      (TC.obj target) := by
    change IsLocallyIndecomposableRightObjectClosedAt E
      ((S.standardFormComponentRestrictedYonedaFunctor
        (k := k) c).obj (vertex target))
    exact
      S.standardFormComponentModuleExtensionByZero_locallyIndecomposableRightObjectClosedAt
        (k := k) c (vertex target)
  have hEAS : IsRightAlmostSplit
      (E.map m ≫ (eComponent target).hom) :=
    (rightAlmostSplit_map_of_full_faithful_of_finiteIndecomposableCore
      E finiteDimensionalModule_finiteIndecomposableDecomposition hmAS
        hclosed).postcomp_iso (eComponent target)
  have hEMin : IsRightMinimal
      (E.map m ≫ (eComponent target).hom) :=
    (rightMinimal_map_of_full_faithful E hmMin).postcomp_iso
      (eComponent target)
  have hFAS : IsRightAlmostSplit
      (F.map m ≫ (eEnd target).hom) := by
    simpa only [F, eEnd, Functor.comp_obj, Functor.comp_map,
      Functor.map_comp, Functor.mapIso_hom, Iso.trans_hom,
      Category.assoc] using
      ((hEAS.map_equivalence EA).postcomp_iso
        (eAlgebra (vertex target).1).symm)
  have hFMin : IsRightMinimal
      (F.map m ≫ (eEnd target).hom) := by
    simpa only [F, eEnd, Functor.comp_obj, Functor.comp_map,
      Functor.map_comp, Functor.mapIso_hom, Iso.trans_hom,
      Category.assoc] using
      ((hEMin.map_equivalence EA).postcomp_iso
        (eAlgebra (vertex target).1).symm)
  let R : Ask.almostSplitSkeleton.MinimalRightAlmostSplitDecomposition
      (vertex target).1 :=
    { middle := F.obj (TC.rightMesh (TC.obj target)).X₂
      finiteLength := fgModule_isFiniteLength (k := k) (A := B) _
      map := F.map m ≫ (eEnd target).hom
      rightAlmostSplit := hFAS
      rightMinimal := hFMin
      index := FintypeCat.of (Fin (FiniteTauMatrix.rightMiddleArity TC target))
      label := fun i ↦
        (vertex (FiniteTauMatrix.rightMiddleLabel TC target i)).1
      decomposition :=
        F.mapIso d.isoBiproduct ≪≫
          F.mapBiproduct d.summand ≪≫
            biproduct.mapIso (fun i ↦
              eEnd (FiniteTauMatrix.rightMiddleLabel TC target i)) }
  let occurrenceEquiv :
      Ask.almostSplitSkeleton.RightAROccurrence R (vertex source).1 ≃
        {i : Fin (FiniteTauMatrix.rightMiddleArity TC target) //
          FiniteTauMatrix.rightMiddleLabel TC target i = source} :=
    { toFun := fun t ↦ ⟨t.1, by
          apply vertex.injective
          apply Subtype.ext
          exact t.2⟩
      invFun := fun t ↦ ⟨t.1, by
        change
          (vertex (FiniteTauMatrix.rightMiddleLabel TC target t.1)).1 =
            (vertex source).1
        exact congrArg Subtype.val (congrArg vertex t.2)⟩
      left_inv := fun t ↦ Subtype.ext rfl
      right_inv := fun t ↦ Subtype.ext rfl }
  let C := Ask.meshRightAlmostSplitAt (vertex target).1
  calc
    FiniteTauMatrix.arrowMultiplicity
          (S.standardFormComponentAlgebraIndecomposableSkeleton
            (k := k) c).finiteTauCategoryData.toFiniteRightTauCategoryData
            source target =
        FiniteTauMatrix.arrowMultiplicity TC source target :=
      S.standardFormComponentAlgebra_arrowMultiplicity_eq_componentModule
        (k := k) c source target
    _ = Nat.card
          {i : Fin (FiniteTauMatrix.rightMiddleArity TC target) //
            FiniteTauMatrix.rightMiddleLabel TC target i = source} := by
      rw [FiniteTauMatrix.arrowMultiplicity, Nat.card_eq_fintype_card,
        Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : FiniteTauMatrix.rightMiddleLabel TC target i = source <;>
        simp [hi]
    _ = Nat.card
          (Ask.almostSplitSkeleton.RightAROccurrence R (vertex source).1) :=
      (Nat.card_congr occurrenceEquiv).symm
    _ = Module.finrank k
          (Ask.almostSplitSkeleton.irreducibleHomSpace
            (K := k) (vertex source).1 (vertex target).1) :=
      (Ask.almostSplitSkeleton
        |>.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
          R (vertex source).1).symm
    _ = Nat.card
          (Ask.almostSplitSkeleton.RightAROccurrence C (vertex source).1) :=
      Ask.almostSplitSkeleton
        |>.finrank_irreducibleHomSpace_eq_card_rightAROccurrence_of_isAlgClosed
          C (vertex source).1
    _ = Nat.card (Ask.MeshArrow (vertex target).1 (vertex source).1) := rfl
    _ = FiniteTauMatrix.arrowMultiplicity TA
          (vertex source).1 (vertex target).1 :=
      Ask.natCard_meshArrow_eq_arrowMultiplicity
        (vertex target).1 (vertex source).1
    _ = FiniteTauMatrix.arrowMultiplicity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData
          (vertex source).1 (vertex target).1 :=
      S.standardFormAlgebra_arrowMultiplicity_eq_original
        (k := k) (vertex source).1 (vertex target).1

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The component algebra's intrinsic standard-form right translation quiver
is augmented-walk connected.  Formal translation edges of the induced
component are first replaced by polarized ordinary two-arrow routes, so only
the arrowwise multiplicity identification is needed; no separate comparison
of the two chosen translations enters the argument. -/
theorem standardFormComponentAlgebra_isWalkConnectedAt
    (c : S.StandardFormWalkComponent)
    (x₀ : S.StandardFormWalkComponentVertex c) :
    let Ask := S.standardFormComponentAlgebraIndecomposableSkeleton
      (k := k) c
    MeshCategory.RightMeshData.UniversalCover.IsWalkConnectedAt
      Ask.standardFormRightMeshData
      ((S.standardFormComponentVertexEquivFin c).symm x₀) := by
  letI : EnoughProjectives
      (FiniteDimensionalModuleCategory
        (C := (S.StandardFormComponentProjectiveMeshCategory
          (k := k) c)ᵒᵖ) k) :=
    enoughProjectives_of_finiteRepresentables
      (S.standardFormComponentFiniteRightRepresentables (k := k) c)
  let Ask := S.standardFormComponentAlgebraIndecomposableSkeleton
    (k := k) c
  let vertex := S.standardFormComponentVertexEquivFin c
  let T₁ := S.standardFormComponentRightMeshData c
  letI : Quiver (S.StandardFormWalkComponentVertex c) :=
    MeshCategory.RightMeshData.UniversalCover.walkComponentQuiver
      S.standardFormRightMeshData c
  letI : Quiver (Fin Ask.n) := Ask.standardFormQuiver
  letI (i j : Fin Ask.n) : Fintype (i ⟶ j) :=
    Ask.standardFormArrowFintype i j
  let arrowEquiv (x y : S.StandardFormWalkComponentVertex c) :
      @Quiver.Hom (S.StandardFormWalkComponentVertex c)
          (MeshCategory.RightMeshData.UniversalCover.walkComponentQuiver
            S.standardFormRightMeshData c) x y ≃
        @Quiver.Hom (Fin Ask.n) Ask.standardFormQuiver
          (vertex.symm x) (vertex.symm y) := by
    letI : Fintype
        (@Quiver.Hom (S.StandardFormWalkComponentVertex c)
          (MeshCategory.RightMeshData.UniversalCover.walkComponentQuiver
            S.standardFormRightMeshData c) x y) :=
      S.standardFormArrowFintype x.1 y.1
    apply Fintype.equivOfCardEq
    simpa only [Nat.card_eq_fintype_card] using
      (calc
        Nat.card
            (@Quiver.Hom (S.StandardFormWalkComponentVertex c)
              (MeshCategory.RightMeshData.UniversalCover.walkComponentQuiver
                S.standardFormRightMeshData c) x y) =
            FiniteTauMatrix.arrowMultiplicity
              S.finiteTauCategoryData.toFiniteRightTauCategoryData y.1 x.1 :=
          S.natCard_standardFormArrow x.1 y.1
        _ = FiniteTauMatrix.arrowMultiplicity
              Ask.finiteTauCategoryData.toFiniteRightTauCategoryData
                (vertex.symm y) (vertex.symm x) := by
          simpa only [vertex, Equiv.apply_symm_apply] using
            (S.standardFormComponentAlgebra_arrowMultiplicity_eq_original
              (k := k) c (vertex.symm y) (vertex.symm x)).symm
        _ = Nat.card
              (@Quiver.Hom (Fin Ask.n) Ask.standardFormQuiver
                (vertex.symm x) (vertex.symm y)) :=
          (Ask.natCard_standardFormArrow
            (vertex.symm x) (vertex.symm y)).symm)
  let P : S.StandardFormWalkComponentVertex c ⥤q Fin Ask.n :=
    { obj := vertex.symm
      map := fun a ↦ arrowEquiv _ _ a }
  have hsurjective : Function.Surjective P.obj := vertex.symm.surjective
  have hmesh : ∀ s : {s : S.StandardFormWalkComponentVertex c //
      s ∉ T₁.projective}, Nonempty (T₁.MeshArrow s) := by
    intro s
    let z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet} :=
      ⟨s.1.1, s.2⟩
    have hpos : 0 < FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1 := by
      simpa only [S.standardFormFiniteTauNonprojective_val z] using
        (FiniteTauMatrix.rightMiddleArity_pos_of_nonprojective
          S.finiteTauCategoryData
            (S.standardFormFiniteTauNonprojective z))
    let i : Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData z.1) :=
      ⟨0, hpos⟩
    let a := S.standardFormMiddleIndexEquiv z.1 i
    let y : S.StandardFormWalkComponentVertex c :=
      ⟨a.1,
        (MeshCategory.RightMeshData.UniversalCover.walkComponentClass_eq_of_arrow
          S.standardFormRightMeshData a.2).symm.trans s.1.2⟩
    exact ⟨⟨y, a.2⟩⟩
  exact
    MeshCategory.RightMeshData.UniversalCover.isWalkConnectedAt_of_ordinaryPrefunctor
      T₁ Ask.standardFormRightMeshData P x₀ hsurjective
        (S.standardFormComponent_isWalkConnectedAt c x₀) hmesh

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
