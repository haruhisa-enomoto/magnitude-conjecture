import MagnitudeConjecture.Algebra.RightModuleStandardFormComponentAlgebraSkeleton
import MagnitudeConjecture.Algebra.RightModuleStandardFormComponentSurplus
import MagnitudeConjecture.CategoryTheory.AlmostSplitFiniteCoreFunctor
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleFiniteAlmostSplit
import MagnitudeConjecture.CategoryTheory.FiniteCategoryAlgebraSurplus
import MagnitudeConjecture.CategoryTheory.FiniteSkeletonDensityInvariance

/-!
# Auslander--Reiten surplus of a standard-form component algebra

Extension by zero is locally closed at component representables: an
indecomposable global module mapping nontrivially into one must belong to the
same augmented-walk component.  Hence the component and global chosen
right-almost-split sources have the same total indecomposable arity.  After
transport through the finite-category algebra equivalence, their local
densities identify the component algebra's ambient surplus with the
combinatorial surplus induced from the original standard-form quiver.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture.CoveringHom
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance componentARSurplusQuiver : Quiver (Fin S.n) :=
  S.standardFormQuiver

noncomputable local instance componentARSurplusArrowFintype
    (x y : Fin S.n) : Fintype (x ⟶ y) :=
  S.standardFormArrowFintype x y

noncomputable local instance componentARSurplusDecidableEq :
    DecidableEq S.StandardFormWalkComponent :=
  Classical.decEq _

noncomputable local instance componentARSurplusAlgebraFiniteDimensional
    (c : S.StandardFormWalkComponent) :
    FiniteDimensional k (S.standardFormComponentAlgebra (k := k) c) :=
  S.standardFormComponentAlgebra_finiteDimensional (k := k) c

local instance componentARSurplusAlgebraNoetherian
    (c : S.StandardFormWalkComponent) :
    IsNoetherianRing (S.standardFormComponentAlgebra (k := k) c)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

noncomputable local instance componentARSurplusGlobalAlgebraFiniteDimensional :
    FiniteDimensional k
      (S.standardFormAlgebra S.standardFormMeshHomFinite) :=
  S.standardFormAlgebra_finiteDimensional S.standardFormMeshHomFinite

local instance componentARSurplusGlobalAlgebraNoetherian :
    IsNoetherianRing
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ :=
  IsNoetherianRing.of_finite k _

/-- An indecomposable global module mapping nontrivially into an extended
component representable belongs to that component. -/
theorem standardFormComponentModuleExtensionByZero_locallyIndecomposableRightObjectClosedAt
    (c : S.StandardFormWalkComponent)
    (X : S.StandardFormComponentMeshCategory (k := k) c) :
    IsLocallyIndecomposableRightObjectClosedAt
      (S.standardFormComponentModuleExtensionByZero (k := k) c)
      ((S.standardFormComponentRestrictedYonedaFunctor (k := k) c).obj X) := by
  intro W hW g hg _
  let E := S.standardFormComponentModuleExtensionByZero (k := k) c
  let Y := S.standardFormRestrictedYonedaFunctor
    S.standardFormMeshHomFinite
  have hcomplete : ∃ j : Fin S.n, Nonempty
      (W ≅ Y.obj
        (MeshCategory.obj (k := k) S.standardFormRightMeshData j)) := by
    simpa only [standardFormProjectiveVertexModuleIndecomposableSkeleton]
      using (S.standardFormProjectiveVertexModuleIndecomposableSkeleton
        (k := k)).complete W hW
  obtain ⟨j, ⟨eW⟩⟩ := hcomplete
  let eX : E.obj
        ((S.standardFormComponentRestrictedYonedaFunctor
          (k := k) c).obj X) ≅
      Y.obj ((S.standardFormComponentMeshInclusion (k := k) c).obj X) :=
    (S.standardFormComponentRestrictedYonedaExtensionNatIso
      (k := k) c).app X
  let q : Y.obj
        (MeshCategory.obj (k := k) S.standardFormRightMeshData j) ⟶
      Y.obj ((S.standardFormComponentMeshInclusion (k := k) c).obj X) :=
    eW.inv ≫ g ≫ eX.hom
  have hq : q ≠ 0 := by
    intro hq0
    apply hg
    calc
      g = eW.hom ≫ q ≫ eX.inv := by simp [q]
      _ = 0 := by rw [hq0]; simp
  have hjc : S.standardFormWalkComponentClass j = c := by
    by_contra hjc
    let r : MeshCategory.obj (k := k) S.standardFormRightMeshData j ⟶
        (S.standardFormComponentMeshInclusion (k := k) c).obj X :=
      Y.preimage q
    have hclass : S.standardFormWalkComponentClass j ≠
        S.standardFormWalkComponentClass X.1 := by
      intro h
      exact hjc (h.trans X.2)
    have hr : r = 0 :=
      S.standardForm_meshHom_eq_zero_of_walkComponentClass_ne hclass r
    apply hq
    rw [← Y.map_preimage q, show Y.preimage q = 0 from hr, Y.map_zero]
  let Z : S.StandardFormComponentMeshCategory (k := k) c := ⟨j, hjc⟩
  refine ⟨(S.standardFormComponentRestrictedYonedaFunctor
    (k := k) c).obj Z, ⟨?_⟩⟩
  exact (S.standardFormComponentRestrictedYonedaExtensionNatIso
    (k := k) c).app Z ≪≫ eW.symm

/-- The ambient Auslander--Reiten surplus of a component category algebra is
the component surplus induced from the original standard-form quiver. -/
theorem standardFormComponentAlgebra_ambientARSurplus_eq_componentSurplus
    (c : S.StandardFormWalkComponent) :
    (S.standardFormComponentAlgebraIndecomposableSkeleton
      (k := k) c).ambientARSurplus =
      S.standardFormComponentSurplus c := by
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
  let Gsk := S.standardFormProjectiveVertexModuleIndecomposableSkeleton
    (k := k)
  let TC := Csk.toFiniteRightTauCategoryData
  let TG := Gsk.toFiniteRightTauCategoryData
  let E := S.standardFormComponentModuleExtensionByZero (k := k) c
  let AlgSk := S.standardFormAlgebraIndecomposableSkeleton (k := k)
  let TA := AlgSk.finiteTauCategoryData.toFiniteRightTauCategoryData
  let EA := S.standardFormProjectiveVertexModuleAlgebraEquivalence (k := k)
  letI : DecidablePred TC.IsProjective := Classical.decPred _
  letI : DecidablePred TG.IsProjective := Classical.decPred _
  letI : DecidablePred TA.IsProjective := Classical.decPred _
  letI : EnoughProjectives
      (RightModule.FinitelyGeneratedCategory
        (S.standardFormAlgebra S.standardFormMeshHomFinite)) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      (S.standardFormAlgebra S.standardFormMeshHomFinite)ᵐᵒᵖ
  have harity (i : Fin Csk.n) :
      FiniteTauMatrix.rightMiddleArity TC i =
        FiniteTauMatrix.rightMiddleArity TG
          (S.standardFormComponentVertexEquivFin c i).1 := by
    let x := S.standardFormComponentVertexEquivFin c i
    let d := FiniteTauMatrix.rightMiddleFiniteIndecomposableDecomposition TC i
    let dMap := d.mapOfIndecomposable E fun j ↦
      S.standardFormComponentModuleExtensionByZero_indec
        (k := k) c (d.summand j) (d.indecomposable j)
    let m := (TC.rightMesh (TC.obj i)).g ≫
      (TC.rightTermIso (TC.obj i)).hom
    let e : E.obj (TC.obj i) ≅ TG.obj x.1 := by
      change E.obj
          ((S.standardFormComponentRestrictedYonedaFunctor
            (k := k) c).obj x) ≅
        (S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite).obj
            ((S.standardFormComponentMeshInclusion (k := k) c).obj x)
      exact (S.standardFormComponentRestrictedYonedaExtensionNatIso
        (k := k) c).app x
    have hmAS : IsRightAlmostSplit m :=
      FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit TC i
    have hmMin : IsRightMinimal m :=
      FiniteTauMatrix.rightMesh_terminal_isRightMinimal TC i
    have hclosed :
        IsLocallyIndecomposableRightObjectClosedAt E (TC.obj i) := by
      change IsLocallyIndecomposableRightObjectClosedAt E
        ((S.standardFormComponentRestrictedYonedaFunctor
          (k := k) c).obj x)
      exact
        S.standardFormComponentModuleExtensionByZero_locallyIndecomposableRightObjectClosedAt
          (k := k) c x
    have hmapAS : IsRightAlmostSplit (E.map m ≫ e.hom) :=
      (rightAlmostSplit_map_of_full_faithful_of_finiteIndecomposableCore
        E finiteDimensionalModule_finiteIndecomposableDecomposition hmAS
          hclosed).postcomp_iso e
    have hmapMin : IsRightMinimal (E.map m ≫ e.hom) :=
      (rightMinimal_map_of_full_faithful E hmMin).postcomp_iso e
    have h :=
      FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
        TG x.1 dMap hmapAS hmapMin
    exact h.symm
  have hprojective (i : Fin Csk.n) :
      TC.IsProjective i ↔
        TG.IsProjective
          (S.standardFormComponentVertexEquivFin c i).1 := by
    let x := S.standardFormComponentVertexEquivFin c i
    rw [FiniteTauMatrix.isProjective_iff_projective_obj,
      FiniteTauMatrix.isProjective_iff_projective_obj]
    change Projective
        ((S.standardFormComponentRestrictedYonedaFunctor
          (k := k) c).obj x) ↔
      Projective
        ((S.standardFormRestrictedYonedaFunctor
          S.standardFormMeshHomFinite).obj
            (MeshCategory.obj (k := k) S.standardFormRightMeshData x.1))
    rw [S.standardFormComponentRestrictedYoneda_projective_iff_original
        (k := k) c x]
    exact (S.standardFormProjectiveVertexModule_projective_iff_original
      (k := k) x.1).symm
  have hlocalExtension (i : Fin Csk.n) :
      ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TC)
          TC.IsProjective i =
        ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TG)
          TG.IsProjective
            (S.standardFormComponentVertexEquivFin c i).1 := by
    let x := S.standardFormComponentVertexEquivFin c i
    calc
      ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TC)
          TC.IsProjective i =
          ARCount.localDensityOfIncomingArity
            (FiniteTauMatrix.rightMiddleArity TG x.1)
            (TG.IsProjective x.1) :=
        FiniteTauMatrix.localDensity_eq_localDensityOfIncomingArity
          TC i (FiniteTauMatrix.rightMiddleArity TG x.1)
            (harity i) (TG.IsProjective x.1) (hprojective i)
      _ = ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TG)
          TG.IsProjective x.1 :=
        (FiniteTauMatrix.localDensity_eq_localDensityOfIncomingArity
          TG x.1 (FiniteTauMatrix.rightMiddleArity TG x.1) rfl
            (TG.IsProjective x.1) Iff.rfl).symm
  let objIso (j : Fin Gsk.n) : EA.functor.obj (TG.obj j) ≅ TA.obj j :=
    (pushforwardRightModuleIndecomposableSkeletonObjIso EA Gsk j).symm
  have hlocalAlgebra (j : Fin Gsk.n) :
      ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TG)
          TG.IsProjective j =
        ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TA)
          TA.IsProjective j :=
    FiniteTauMatrix.localDensity_eq_of_equivalence
      TG TA EA (Equiv.refl (Fin Gsk.n)) objIso j
  let originalArrow : Fin S.n → Fin S.n → ℕ :=
    FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData
  let originalProjective : Fin S.n → Prop :=
    fun j ↦ Projective (S.fgObj j)
  letI : DecidablePred originalProjective := Classical.decPred _
  have hlocalOriginal (j : Fin Gsk.n) :
      ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TA)
          TA.IsProjective j =
        ARCount.localDensity originalArrow originalProjective j := by
    have hindegree :
        ARCount.indegree (FiniteTauMatrix.arrowMultiplicity TA) j =
          ARCount.indegree originalArrow j := by
      unfold ARCount.indegree
      apply Finset.sum_congr rfl
      intro x hx
      exact congrArg (fun n : ℕ ↦ (n : ℤ))
        (S.standardFormAlgebra_arrowMultiplicity_eq_original
          (k := k) x j)
    have hprojectiveOriginal : TA.IsProjective j ↔
        originalProjective j := by
      rw [FiniteTauMatrix.isProjective_iff_projective_obj]
      exact S.standardFormAlgebraSkeleton_projective_iff_original
        (k := k) j
    rw [ARCount.localDensity, ARCount.localDensity, hindegree]
    by_cases h : TA.IsProjective j
    · have h' : originalProjective j := hprojectiveOriginal.mp h
      simp [h, h']
    · have h' : ¬ originalProjective j := by
        intro hj
        exact h (hprojectiveOriginal.mpr hj)
      simp [h, h']
  have hlocalComponent (i : Fin Csk.n) :
      ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TC)
          TC.IsProjective i =
        ARCount.localDensity (S.standardFormComponentArrowMultiplicity c)
          (S.standardFormComponentIsProjective c)
            (S.standardFormComponentVertexEquivFin c i) := by
    let x := S.standardFormComponentVertexEquivFin c i
    calc
      ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TC)
          TC.IsProjective i =
          ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TG)
            TG.IsProjective x.1 := hlocalExtension i
      _ = ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TA)
            TA.IsProjective x.1 := hlocalAlgebra x.1
      _ = ARCount.localDensity originalArrow originalProjective x.1 :=
        hlocalOriginal x.1
      _ = ARCount.localDensity
            (S.standardFormComponentArrowMultiplicity c)
            (S.standardFormComponentIsProjective c) x := by
        symm
        exact ARCount.component_localDensity_eq originalArrow
          originalProjective S.standardFormWalkComponentClass
          (by
            intro source target hne
            exact S.standardForm_arrowMultiplicity_eq_zero_of_walkComponentClass_ne
              source target hne)
          c x
  let ComponentAlgSk :=
    S.standardFormComponentAlgebraIndecomposableSkeleton (k := k) c
  have hcategory :
      ARCount.surplus (FiniteTauMatrix.arrowMultiplicity TC)
          TC.IsProjective =
        ComponentAlgSk.ambientARSurplus := by
    exact
      CoveringHom.finiteCategoryProjectiveGenerator.categorySkeleton_surplus_eq_ambientARSurplus
        (S.standardFormComponentFiniteRightRepresentables (k := k) c)
        Csk ComponentAlgSk
  calc
    ComponentAlgSk.ambientARSurplus =
        ARCount.surplus (FiniteTauMatrix.arrowMultiplicity TC)
          TC.IsProjective := hcategory.symm
    _ = ∑ i : Fin Csk.n,
          ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TC)
            TC.IsProjective i :=
      (ARCount.sum_localDensity_eq_surplus
        (FiniteTauMatrix.arrowMultiplicity TC) TC.IsProjective).symm
    _ = ∑ x : S.StandardFormWalkComponentVertex c,
          ARCount.localDensity (S.standardFormComponentArrowMultiplicity c)
            (S.standardFormComponentIsProjective c) x := by
      exact Fintype.sum_equiv
        (S.standardFormComponentVertexEquivFin c)
        (fun i : Fin Csk.n ↦
          ARCount.localDensity (FiniteTauMatrix.arrowMultiplicity TC)
            TC.IsProjective i)
        (fun x : S.StandardFormWalkComponentVertex c ↦
          ARCount.localDensity (S.standardFormComponentArrowMultiplicity c)
            (S.standardFormComponentIsProjective c) x)
        hlocalComponent
    _ = S.standardFormComponentSurplus c :=
      ARCount.sum_localDensity_eq_surplus
        (S.standardFormComponentArrowMultiplicity c)
        (S.standardFormComponentIsProjective c)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
