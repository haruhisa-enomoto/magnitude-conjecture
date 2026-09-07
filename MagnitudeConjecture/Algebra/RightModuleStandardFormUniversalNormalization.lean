import MagnitudeConjecture.Algebra.RightModuleRepresentationFiniteSquareFree
import MagnitudeConjecture.Algebra.RightModuleStandardMeshNormalization
import MagnitudeConjecture.CategoryTheory.FiniteKrullSchmidtMatrix

/-!
# Local normalization on the standard-form universal cover

Square-freeness makes the indecomposable labels in a displayed mesh middle
term pairwise distinct.  If every realized sink is minimal right almost
split, then every assigned arrow is irreducible.  The paired arrows in one
lifted mesh therefore assemble into a minimal left almost-split map: after
factoring its components through the chosen left almost-split source, the
comparison endomorphism has invertible diagonal entries and hence is an
automorphism by the finite Krull--Schmidt matrix theorem.

Twisting the chosen right sink by the inverse comparison makes the lifted
mesh relation hold literally while preserving minimal right almost-splitness.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule

universe u

/-- Precomposition by an isomorphism preserves right minimality. -/
theorem rightMinimal_precomp_iso
    {C : Type*} [CategoryTheory.Category C] {E' E Z : C} {f : E ⟶ Z}
    (hf : IsRightMinimal f) (e : E' ≅ E) :
    IsRightMinimal (e.hom ≫ f) := by
  intro a ha
  let b : E ⟶ E := e.inv ≫ a ≫ e.hom
  have hb : b ≫ f = f := by
    apply (cancel_epi e.hom).1
    simpa only [b, Category.assoc, Iso.hom_inv_id_assoc] using ha
  letI : IsIso b := hf b hb
  let aIso : E' ≅ E' := e.trans ((asIso b).trans e.symm)
  have haIso : aIso.hom = a := by
    simp [aIso, b, Category.assoc]
  rw [← haIso]
  infer_instance

namespace FiniteIndecomposableSkeleton

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

local instance standardFormUniversalNormalizationQuiverInstance :
    Quiver (Fin S.n) :=
  S.standardFormQuiver

/-- The official middle labels of a standard-form right mesh are pairwise
distinct. -/
theorem standardFormRightMiddleLabel_injective (x : Fin S.n) :
    Function.Injective
      (FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData x) := by
  intro i j hij
  let y := FiniteTauMatrix.rightMiddleLabel
    S.finiteTauCategoryData.toFiniteRightTauCategoryData x i
  let oi : S.StandardFormOccurrence x y := ⟨i, rfl⟩
  let oj : S.StandardFormOccurrence x y := ⟨j, hij.symm⟩
  have ho : oi = oj := by
    apply (S.standardFormArrowOccurrenceEquiv x y).symm.injective
    exact (S.standardFormArrow_subsingleton x y).elim _ _
  exact congrArg Subtype.val ho

/-- A component cut out by a split inclusion from a minimal right
almost-split morphism between selected indecomposables is irreducible. -/
theorem isIrreducible_comp_of_rightAlmostSplit_rightMinimal
    {x y : Fin S.n}
    {E : RightModule.FinitelyGeneratedCategory A}
    (inc : S.fgObj x ⟶ E) (proj : E ⟶ S.fgObj x)
    (hinc : inc ≫ proj = 𝟙 (S.fgObj x))
    (g : E ⟶ S.fgObj y)
    (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g) :
    IsIrreducibleMorphism (inc ≫ g) := by
  have hnotepi : ¬ IsSplitEpi (inc ≫ g) := by
    intro hf
    obtain ⟨se⟩ := hf.exists_splitEpi
    apply hg.not_isSplitEpi
    exact IsSplitEpi.mk'
      { section_ := se.section_ ≫ inc
        id := by simpa only [Category.assoc] using se.id }
  have hnotmono : ¬ IsSplitMono (inc ≫ g) := by
    intro hf
    letI hfMono : IsSplitMono (inc ≫ g) := hf
    haveI : IsIso (inc ≫ g) :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
        (S.fgObj_indecomposable y) (inc ≫ g)
          (S.fgObj_indecomposable x).1
    exact hnotepi inferInstance
  refine ⟨hnotmono, hnotepi, ?_⟩
  intro M a b hab
  by_cases hb : IsSplitEpi b
  · exact Or.inr hb
  · obtain ⟨c, hc⟩ := hg.factors b hb
    let d : E ⟶ E := 𝟙 E + proj ≫ (a ≫ c - inc)
    have hdfix : d ≫ g = g := by
      dsimp only [d]
      rw [Preadditive.add_comp, Category.id_comp,
        Category.assoc, Preadditive.sub_comp]
      have hac : (a ≫ c) ≫ g = inc ≫ g := by
        rw [Category.assoc, hc, hab]
      rw [hac, sub_self, comp_zero, add_zero]
    have hincd : inc ≫ d = a ≫ c := by
      dsimp only [d]
      rw [Preadditive.comp_add, Category.comp_id,
        ← Category.assoc, hinc, Category.id_comp]
      abel
    letI : IsIso d := hgmin d hdfix
    exact Or.inl (IsSplitMono.mk'
      { retraction := c ≫ inv d ≫ proj
        id := by
          calc
            a ≫ (c ≫ inv d ≫ proj) =
                (a ≫ c) ≫ inv d ≫ proj := by
                  simp only [Category.assoc]
            _ = (inc ≫ d) ≫ inv d ≫ proj := by rw [hincd]
            _ = 𝟙 (S.fgObj x) := by
                  simp only [Category.assoc,
                    IsIso.hom_inv_id_assoc, hinc] })

/-- Under the global sink invariant, every universal-cover arrow
representative is irreducible. -/
theorem StandardFormUniversalSinkCondition.arrow_isIrreducible
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    {W Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : W ⟶ Z) :
    IsIrreducibleMorphism (D a) := by
  let inc := S.standardFormOccurrenceInclusion a.1
  let proj := S.standardFormOccurrenceProjection a.1
  let g := S.standardFormUniversalRealizedSink x₀ D W
  have hDcomp : D a = inc ≫ g := by
    rw [← S.standardFormUniversalSinkArrowMap_realizedSink x₀ D a]
    rfl
  rw [hDcomp]
  exact S.isIrreducible_comp_of_rightAlmostSplit_rightMinimal
    inc proj (S.standardFormOccurrenceInclusion_projection a.1) g
      (hD.rightAlmostSplit W) (hD.rightMinimal W)

/-- The representatives on the polarized partner arrows assemble into a
minimal left almost-split map.  More precisely, they differ from the chosen
right-mesh source by an automorphism of the displayed middle term. -/
theorem StandardFormUniversalSinkCondition.exists_realizedSource_iso
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    ∃ e : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂ ≅
        (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂,
      S.standardFormRightSource
          (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
            S.standardFormRightMeshData x₀ W) ≫ e.hom =
        S.standardFormUniversalRealizedSource x₀ D W := by
  classical
  let z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet} :=
    ⟨W.1.1, W.2⟩
  let E := (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂
  let n := FiniteTauMatrix.rightMiddleArity
    S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1
  let label := FiniteTauMatrix.rightMiddleLabel
    S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1
  let F : Fin n → FGModuleCat Aᵐᵒᵖ :=
    fun t ↦ S.almostSplitSkeleton.obj (label t)
  let eMiddle : E ≅ ⨁ F :=
    FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1.1
  let i : S.fgObj (S.standardFormTau z) ⟶ E :=
    S.standardFormRightSource z
  let q : S.fgObj (S.standardFormTau z) ⟶ E :=
    S.standardFormUniversalRealizedSource x₀ D W
  let component (t : Fin n) : S.fgObj (S.standardFormTau z) ⟶ F t :=
    q ≫ FiniteTauMatrix.rightMiddleProjection
      S.finiteTauCategoryData W.1.1 t
  have hcomponent (t : Fin n) :
      IsIrreducibleMorphism (component t) := by
    change IsIrreducibleMorphism
      (S.standardFormUniversalRealizedSource x₀ D W ≫
        FiniteTauMatrix.rightMiddleProjection
          S.finiteTauCategoryData W.1.1 t)
    rw [S.standardFormUniversalRealizedSource_rightMiddleProjection]
    exact hD.arrow_isIrreducible S x₀
      (S.standardFormUniversalPairedMiddleArrow x₀ W t)
  have hiAS : IsLeftAlmostSplit i :=
    S.standardFormRightSource_isLeftAlmostSplit z
  let factor (t : Fin n) : E ⟶ F t :=
    Classical.choose (hiAS.factors (component t)
      (hcomponent t).not_isSplitMono)
  have factor_spec (t : Fin n) : i ≫ factor t = component t :=
    Classical.choose_spec (hiAS.factors (component t)
      (hcomponent t).not_isSplitMono)
  have factor_splitEpi (t : Fin n) : IsSplitEpi (factor t) := by
    rcases (hcomponent t).factorization i (factor t) (factor_spec t) with
      hiSplit | htSplit
    · exact (hiAS.not_isSplitMono hiSplit).elim
    · exact htSplit
  let h : E ⟶ E := biproduct.lift factor ≫ eMiddle.inv
  have hih : i ≫ h = q := by
    apply (cancel_mono eMiddle.hom).1
    apply biproduct.hom_ext
    intro t
    change i ≫ h ≫ eMiddle.hom ≫ biproduct.π F t =
      q ≫ eMiddle.hom ≫ biproduct.π F t
    simp only [h, Category.assoc, Iso.inv_hom_id_assoc,
      biproduct.lift_π]
    exact factor_spec t
  have hlabel : Function.Injective label :=
    S.standardFormRightMiddleLabel_injective W.1.1
  let inc (t : Fin n) : F t ⟶ E :=
    biproduct.ι F t ≫ eMiddle.inv
  have hdiag (t : Fin n) : IsIso (inc t ≫ factor t) := by
    have hdiagSplit : IsSplitEpi (inc t ≫ factor t) := by
      by_contra hnot
      have hcomponentNot (j : Fin n) :
          ¬ IsSplitEpi (inc j ≫ factor t) := by
        by_cases hjt : j = t
        · subst j
          exact hnot
        · intro hsplit
          letI : IsSplitEpi (inc j ≫ factor t) := hsplit
          haveI : IsSplitMono (inc j ≫ factor t) :=
            S.almostSplitSkeleton.isSplitMono_of_isSplitEpi_between_obj
              (inc j ≫ factor t)
          haveI : IsIso (inc j ≫ factor t) :=
            isIso_of_mono_of_isSplitEpi (inc j ≫ factor t)
          apply hjt
          apply hlabel
          exact S.almostSplitSkeleton.eq_of_iso
            ⟨asIso (inc j ≫ factor t)⟩
      have hdesc : biproduct.desc (fun j ↦ inc j ≫ factor t) =
          eMiddle.inv ≫ factor t := by
        apply biproduct.hom_ext'
        intro j
        simp only [biproduct.ι_desc]
        rfl
      have hnonsplit :=
        S.almostSplitSkeleton.biproductDesc_not_isSplitEpi F
          (fun j ↦ inc j ≫ factor t) hcomponentNot
      apply hnonsplit
      rw [hdesc]
      letI : IsSplitEpi (factor t) := factor_splitEpi t
      infer_instance
    letI : IsSplitEpi (inc t ≫ factor t) := hdiagSplit
    haveI : IsSplitMono (inc t ≫ factor t) :=
      S.almostSplitSkeleton.isSplitMono_of_isSplitEpi_between_obj
        (inc t ≫ factor t)
    exact isIso_of_mono_of_isSplitEpi (inc t ≫ factor t)
  let hSum : (⨁ F) ⟶ ⨁ F := eMiddle.inv ≫ h ≫ eMiddle.hom
  have hpair (a b : Fin n) (hab : a ≠ b) :
      ¬ Nonempty (F a ≅ F b) := by
    intro e
    apply hab
    apply hlabel
    exact S.almostSplitSkeleton.eq_of_iso e
  have hsumDiag (t : Fin n) : IsIso
      (biproduct.ι F t ≫ hSum ≫ biproduct.π F t) := by
    simpa only [hSum, h, inc, eMiddle, F, Category.assoc,
      Iso.inv_hom_id_assoc, biproduct.lift_π] using hdiag t
  haveI : IsIso hSum :=
    MagnitudeConjecture.CategoryTheory.isIso_of_finBiproduct_diagonal_isIso
      F (fun t ↦ S.fgObj_indecomposable (label t))
      (fun t ↦ S.fgObj_end_isLocalRing (label t)) hpair hSum hsumDiag
  have heq : h = eMiddle.hom ≫ hSum ≫ eMiddle.inv := by
    simp [hSum, Category.assoc]
  haveI : IsIso h := by
    rw [heq]
    infer_instance
  exact ⟨asIso h, hih⟩

/-- The canonical comparison automorphism between the chosen mesh source
and the source assembled from a sink-compatible universal assignment. -/
def StandardFormUniversalSinkCondition.realizedSourceIso
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂ ≅
      (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂ :=
  Classical.choose (hD.exists_realizedSource_iso S x₀ W)

/-- The comparison automorphism realizes the assembled source exactly. -/
theorem StandardFormUniversalSinkCondition.rightSource_comp_realizedSourceIso
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    S.standardFormRightSource
        (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
          S.standardFormRightMeshData x₀ W) ≫
        (hD.realizedSourceIso S x₀ W).hom =
      S.standardFormUniversalRealizedSource x₀ D W :=
  Classical.choose_spec (hD.exists_realizedSource_iso S x₀ W)

/-- The source assembled from a sink-compatible universal assignment is
left almost split. -/
theorem StandardFormUniversalSinkCondition.realizedSource_isLeftAlmostSplit
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    IsLeftAlmostSplit
      (S.standardFormUniversalRealizedSource x₀ D W) := by
  rw [← hD.rightSource_comp_realizedSourceIso S x₀ W]
  exact leftAlmostSplit_postcomp_iso
    (S.standardFormRightSource_isLeftAlmostSplit
      (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
        S.standardFormRightMeshData x₀ W))
    (hD.realizedSourceIso S x₀ W)

/-- The source assembled from a sink-compatible universal assignment is
left minimal. -/
theorem StandardFormUniversalSinkCondition.realizedSource_isLeftMinimal
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    IsLeftMinimal
      (S.standardFormUniversalRealizedSource x₀ D W) := by
  rw [← hD.rightSource_comp_realizedSourceIso S x₀ W]
  exact leftMinimal_postcomp_iso
    (S.standardFormRightSource_isLeftMinimal
      (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
        S.standardFormRightMeshData x₀ W))
    (hD.realizedSourceIso S x₀ W)

/-- Twist the chosen downstairs right sink so that its source is the source
assembled from the current universal arrow assignment. -/
def StandardFormUniversalSinkCondition.normalizedSink
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂ ⟶
      S.fgObj W.1.1 :=
  (hD.realizedSourceIso S x₀ W).inv ≫
    S.standardFormRightSink W.1.1

/-- The locally normalized source and sink have zero composite. -/
@[reassoc (attr := simp)]
theorem StandardFormUniversalSinkCondition.realizedSource_comp_normalizedSink
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    S.standardFormUniversalRealizedSource x₀ D W ≫
        hD.normalizedSink S x₀ W = 0 := by
  rw [← hD.rightSource_comp_realizedSourceIso S x₀ W]
  unfold StandardFormUniversalSinkCondition.normalizedSink
  let e := hD.realizedSourceIso S x₀ W
  let z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet} :=
    ⟨W.1.1, W.2⟩
  change (S.standardFormRightSource z ≫ e.hom) ≫
    (e.inv ≫ S.standardFormRightSink W.1.1) = 0
  calc
    _ = S.standardFormRightSource z ≫
        ((e.hom ≫ e.inv) ≫ S.standardFormRightSink W.1.1) := by
      simp only [Category.assoc]
    _ = S.standardFormRightSource z ≫
        ((𝟙 _ : _ ⟶ _) ≫ S.standardFormRightSink W.1.1) := by
      rw [e.hom_inv_id]
    _ = S.standardFormRightSource z ≫
        S.standardFormRightSink W.1.1 := by
      rw [Category.id_comp]
    _ = 0 := S.standardFormRightSource_comp_rightSink z

/-- The locally normalized sink remains right almost split. -/
theorem StandardFormUniversalSinkCondition.normalizedSink_isRightAlmostSplit
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    IsRightAlmostSplit (hD.normalizedSink S x₀ W) := by
  exact rightAlmostSplit_precomp_iso
    (S.standardFormRightSink_isRightAlmostSplit W.1.1)
    (hD.realizedSourceIso S x₀ W).symm

/-- The locally normalized sink remains right minimal. -/
theorem StandardFormUniversalSinkCondition.normalizedSink_isRightMinimal
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    IsRightMinimal (hD.normalizedSink S x₀ W) := by
  exact rightMinimal_precomp_iso
    (S.standardFormRightSink_isRightMinimal W.1.1)
    (hD.realizedSourceIso S x₀ W).symm

/-- At one height, use the normalized sink at nonprojective vertices and
leave the current realized sink unchanged at projective vertices. -/
def StandardFormUniversalSinkCondition.heightSink
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (m : ℤ)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (_hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W = m) :
    (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
      S.fgObj W.1 := by
  classical
  by_cases hP : W ∈
      MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀
  · exact S.standardFormUniversalRealizedSink x₀ D W
  · exact hD.normalizedSink S x₀ ⟨W, hP⟩

theorem StandardFormUniversalSinkCondition.heightSink_eq_of_projective
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (m : ℤ)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W = m)
    (hP : W ∈ MeshCategory.RightMeshData.UniversalCover.projectiveSet
      S.standardFormRightMeshData x₀) :
    hD.heightSink S x₀ m W hW =
      S.standardFormUniversalRealizedSink x₀ D W := by
  simp [StandardFormUniversalSinkCondition.heightSink, hP]

theorem StandardFormUniversalSinkCondition.heightSink_eq_of_nonprojective
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (m : ℤ)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W = m)
    (hP : W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
      S.standardFormRightMeshData x₀) :
    hD.heightSink S x₀ m W hW =
      hD.normalizedSink S x₀ ⟨W, hP⟩ := by
  simp [StandardFormUniversalSinkCondition.heightSink, hP]

/-- Simultaneously normalize every nonprojective lifted mesh at one height,
while retaining projective sinks. -/
def StandardFormUniversalSinkCondition.normalizeAtHeight
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (m : ℤ) : S.StandardFormUniversalArrowAssignment x₀ :=
  S.replaceStandardFormUniversalArrowMapAtHeight x₀ D m
    (hD.heightSink S x₀ m)

/-- Height normalization preserves the global minimal right almost-split
sink invariant. -/
theorem StandardFormUniversalSinkCondition.normalizeAtHeight_sinkCondition
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (m : ℤ) :
    S.StandardFormUniversalSinkCondition x₀
      (hD.normalizeAtHeight S x₀ m) := by
  apply hD.replaceAtHeight S x₀ m (hD.heightSink S x₀ m)
  · intro W hW
    by_cases hP : W ∈
        MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀
    · rw [hD.heightSink_eq_of_projective S x₀ m W hW hP]
      exact hD.rightAlmostSplit W
    · rw [hD.heightSink_eq_of_nonprojective S x₀ m W hW hP]
      exact hD.normalizedSink_isRightAlmostSplit S x₀ ⟨W, hP⟩
  · intro W hW
    by_cases hP : W ∈
        MeshCategory.RightMeshData.UniversalCover.projectiveSet
          S.standardFormRightMeshData x₀
    · rw [hD.heightSink_eq_of_projective S x₀ m W hW hP]
      exact hD.rightMinimal W
    · rw [hD.heightSink_eq_of_nonprojective S x₀ m W hW hP]
      exact hD.normalizedSink_isRightMinimal S x₀ ⟨W, hP⟩

/-- Replacing sinks at height `m` does not change the source of a mesh whose
endpoint has height `m`: every paired arrow used by that source starts one
height lower. -/
theorem StandardFormUniversalSinkCondition.realizedSource_normalizeAtHeight_eq
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (m : ℤ)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W.1 = m) :
    S.standardFormUniversalRealizedSource x₀
        (hD.normalizeAtHeight S x₀ m) W =
      S.standardFormUniversalRealizedSource x₀ D W := by
  unfold standardFormUniversalRealizedSource
  congr 1
  apply congrArg biproduct.lift
  funext i
  change S.replaceStandardFormUniversalArrowMapAtHeight x₀ D m
      (hD.heightSink S x₀ m)
        (S.standardFormUniversalPairedMiddleArrow x₀ W i) =
    D (S.standardFormUniversalPairedMiddleArrow x₀ W i)
  apply S.replaceStandardFormUniversalArrowMapAtHeight_eq_of_ne
  have hmiddle :=
    MeshCategory.RightMeshData.UniversalCover.vertexHeight_arrow
      S.standardFormRightMeshData x₀
        (S.standardFormUniversalMiddleArrow x₀ W.1 i)
  rw [hW] at hmiddle
  omega

/-- Every nonprojective mesh at the selected height satisfies its literal
zero relation after simultaneous normalization. -/
theorem StandardFormUniversalSinkCondition.normalizeAtHeight_mesh_zero
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (m : ℤ)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W.1 = m) :
    S.standardFormUniversalRealizedSource x₀
        (hD.normalizeAtHeight S x₀ m) W ≫
      S.standardFormUniversalRealizedSink x₀
        (hD.normalizeAtHeight S x₀ m) W.1 = 0 := by
  rw [hD.realizedSource_normalizeAtHeight_eq S x₀ m W hW]
  unfold StandardFormUniversalSinkCondition.normalizeAtHeight
  rw [S.standardFormUniversalRealizedSink_replaceAtHeight_eq
    x₀ D m (hD.heightSink S x₀ m) W.1 hW]
  rw [hD.heightSink_eq_of_nonprojective S x₀ m W.1 hW W.2]
  exact hD.realizedSource_comp_normalizedSink S x₀ W

/-- An arrow assignment together with the global minimal right almost-split
sink invariant needed by the positive-height induction. -/
structure StandardFormUniversalSinkAssignment (x₀ : Fin S.n) where
  arrowMap : S.StandardFormUniversalArrowAssignment x₀
  sinkCondition : S.StandardFormUniversalSinkCondition x₀ arrowMap

/-- The occurrence-component assignment is the initial state of the
positive-height induction. -/
def standardFormUniversalInitialSinkAssignment (x₀ : Fin S.n) :
    S.StandardFormUniversalSinkAssignment x₀ where
  arrowMap := S.standardFormUniversalArrowMap x₀
  sinkCondition := S.standardFormUniversalArrowMap_sinkCondition x₀

/-- Normalize all sinks at one height while retaining the global sink
invariant. -/
def StandardFormUniversalSinkAssignment.normalizeAtHeight (x₀ : Fin S.n)
    (E : S.StandardFormUniversalSinkAssignment x₀) (m : ℤ) :
    S.StandardFormUniversalSinkAssignment x₀ where
  arrowMap := E.sinkCondition.normalizeAtHeight S x₀ m
  sinkCondition := E.sinkCondition.normalizeAtHeight_sinkCondition S x₀ m

/-- Stage `n` of the positive induction has normalized precisely the positive
heights `1, ..., n`. -/
def standardFormUniversalPositiveStage (x₀ : Fin S.n) :
    ℕ → S.StandardFormUniversalSinkAssignment x₀
  | 0 => S.standardFormUniversalInitialSinkAssignment x₀
  | n + 1 =>
      (standardFormUniversalPositiveStage x₀ n).normalizeAtHeight
        S x₀ (n + 1 : ℕ)

/-- The positive limiting assignment.  An arrow whose source has positive
height `n` takes its representative from stage `n`; arrows of nonpositive
source height retain their initial representatives. -/
def standardFormUniversalPositiveArrowMap (x₀ : Fin S.n) :
    S.StandardFormUniversalArrowAssignment x₀ :=
  fun {W Z} a ↦ by
    classical
    let h := MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W
    by_cases hp : 0 < h
    · exact (S.standardFormUniversalPositiveStage x₀ h.toNat).arrowMap a
    · exact S.standardFormUniversalArrowMap x₀ a

/-- At a source of natural-number height `n`, the positive limiting
assignment agrees with stage `n`. -/
theorem standardFormUniversalPositiveArrowMap_eq_stage_of_height_eq_nat
    (x₀ : Fin S.n) (n : ℕ)
    {W Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W = (n : ℤ)) (a : W ⟶ Z) :
    S.standardFormUniversalPositiveArrowMap x₀ a =
      (S.standardFormUniversalPositiveStage x₀ n).arrowMap a := by
  rcases n with _ | n
  · simp [standardFormUniversalPositiveArrowMap, hW,
      standardFormUniversalPositiveStage,
      standardFormUniversalInitialSinkAssignment]
  · simp [standardFormUniversalPositiveArrowMap, hW]

/-- The successor positive stage changes only arrows whose source has the
newly processed height. -/
theorem standardFormUniversalPositiveStage_succ_arrow_eq_of_height_ne
    (x₀ : Fin S.n) (n : ℕ)
    {W Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W ≠ ((n + 1 : ℕ) : ℤ)) (a : W ⟶ Z) :
    (S.standardFormUniversalPositiveStage x₀ (n + 1)).arrowMap a =
      (S.standardFormUniversalPositiveStage x₀ n).arrowMap a := by
  exact S.replaceStandardFormUniversalArrowMapAtHeight_eq_of_ne
    x₀ (S.standardFormUniversalPositiveStage x₀ n).arrowMap
      (n + 1 : ℕ)
      ((S.standardFormUniversalPositiveStage x₀ n).sinkCondition.heightSink
        S x₀ (n + 1 : ℕ)) hW a

/-- At a vertex of natural-number height `n`, the limiting realized sink is
already the sink of stage `n`. -/
theorem standardFormUniversalPositiveRealizedSink_eq_stage
    (x₀ : Fin S.n) (n : ℕ)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W = (n : ℤ)) :
    S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalPositiveArrowMap x₀) W =
      S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalPositiveStage x₀ n).arrowMap W := by
  unfold standardFormUniversalRealizedSink
  congr 1
  apply congrArg biproduct.desc
  funext i
  exact S.standardFormUniversalPositiveArrowMap_eq_stage_of_height_eq_nat
    x₀ n hW (S.standardFormUniversalMiddleArrow x₀ W i)

/-- For a mesh ending at height `n + 1`, its source in the limiting
assignment is already its source at stage `n + 1`.  Its paired arrows start
at height `n`, so the successor stage leaves them unchanged. -/
theorem standardFormUniversalPositiveRealizedSource_eq_stage_succ
    (x₀ : Fin S.n) (n : ℕ)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W.1 = ((n + 1 : ℕ) : ℤ)) :
    S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalPositiveArrowMap x₀) W =
      S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalPositiveStage x₀ (n + 1)).arrowMap W := by
  unfold standardFormUniversalRealizedSource
  congr 1
  apply congrArg biproduct.lift
  funext i
  have hmiddle :=
    MeshCategory.RightMeshData.UniversalCover.vertexHeight_arrow
      S.standardFormRightMeshData x₀
        (S.standardFormUniversalMiddleArrow x₀ W.1 i)
  have hmiddleNat :
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
        S.standardFormRightMeshData x₀
          (S.standardFormUniversalMiddleVertex x₀ W.1 i) = (n : ℤ) := by
    rw [hW] at hmiddle
    omega
  calc
    S.standardFormUniversalPositiveArrowMap x₀
        (S.standardFormUniversalPairedMiddleArrow x₀ W i) =
        (S.standardFormUniversalPositiveStage x₀ n).arrowMap
          (S.standardFormUniversalPairedMiddleArrow x₀ W i) :=
      S.standardFormUniversalPositiveArrowMap_eq_stage_of_height_eq_nat
        x₀ n hmiddleNat (S.standardFormUniversalPairedMiddleArrow x₀ W i)
    _ = (S.standardFormUniversalPositiveStage x₀ (n + 1)).arrowMap
          (S.standardFormUniversalPairedMiddleArrow x₀ W i) := by
      symm
      apply S.standardFormUniversalPositiveStage_succ_arrow_eq_of_height_ne
        x₀ n
      omega

/-- Every mesh whose endpoint has positive natural-number height satisfies
its literal zero relation in the positive limiting assignment. -/
theorem standardFormUniversalPositive_mesh_zero_of_height_eq_succ
    (x₀ : Fin S.n) (n : ℕ)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W.1 = ((n + 1 : ℕ) : ℤ)) :
    S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalPositiveArrowMap x₀) W ≫
      S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalPositiveArrowMap x₀) W.1 = 0 := by
  rw [S.standardFormUniversalPositiveRealizedSource_eq_stage_succ
    x₀ n W hW]
  rw [S.standardFormUniversalPositiveRealizedSink_eq_stage
    x₀ (n + 1) W.1 hW]
  exact
    (S.standardFormUniversalPositiveStage x₀ n).sinkCondition
      |>.normalizeAtHeight_mesh_zero S x₀ (n + 1 : ℕ) W hW

/-- At a nonpositive source height, the positive induction leaves the
realized sink equal to its initial value. -/
theorem standardFormUniversalPositiveRealizedSink_eq_initial_of_nonpos
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W ≤ 0) :
    S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalPositiveArrowMap x₀) W =
      S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalArrowMap x₀) W := by
  unfold standardFormUniversalRealizedSink
  congr 1
  apply congrArg biproduct.desc
  funext i
  simp [standardFormUniversalPositiveArrowMap, hW.not_gt]

/-- Passing to the pointwise positive limit preserves the global minimal
right almost-split sink invariant. -/
theorem standardFormUniversalPositiveArrowMap_sinkCondition (x₀ : Fin S.n) :
    S.StandardFormUniversalSinkCondition x₀
      (S.standardFormUniversalPositiveArrowMap x₀) where
  rightAlmostSplit W := by
    let h := MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W
    by_cases hp : 0 < h
    · have hnat :
          MeshCategory.RightMeshData.UniversalCover.vertexHeight
              S.standardFormRightMeshData x₀ W = (h.toNat : ℤ) := by
        exact (Int.toNat_of_nonneg hp.le).symm
      rw [S.standardFormUniversalPositiveRealizedSink_eq_stage
        x₀ h.toNat W hnat]
      exact
        (S.standardFormUniversalPositiveStage x₀ h.toNat).sinkCondition
          |>.rightAlmostSplit W
    · rw [S.standardFormUniversalPositiveRealizedSink_eq_initial_of_nonpos
        x₀ W (le_of_not_gt hp)]
      exact (S.standardFormUniversalArrowMap_sinkCondition x₀)
        |>.rightAlmostSplit W
  rightMinimal W := by
    let h := MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W
    by_cases hp : 0 < h
    · have hnat :
          MeshCategory.RightMeshData.UniversalCover.vertexHeight
              S.standardFormRightMeshData x₀ W = (h.toNat : ℤ) := by
        exact (Int.toNat_of_nonneg hp.le).symm
      rw [S.standardFormUniversalPositiveRealizedSink_eq_stage
        x₀ h.toNat W hnat]
      exact
        (S.standardFormUniversalPositiveStage x₀ h.toNat).sinkCondition
          |>.rightMinimal W
    · rw [S.standardFormUniversalPositiveRealizedSink_eq_initial_of_nonpos
        x₀ W (le_of_not_gt hp)]
      exact (S.standardFormUniversalArrowMap_sinkCondition x₀)
        |>.rightMinimal W

/-- Every nonprojective mesh at positive height satisfies its literal zero
relation in the positive limiting assignment. -/
theorem standardFormUniversalPositive_mesh_zero (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (hW : 0 < MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W.1) :
    S.standardFormUniversalRealizedSource x₀
        (S.standardFormUniversalPositiveArrowMap x₀) W ≫
      S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalPositiveArrowMap x₀) W.1 = 0 := by
  let h := MeshCategory.RightMeshData.UniversalCover.vertexHeight
    S.standardFormRightMeshData x₀ W.1
  let n := h.toNat - 1
  apply S.standardFormUniversalPositive_mesh_zero_of_height_eq_succ x₀ n W
  have hnat : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hW.le
  dsimp only [n]
  omega

end FiniteIndecomposableSkeleton

end MagnitudeConjecture.RightModule
