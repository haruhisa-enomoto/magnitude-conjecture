import MagnitudeConjecture.Algebra.RightModuleStandardFormMesh
import MagnitudeConjecture.CategoryTheory.FiniteTauAlmostSplitMultiplicity
import MagnitudeConjecture.CategoryTheory.FiniteTauIrreducible
import MagnitudeConjecture.CategoryTheory.TranslationQuiverUniversalGrading

/-!
# Irreducible representatives of standard-form arrows

The standard-form AR quiver indexes parallel arrows by the numerical
arrow-multiplicity entry.  Here that finite index is identified with the
literal occurrences of the required label in the chosen right almost-split
middle term.  The corresponding middle-term components give concrete
irreducible module morphisms.  Pulling this assignment to the based universal
cover supplies the initial arrow representatives for the two-sided
Bongartz--Gabriel normalization.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open QuotientSubmoduleEquidistribution.CategoricalRadical

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

private theorem isIrreducibleMorphism_eqToHom_comp
    {C : Type*} [Category C] {X X' Y : C} (h : X = X')
    (f : X' ⟶ Y) (hf : IsIrreducibleMorphism f) :
    IsIrreducibleMorphism (eqToHom h ≫ f) := by
  subst X'
  simpa using hf

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Occurrences of `y` in the chosen right almost-split middle term ending at
`x`. -/
abbrev StandardFormOccurrence (x y : Fin S.n) :=
  {i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x) //
    FiniteTauMatrix.rightMiddleLabel
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x i = y}

/-- The number of literal occurrences with endpoints `(y,x)` is the official
standard-form arrow multiplicity. -/
theorem card_standardFormOccurrence (x y : Fin S.n) :
    Fintype.card (S.StandardFormOccurrence x y) =
      FiniteTauMatrix.arrowMultiplicity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData y x := by
  classical
  rw [FiniteTauMatrix.arrowMultiplicity, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : FiniteTauMatrix.rightMiddleLabel
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x i = y <;>
    simp [hi]

/-- Abstract standard-form arrows are canonically chosen representatives of
the corresponding literal middle-term occurrences. -/
def standardFormArrowOccurrenceEquiv (x y : Fin S.n) :
    S.StandardFormArrow x y ≃ S.StandardFormOccurrence x y :=
  (Fintype.equivFinOfCardEq (S.card_standardFormOccurrence x y)).symm

/-- Forgetting the retained label identifies the disjoint union of all
occurrence fibres with the full finite middle-index type. -/
def standardFormOccurrenceMiddleIndexEquiv (x : Fin S.n) :
    (Σ y : Fin S.n, S.StandardFormOccurrence x y) ≃
      Fin (FiniteTauMatrix.rightMiddleArity
        S.finiteTauCategoryData.toFiniteRightTauCategoryData x) where
  toFun a := a.2.1
  invFun i :=
    ⟨FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData x i,
      ⟨i, rfl⟩⟩
  left_inv a := by
    rcases a with ⟨y, i, hi⟩
    subst y
    rfl
  right_inv _ := rfl

/-- The displayed middle indices at `x` are exactly the standard-form arrows
leaving `x`, with the target label retained in the dependent sum. -/
def standardFormMiddleIndexEquiv (x : Fin S.n) :
    Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x) ≃
      Σ y : Fin S.n, S.StandardFormArrow x y :=
  ((Equiv.sigmaCongrRight fun y ↦ S.standardFormArrowOccurrenceEquiv x y).trans
    (S.standardFormOccurrenceMiddleIndexEquiv x)).symm

@[simp]
theorem standardFormMiddleIndexEquiv_fst (x : Fin S.n)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x)) :
    (S.standardFormMiddleIndexEquiv x i).1 =
      FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData x i :=
  rfl

@[simp]
theorem standardFormArrowOccurrenceEquiv_middleIndex (x : Fin S.n)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x)) :
    S.standardFormArrowOccurrenceEquiv x
        (S.standardFormMiddleIndexEquiv x i).1
        (S.standardFormMiddleIndexEquiv x i).2 =
      ⟨i, S.standardFormMiddleIndexEquiv_fst x i⟩ := by
  apply Subtype.ext
  exact ((Equiv.sigmaCongrRight fun y ↦
    S.standardFormArrowOccurrenceEquiv x y).trans
      (S.standardFormOccurrenceMiddleIndexEquiv x)).apply_symm_apply i

/-- The irreducible module morphism represented by one reversed
standard-form arrow. -/
def standardFormArrowMap {x y : Fin S.n}
    (a : S.StandardFormArrow x y) :
    S.fgObj y ⟶ S.fgObj x := by
  let i := S.standardFormArrowOccurrenceEquiv x y a
  exact eqToHom (congrArg S.fgObj i.2.symm) ≫
    FiniteTauMatrix.rightMiddleComponent
      S.finiteTauCategoryData x i.1

/-- The arrow attached to the `i`-th middle index is its actual chosen
right-mesh component. -/
@[simp]
theorem standardFormArrowMap_middleIndex (x : Fin S.n)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x)) :
    S.standardFormArrowMap (S.standardFormMiddleIndexEquiv x i).2 =
      FiniteTauMatrix.rightMiddleComponent
        S.finiteTauCategoryData x i := by
  let a := S.standardFormMiddleIndexEquiv x i
  let j := S.standardFormArrowOccurrenceEquiv x a.1 a.2
  have hj : j = ⟨i, S.standardFormMiddleIndexEquiv_fst x i⟩ :=
    S.standardFormArrowOccurrenceEquiv_middleIndex x i
  change eqToHom (congrArg S.fgObj j.2.symm) ≫
      FiniteTauMatrix.rightMiddleComponent
        S.finiteTauCategoryData x j.1 =
    FiniteTauMatrix.rightMiddleComponent S.finiteTauCategoryData x i
  rw [hj]
  change 𝟙 (S.fgObj (FiniteTauMatrix.rightMiddleLabel
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x i)) ≫
      FiniteTauMatrix.rightMiddleComponent
        S.finiteTauCategoryData x i = _
  simp

@[simp]
theorem finiteTauCategoryData_obj (x : Fin S.n) :
    S.finiteTauCategoryData.obj x = S.fgObj x :=
  rfl

/-- The terminal map of the chosen right mesh, after identifying its endpoint
with the selected indecomposable representative. -/
def standardFormRightSink (x : Fin S.n) :
    (S.finiteTauCategoryData.rightMesh (S.fgObj x)).X₂ ⟶ S.fgObj x :=
  (S.finiteTauCategoryData.rightMesh (S.fgObj x)).g ≫
    (S.finiteTauCategoryData.rightTermIso (S.fgObj x)).hom

/-- The chosen standard-form right sink is right almost split. -/
theorem standardFormRightSink_isRightAlmostSplit (x : Fin S.n) :
    IsRightAlmostSplit (S.standardFormRightSink x) := by
  simpa only [standardFormRightSink, S.finiteTauCategoryData_obj] using
    (FiniteTauMatrix.rightMesh_terminal_isRightAlmostSplit
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x)

/-- The chosen standard-form right sink is right minimal. -/
theorem standardFormRightSink_isRightMinimal (x : Fin S.n) :
    IsRightMinimal (S.standardFormRightSink x) := by
  simpa only [standardFormRightSink, S.finiteTauCategoryData_obj] using
    (FiniteTauMatrix.rightMesh_terminal_isRightMinimal
      S.finiteTauCategoryData.toFiniteRightTauCategoryData x)

/-- Take the occurrence component of an arbitrary replacement sink at one
standard-form vertex. -/
def standardFormSinkArrowMap {x y : Fin S.n}
    (g : (S.finiteTauCategoryData.rightMesh (S.fgObj x)).X₂ ⟶
      S.fgObj x)
    (a : S.StandardFormArrow x y) :
    S.fgObj y ⟶ S.fgObj x := by
  let i := S.standardFormArrowOccurrenceEquiv x y a
  exact eqToHom (congrArg S.fgObj i.2.symm) ≫
    FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData x i.1 ≫ g

/-- The initial arrow representative is the occurrence component of the
chosen right almost-split sink. -/
theorem standardFormSinkArrowMap_rightSink {x y : Fin S.n}
    (a : S.StandardFormArrow x y) :
    S.standardFormSinkArrowMap (S.standardFormRightSink x) a =
      S.standardFormArrowMap a := by
  simp [standardFormSinkArrowMap, standardFormArrowMap,
    standardFormRightSink, FiniteTauMatrix.rightMiddleComponent]

/-- Every chosen standard-form arrow representative is irreducible. -/
theorem standardFormArrowMap_isIrreducible {x y : Fin S.n}
    (a : S.StandardFormArrow x y) :
    IsIrreducibleMorphism (S.standardFormArrowMap a) := by
  let i := S.standardFormArrowOccurrenceEquiv x y a
  apply isIrreducibleMorphism_eqToHom_comp
  exact FiniteTauMatrix.rightMiddleComponent_isIrreducible
    S.finiteTauCategoryData x i.1

/-- A nonprojective standard-form vertex as the corresponding nonzero right
boundary of the finite tau-category. -/
def standardFormFiniteTauNonprojective
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    S.finiteTauCategoryData.Nonprojective :=
  (S.canonicalRightNonzeroEquivNonprojective).symm
    ⟨z.1, by simpa [standardFormProjectiveSet] using z.2⟩

@[simp]
theorem standardFormFiniteTauNonprojective_val
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    (S.standardFormFiniteTauNonprojective z).1 = z.1 :=
  rfl

/-- The finite-tau positive translate and the standard-form translation have
the same underlying label. -/
theorem finiteTauCategoryData_tauPlus_standardFormTau
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    S.finiteTauCategoryData.tauPlus
        (S.standardFormFiniteTauNonprojective z) =
      S.standardFormTau z := by
  change (S.canonicalTauPlusEquiv
      (S.standardFormFiniteTauNonprojective z)).1 =
    (S.rightTranslationEquiv
      ⟨z.1, by simpa [standardFormProjectiveSet] using z.2⟩).1
  rw [S.canonicalTauPlusEquiv_val]
  congr 2

/-- The first map of the chosen right mesh, with its source identified with
the standard-form translate. -/
def standardFormRightSource
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    S.fgObj (S.standardFormTau z) ⟶
      (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).X₂ :=
  eqToHom (congrArg S.fgObj
      (S.finiteTauCategoryData_tauPlus_standardFormTau z).symm) ≫
    (S.finiteTauCategoryData.tauPlusIso
      (S.standardFormFiniteTauNonprojective z)).inv ≫
    (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).f

/-- The first map of the chosen nonprojective standard-form right mesh is
monic: it is the selected Auslander--Reiten kernel inclusion, up to the two
displayed source identifications. -/
theorem standardFormRightSource_mono
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    Mono (S.standardFormRightSource z) := by
  have hf : Mono
      (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).f := by
    change Mono (S.canonicalRightMesh (S.fgObj z.1)).f
    rw [S.canonicalRightMesh_at_label z.1]
    exact S.labelRightMesh_f_mono z.1
  letI : Mono (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).f := hf
  unfold standardFormRightSource
  exact mono_comp' (by infer_instance) (mono_comp' (by infer_instance) hf)

/-- The identified first map of a chosen nonprojective right mesh is left
almost split. -/
theorem standardFormRightSource_isLeftAlmostSplit
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    IsLeftAlmostSplit (S.standardFormRightSource z) := by
  let T := S.finiteTauCategoryData
  let zT := S.standardFormFiniteTauNonprojective z
  let f : T.obj (T.tauPlus zT) ⟶ (T.rightMesh (T.obj zT.1)).X₂ :=
    (T.tauPlusIso zT).inv ≫ (T.rightMesh (T.obj zT.1)).f
  have hf : IsLeftAlmostSplit f := by
    constructor
    · have hrad : IsRadicalMorphism f :=
        isRadicalMorphism_precomp (T.tauPlusIso zT).inv
          (T.rightTau (T.obj z.1)).f_radical
      exact (T.isRadicalMorphism_iff_not_isSplitMono_from_obj f).1 hrad
    · intro Y g hg
      have hgrad : IsRadicalMorphism g :=
        (T.isRadicalMorphism_iff_not_isSplitMono_from_obj g).2 hg
      have hgrad' : IsRadicalMorphism ((T.tauPlusIso zT).hom ≫ g) :=
        isRadicalMorphism_precomp (T.tauPlusIso zT).hom hgrad
      obtain ⟨b, hb⟩ :=
        (T.rightTau (T.obj zT.1)).factors_from_left
          ((T.tauPlusIso zT).hom ≫ g) hgrad'
      refine ⟨b, ?_⟩
      dsimp only [f]
      calc
        ((T.tauPlusIso zT).inv ≫
              (T.rightMesh (T.obj zT.1)).f) ≫ b =
            (T.tauPlusIso zT).inv ≫
              ((T.rightMesh (T.obj zT.1)).f ≫ b) :=
          Category.assoc _ _ _
        _ = (T.tauPlusIso zT).inv ≫
              ((T.tauPlusIso zT).hom ≫ g) := by rw [hb]
        _ = g := by simp
  let e : S.fgObj (S.standardFormTau z) ≅ T.obj (T.tauPlus zT) :=
    eqToIso (congrArg S.fgObj
      (S.finiteTauCategoryData_tauPlus_standardFormTau z).symm)
  simpa [standardFormRightSource, f, e, T, zT, Category.assoc] using
    hf.precomp_iso e

/-- The identified first map of a chosen nonprojective right mesh is left
minimal. -/
theorem standardFormRightSource_isLeftMinimal
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    IsLeftMinimal (S.standardFormRightSource z) := by
  let e : S.fgObj (S.standardFormTau z) ≅
      (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).X₁ :=
    (eqToIso (congrArg S.fgObj
      (S.finiteTauCategoryData_tauPlus_standardFormTau z).symm)).trans
        (S.finiteTauCategoryData.tauPlusIso
          (S.standardFormFiniteTauNonprojective z)).symm
  simpa [standardFormRightSource, e, Category.assoc] using
    (FiniteTauMatrix.rightMesh_f_isLeftMinimal
      S.finiteTauCategoryData
        (S.standardFormFiniteTauNonprojective z)).precomp_iso e

/-- The identified chosen right-mesh source and sink have zero composite. -/
@[reassoc (attr := simp)]
theorem standardFormRightSource_comp_rightSink
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet}) :
    S.standardFormRightSource z ≫ S.standardFormRightSink z.1 = 0 := by
  unfold standardFormRightSource standardFormRightSink
  simp only [Category.assoc]
  erw [← Category.assoc
    (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).f
    (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).g]
  rw [(S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).zero,
    zero_comp]
  erw [comp_zero]

/-- The identified first map of a chosen nonprojective right mesh is a weak
kernel of its identified sink.  Thus every morphism killed by the sink
factors through the standard-form translate. -/
theorem standardFormRightSource_factors_of_comp_rightSink_eq_zero
    (z : {z : Fin S.n // z ∉ S.standardFormProjectiveSet})
    {X : FGModuleCat Aᵐᵒᵖ}
    (q : X ⟶ (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).X₂)
    (hq : q ≫ S.standardFormRightSink z.1 = 0) :
    ∃ t : X ⟶ S.fgObj (S.standardFormTau z),
      t ≫ S.standardFormRightSource z = q := by
  let zT := S.standardFormFiniteTauNonprojective z
  have hqg : q ≫
      (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).g = 0 := by
    apply (cancel_mono
      (S.finiteTauCategoryData.rightTermIso (S.fgObj z.1)).hom).1
    simpa only [standardFormRightSink, Category.assoc, comp_zero,
      zero_comp] using hq
  obtain ⟨t, ht⟩ :=
    (S.finiteTauCategoryData.rightTau
      (S.fgObj z.1)).exact_postcomp X q |>.mp hqg
  let e : S.fgObj (S.standardFormTau z) ≅
      (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).X₁ :=
    (eqToIso (congrArg S.fgObj
      (S.finiteTauCategoryData_tauPlus_standardFormTau z).symm)).trans
        (S.finiteTauCategoryData.tauPlusIso zT).symm
  refine ⟨t ≫ e.inv, ?_⟩
  change (t ≫ e.inv) ≫
    (e.hom ≫ (S.finiteTauCategoryData.rightMesh (S.fgObj z.1)).f) = q
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using ht

section UniversalCover

variable [IsAlgClosed k]

local instance standardFormArrowQuiverInstance : Quiver (Fin S.n) :=
  S.standardFormQuiver

/-- The finite middle index at a cover vertex, regarded as its corresponding
outgoing arrow downstairs. -/
def standardFormUniversalMiddleBaseStar (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    Quiver.Star W.1 :=
  S.standardFormMiddleIndexEquiv W.1 i

/-- The target cover vertex obtained by lifting one displayed middle
occurrence from `W`. -/
def standardFormUniversalMiddleVertex (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀ :=
  MeshCategory.RightMeshData.UniversalCover.extendOld
    S.standardFormRightMeshData x₀ W
      (S.standardFormUniversalMiddleBaseStar x₀ W i).2

/-- The unique lifted outgoing arrow represented by one displayed middle
occurrence. -/
def standardFormUniversalMiddleArrow (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    W ⟶ S.standardFormUniversalMiddleVertex x₀ W i :=
  ⟨(S.standardFormUniversalMiddleBaseStar x₀ W i).2, rfl⟩

@[simp]
theorem standardFormUniversalMiddleVertex_base (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    (S.standardFormUniversalMiddleVertex x₀ W i).1 =
      FiniteTauMatrix.rightMiddleLabel
        S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i :=
  rfl

@[simp]
theorem standardFormUniversalMiddleArrow_val (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    (S.standardFormUniversalMiddleArrow x₀ W i).1 =
      (S.standardFormMiddleIndexEquiv W.1 i).2 :=
  rfl

/-- The displayed middle indices exhaust the outgoing star at every
universal-cover vertex. -/
def standardFormUniversalMiddleStarEquiv (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1) ≃
      Quiver.Star W :=
  (S.standardFormMiddleIndexEquiv W.1).trans
    (Equiv.ofBijective
      ((MeshCategory.RightMeshData.UniversalCover.projection
        S.standardFormRightMeshData x₀).star W)
      (MeshCategory.RightMeshData.UniversalCover.projection_star_bijective
        S.standardFormRightMeshData x₀ W)).symm

/-- The abstract star-equivalence lift is the explicit arrow obtained by
`extendOld`. -/
theorem standardFormUniversalMiddleStarEquiv_apply (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    S.standardFormUniversalMiddleStarEquiv x₀ W i =
      ⟨S.standardFormUniversalMiddleVertex x₀ W i,
        S.standardFormUniversalMiddleArrow x₀ W i⟩ := by
  apply (MeshCategory.RightMeshData.UniversalCover.projection_star_bijective
    S.standardFormRightMeshData x₀ W).1
  exact (Equiv.ofBijective
    ((MeshCategory.RightMeshData.UniversalCover.projection
      S.standardFormRightMeshData x₀).star W)
    (MeshCategory.RightMeshData.UniversalCover.projection_star_bijective
      S.standardFormRightMeshData x₀ W)).apply_symm_apply
        (S.standardFormMiddleIndexEquiv W.1 i)

/-- The downstairs module object attached to a universal-cover vertex. -/
def standardFormUniversalObj (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) : FGModuleCat.{u} Aᵐᵒᵖ :=
  S.fgObj W.1

/-- An arbitrary choice of module representative for every reversed arrow of
the based universal cover. -/
abbrev StandardFormUniversalArrowAssignment (x₀ : Fin S.n) :=
  ∀ {W Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}, (W ⟶ Z) →
    (S.standardFormUniversalObj x₀ Z ⟶
      S.standardFormUniversalObj x₀ W)

/-- The polarized partner of the lifted arrow represented by one displayed
middle occurrence at a nonprojective cover vertex. -/
def standardFormUniversalPairedMiddleArrow (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1)) :
    S.standardFormUniversalMiddleVertex x₀ W.1 i ⟶
      MeshCategory.RightMeshData.UniversalCover.tau
        S.standardFormRightMeshData x₀ W :=
  MeshCategory.RightMeshData.UniversalCover.pairedArrow
    S.standardFormRightMeshData x₀ W
      (S.standardFormUniversalMiddleVertex x₀ W.1 i)
      (S.standardFormUniversalMiddleArrow x₀ W.1 i)

@[simp]
theorem standardFormUniversalPairedMiddleArrow_val (x₀ : Fin S.n)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1)) :
    (S.standardFormUniversalPairedMiddleArrow x₀ W i).1 =
      (S.standardFormRightMeshData.arrowEquiv
        (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
          S.standardFormRightMeshData x₀ W)
        (S.standardFormUniversalMiddleVertex x₀ W.1 i).1)
          (S.standardFormMiddleIndexEquiv W.1.1 i).2 :=
  rfl

/-- Assemble the representatives on the polarized partner arrows into the
source map of the lifted mesh at `W`. -/
def standardFormUniversalRealizedSource (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀}) :
    S.fgObj (S.standardFormTau
        (MeshCategory.RightMeshData.UniversalCover.baseNonprojective
          S.standardFormRightMeshData x₀ W)) ⟶
      (S.finiteTauCategoryData.rightMesh (S.fgObj W.1.1)).X₂ :=
  biproduct.lift (fun i ↦
      D (S.standardFormUniversalPairedMiddleArrow x₀ W i)) ≫
    (FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1.1).inv

/-- Projection to the `i`-th displayed summand recovers the representative
on its polarized partner arrow. -/
@[reassoc (attr := simp)]
theorem standardFormUniversalRealizedSource_rightMiddleProjection
    (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    (W : {W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀ //
      W ∉ MeshCategory.RightMeshData.UniversalCover.projectiveSet
        S.standardFormRightMeshData x₀})
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1.1)) :
    S.standardFormUniversalRealizedSource x₀ D W ≫
      FiniteTauMatrix.rightMiddleProjection
        S.finiteTauCategoryData W.1.1 i =
      D (S.standardFormUniversalPairedMiddleArrow x₀ W i) := by
  unfold standardFormUniversalRealizedSource
    FiniteTauMatrix.rightMiddleProjection
  erw [Category.assoc, Iso.inv_hom_id_assoc, biproduct.lift_π]

/-- Reassemble all arrow representatives leaving `W` into a single map from
the chosen right-mesh middle term to its endpoint. -/
def standardFormUniversalRealizedSink (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
      S.fgObj W.1 :=
  (FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1).hom ≫
    biproduct.desc (fun i ↦
      D (S.standardFormUniversalMiddleArrow x₀ W i))

/-- The `i`-th component of the reassembled sink is the representative on
the corresponding lifted arrow. -/
@[reassoc (attr := simp)]
theorem rightMiddleInclusion_standardFormUniversalRealizedSink
    (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    FiniteTauMatrix.rightMiddleInclusion
        S.finiteTauCategoryData W.1 i ≫
      S.standardFormUniversalRealizedSink x₀ D W =
        D (S.standardFormUniversalMiddleArrow x₀ W i) := by
  simp [FiniteTauMatrix.rightMiddleInclusion,
    standardFormUniversalRealizedSink, Category.assoc]

/-- Initial irreducible arrow representatives on the universal cover, pulled
back from the chosen standard-form occurrence representatives. -/
def standardFormUniversalArrowMap (x₀ : Fin S.n)
    {W Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : W ⟶ Z) :
    S.standardFormUniversalObj x₀ Z ⟶
      S.standardFormUniversalObj x₀ W :=
  S.standardFormArrowMap a.1

/-- Every initial universal-cover arrow representative is irreducible. -/
theorem standardFormUniversalArrowMap_isIrreducible (x₀ : Fin S.n)
    {W Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : W ⟶ Z) :
    IsIrreducibleMorphism (S.standardFormUniversalArrowMap x₀ a) :=
  S.standardFormArrowMap_isIrreducible a.1

/-- Reassembling the initial lifted representatives recovers the chosen
downstairs right almost-split sink exactly. -/
theorem standardFormUniversalRealizedSink_arrowMap (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀) :
    S.standardFormUniversalRealizedSink x₀
        (S.standardFormUniversalArrowMap x₀) W =
      S.standardFormRightSink W.1 := by
  classical
  apply (cancel_epi
    (FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1).inv).1
  apply biproduct.hom_ext'
  intro i
  change FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData W.1 i ≫
        S.standardFormUniversalRealizedSink x₀
          (S.standardFormUniversalArrowMap x₀) W =
    FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData W.1 i ≫ S.standardFormRightSink W.1
  rw [S.rightMiddleInclusion_standardFormUniversalRealizedSink]
  change S.standardFormArrowMap
      (S.standardFormMiddleIndexEquiv W.1 i).2 =
    FiniteTauMatrix.rightMiddleComponent S.finiteTauCategoryData W.1 i
  exact S.standardFormArrowMap_middleIndex W.1 i

/-- Occurrence component of a replacement right sink at one universal-cover
vertex. -/
def standardFormUniversalSinkArrowMap (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (g : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
      S.fgObj W.1)
    {Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : W ⟶ Z) :
    S.standardFormUniversalObj x₀ Z ⟶
      S.standardFormUniversalObj x₀ W :=
  S.standardFormSinkArrowMap g a.1

/-- On an explicitly indexed lifted arrow, sink-component extraction is
literally precomposition with the corresponding middle inclusion. -/
theorem standardFormUniversalSinkArrowMap_middleArrow
    (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (g : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
      S.fgObj W.1)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    S.standardFormUniversalSinkArrowMap x₀ W g
        (S.standardFormUniversalMiddleArrow x₀ W i) =
      FiniteTauMatrix.rightMiddleInclusion
        S.finiteTauCategoryData W.1 i ≫ g := by
  let j := S.standardFormArrowOccurrenceEquiv W.1
    (S.standardFormMiddleIndexEquiv W.1 i).1
    (S.standardFormMiddleIndexEquiv W.1 i).2
  have hj : j = ⟨i, S.standardFormMiddleIndexEquiv_fst W.1 i⟩ :=
    S.standardFormArrowOccurrenceEquiv_middleIndex W.1 i
  change eqToHom (congrArg S.fgObj j.2.symm) ≫
      FiniteTauMatrix.rightMiddleInclusion
        S.finiteTauCategoryData W.1 j.1 ≫ g = _
  rw [hj]
  change 𝟙 (S.fgObj (FiniteTauMatrix.rightMiddleLabel
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i)) ≫
      FiniteTauMatrix.rightMiddleInclusion
        S.finiteTauCategoryData W.1 i ≫ g = _
  simp

/-- Extracting a displayed middle component from the sink reassembled from
`D` returns that arrow representative. -/
@[simp]
theorem standardFormUniversalSinkArrowMap_realizedSink_middleArrow
    (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (i : Fin (FiniteTauMatrix.rightMiddleArity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1)) :
    S.standardFormUniversalSinkArrowMap x₀ W
        (S.standardFormUniversalRealizedSink x₀ D W)
        (S.standardFormUniversalMiddleArrow x₀ W i) =
      D (S.standardFormUniversalMiddleArrow x₀ W i) := by
  let j := S.standardFormArrowOccurrenceEquiv W.1
    (S.standardFormMiddleIndexEquiv W.1 i).1
    (S.standardFormMiddleIndexEquiv W.1 i).2
  have hj : j = ⟨i, S.standardFormMiddleIndexEquiv_fst W.1 i⟩ :=
    S.standardFormArrowOccurrenceEquiv_middleIndex W.1 i
  change eqToHom (congrArg S.fgObj j.2.symm) ≫
      FiniteTauMatrix.rightMiddleInclusion
        S.finiteTauCategoryData W.1 j.1 ≫
        S.standardFormUniversalRealizedSink x₀ D W = _
  rw [hj]
  change 𝟙 (S.fgObj (FiniteTauMatrix.rightMiddleLabel
      S.finiteTauCategoryData.toFiniteRightTauCategoryData W.1 i)) ≫
      FiniteTauMatrix.rightMiddleInclusion
        S.finiteTauCategoryData W.1 i ≫
        S.standardFormUniversalRealizedSink x₀ D W = _
  rw [Category.id_comp]
  exact S.rightMiddleInclusion_standardFormUniversalRealizedSink x₀ D W i

/-- Reassembly followed by component extraction is the identity for every
universal-cover arrow, not only for the explicitly displayed lift. -/
theorem standardFormUniversalSinkArrowMap_realizedSink (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    {W Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : W ⟶ Z) :
    S.standardFormUniversalSinkArrowMap x₀ W
        (S.standardFormUniversalRealizedSink x₀ D W) a = D a := by
  obtain ⟨i, hi⟩ :=
    (S.standardFormUniversalMiddleStarEquiv x₀ W).surjective
      (⟨Z, a⟩ : Quiver.Star W)
  have hstar :
      (⟨S.standardFormUniversalMiddleVertex x₀ W i,
          S.standardFormUniversalMiddleArrow x₀ W i⟩ : Quiver.Star W) =
        ⟨Z, a⟩ :=
    (S.standardFormUniversalMiddleStarEquiv_apply x₀ W i).symm.trans
      hi
  cases hstar
  exact S.standardFormUniversalSinkArrowMap_realizedSink_middleArrow x₀ D W i

/-- Initially, every lifted arrow is the occurrence component of the chosen
downstairs right almost-split sink. -/
theorem standardFormUniversalSinkArrowMap_rightSink (x₀ : Fin S.n)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    {Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : W ⟶ Z) :
    S.standardFormUniversalSinkArrowMap x₀ W
        (S.standardFormRightSink W.1) a =
      S.standardFormUniversalArrowMap x₀ a :=
  S.standardFormSinkArrowMap_rightSink a.1

/-- Replace all arrow representatives whose reversed-quiver source is one
fixed universal-cover vertex. -/
def replaceStandardFormUniversalArrowMapAt (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (g : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
      S.fgObj W.1) :
    S.StandardFormUniversalArrowAssignment x₀ :=
  fun {Y Z} a ↦ by
    classical
    by_cases hYW : Y = W
    · subst Y
      exact S.standardFormUniversalSinkArrowMap x₀ W g a
    · exact D a

@[simp]
theorem replaceStandardFormUniversalArrowMapAt_eq (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (g : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
      S.fgObj W.1)
    {Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (a : W ⟶ Z) :
    S.replaceStandardFormUniversalArrowMapAt x₀ D W g a =
      S.standardFormUniversalSinkArrowMap x₀ W g a := by
  simp [replaceStandardFormUniversalArrowMapAt]

@[simp]
theorem replaceStandardFormUniversalArrowMapAt_eq_of_ne (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (g : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
      S.fgObj W.1)
    {Y Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀} (hYW : Y ≠ W) (a : Y ⟶ Z) :
    S.replaceStandardFormUniversalArrowMapAt x₀ D W g a = D a := by
  simp [replaceStandardFormUniversalArrowMapAt, hYW]

/-- Reassembling at the replaced vertex recovers the replacement sink
exactly. -/
theorem standardFormUniversalRealizedSink_replaceAt_eq (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (g : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
      S.fgObj W.1) :
    S.standardFormUniversalRealizedSink x₀
        (S.replaceStandardFormUniversalArrowMapAt x₀ D W g) W = g := by
  apply (cancel_epi
    (FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1).inv).1
  apply biproduct.hom_ext'
  intro i
  change FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData W.1 i ≫
        S.standardFormUniversalRealizedSink x₀
          (S.replaceStandardFormUniversalArrowMapAt x₀ D W g) W =
    FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData W.1 i ≫ g
  rw [S.rightMiddleInclusion_standardFormUniversalRealizedSink,
    S.replaceStandardFormUniversalArrowMapAt_eq]
  exact S.standardFormUniversalSinkArrowMap_middleArrow x₀ W g i

/-- A replacement at `W` leaves every realized sink at a different source
vertex unchanged. -/
theorem standardFormUniversalRealizedSink_replaceAt_eq_of_ne (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀)
    (W Y : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (g : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
      S.fgObj W.1) (hYW : Y ≠ W) :
    S.standardFormUniversalRealizedSink x₀
        (S.replaceStandardFormUniversalArrowMapAt x₀ D W g) Y =
      S.standardFormUniversalRealizedSink x₀ D Y := by
  unfold standardFormUniversalRealizedSink
  congr 1
  apply congrArg biproduct.desc
  funext i
  exact S.replaceStandardFormUniversalArrowMapAt_eq_of_ne
    x₀ D W g hYW (S.standardFormUniversalMiddleArrow x₀ Y i)

/-- The inductive invariant: every realized sink is minimal right almost
split. -/
structure StandardFormUniversalSinkCondition (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀) : Prop where
  rightAlmostSplit : ∀ W, IsRightAlmostSplit
    (S.standardFormUniversalRealizedSink x₀ D W)
  rightMinimal : ∀ W, IsRightMinimal
    (S.standardFormUniversalRealizedSink x₀ D W)

/-- The initial occurrence-component assignment satisfies the sink
condition. -/
theorem standardFormUniversalArrowMap_sinkCondition (x₀ : Fin S.n) :
    S.StandardFormUniversalSinkCondition x₀
      (S.standardFormUniversalArrowMap x₀) where
  rightAlmostSplit W := by
    rw [S.standardFormUniversalRealizedSink_arrowMap]
    exact S.standardFormRightSink_isRightAlmostSplit W.1
  rightMinimal W := by
    rw [S.standardFormUniversalRealizedSink_arrowMap]
    exact S.standardFormRightSink_isRightMinimal W.1

/-- Replacing one realized sink by another minimal right almost-split sink
preserves the inductive invariant globally. -/
theorem StandardFormUniversalSinkCondition.replaceAt (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D)
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (g : (S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
      S.fgObj W.1)
    (hg : IsRightAlmostSplit g) (hgmin : IsRightMinimal g) :
    S.StandardFormUniversalSinkCondition x₀
      (S.replaceStandardFormUniversalArrowMapAt x₀ D W g) where
  rightAlmostSplit Y := by
    by_cases hYW : Y = W
    · subst Y
      rw [S.standardFormUniversalRealizedSink_replaceAt_eq]
      exact hg
    · rw [S.standardFormUniversalRealizedSink_replaceAt_eq_of_ne
        x₀ D W Y g hYW]
      exact hD.rightAlmostSplit Y
  rightMinimal Y := by
    by_cases hYW : Y = W
    · subst Y
      rw [S.standardFormUniversalRealizedSink_replaceAt_eq]
      exact hgmin
    · rw [S.standardFormUniversalRealizedSink_replaceAt_eq_of_ne
        x₀ D W Y g hYW]
      exact hD.rightMinimal Y

/-- Simultaneously replace the outgoing representatives at every cover
vertex of one Bongartz--Gabriel height.  No enumeration of the (potentially
infinite) height fibre is required because each arrow has a unique source. -/
def replaceStandardFormUniversalArrowMapAtHeight (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀,
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀ W = m →
        ((S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
          S.fgObj W.1)) :
    S.StandardFormUniversalArrowAssignment x₀ :=
  fun {W Z} a ↦ by
    classical
    by_cases hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
        S.standardFormRightMeshData x₀ W = m
    · exact S.standardFormUniversalSinkArrowMap x₀ W (g W hW) a
    · exact D a

@[simp]
theorem replaceStandardFormUniversalArrowMapAtHeight_eq (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀,
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀ W = m →
        ((S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
          S.fgObj W.1))
    {W Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W = m) (a : W ⟶ Z) :
    S.replaceStandardFormUniversalArrowMapAtHeight x₀ D m g a =
      S.standardFormUniversalSinkArrowMap x₀ W (g W hW) a := by
  simp [replaceStandardFormUniversalArrowMapAtHeight, hW]

@[simp]
theorem replaceStandardFormUniversalArrowMapAtHeight_eq_of_ne
    (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀,
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀ W = m →
        ((S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
          S.fgObj W.1))
    {W Z : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀}
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W ≠ m) (a : W ⟶ Z) :
    S.replaceStandardFormUniversalArrowMapAtHeight x₀ D m g a = D a := by
  simp [replaceStandardFormUniversalArrowMapAtHeight, hW]

/-- At a selected height, reassembling the simultaneous replacement returns
the supplied sink at that vertex. -/
theorem standardFormUniversalRealizedSink_replaceAtHeight_eq
    (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀,
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀ W = m →
        ((S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
          S.fgObj W.1))
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W = m) :
    S.standardFormUniversalRealizedSink x₀
        (S.replaceStandardFormUniversalArrowMapAtHeight x₀ D m g) W =
      g W hW := by
  apply (cancel_epi
    (FiniteTauMatrix.rightMiddleDecompositionIso
      S.finiteTauCategoryData W.1).inv).1
  apply biproduct.hom_ext'
  intro i
  change FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData W.1 i ≫
        S.standardFormUniversalRealizedSink x₀
          (S.replaceStandardFormUniversalArrowMapAtHeight x₀ D m g) W =
    FiniteTauMatrix.rightMiddleInclusion
      S.finiteTauCategoryData W.1 i ≫ g W hW
  rw [S.rightMiddleInclusion_standardFormUniversalRealizedSink,
    S.replaceStandardFormUniversalArrowMapAtHeight_eq x₀ D m g hW]
  exact S.standardFormUniversalSinkArrowMap_middleArrow x₀ W (g W hW) i

/-- Outside the selected height, simultaneous replacement leaves the
realized sink unchanged. -/
theorem standardFormUniversalRealizedSink_replaceAtHeight_eq_of_ne
    (x₀ : Fin S.n)
    (D : S.StandardFormUniversalArrowAssignment x₀) (m : ℤ)
    (g : ∀ W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀,
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀ W = m →
        ((S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
          S.fgObj W.1))
    (W : MeshCategory.RightMeshData.UniversalCover.Vertex
      S.standardFormRightMeshData x₀)
    (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
      S.standardFormRightMeshData x₀ W ≠ m) :
    S.standardFormUniversalRealizedSink x₀
        (S.replaceStandardFormUniversalArrowMapAtHeight x₀ D m g) W =
      S.standardFormUniversalRealizedSink x₀ D W := by
  unfold standardFormUniversalRealizedSink
  congr 1
  apply congrArg biproduct.desc
  funext i
  exact S.replaceStandardFormUniversalArrowMapAtHeight_eq_of_ne
    x₀ D m g hW (S.standardFormUniversalMiddleArrow x₀ W i)

/-- A simultaneous height replacement by minimal right almost-split sinks
preserves the global sink condition. -/
theorem StandardFormUniversalSinkCondition.replaceAtHeight
    (x₀ : Fin S.n)
    {D : S.StandardFormUniversalArrowAssignment x₀}
    (hD : S.StandardFormUniversalSinkCondition x₀ D) (m : ℤ)
    (g : ∀ W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀,
      MeshCategory.RightMeshData.UniversalCover.vertexHeight
          S.standardFormRightMeshData x₀ W = m →
        ((S.finiteTauCategoryData.rightMesh (S.fgObj W.1)).X₂ ⟶
          S.fgObj W.1))
    (hg : ∀ (W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀)
      (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
        S.standardFormRightMeshData x₀ W = m),
      IsRightAlmostSplit (g W hW))
    (hgmin : ∀ (W : MeshCategory.RightMeshData.UniversalCover.Vertex
        S.standardFormRightMeshData x₀)
      (hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
        S.standardFormRightMeshData x₀ W = m),
      IsRightMinimal (g W hW)) :
    S.StandardFormUniversalSinkCondition x₀
      (S.replaceStandardFormUniversalArrowMapAtHeight x₀ D m g) where
  rightAlmostSplit W := by
    by_cases hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
        S.standardFormRightMeshData x₀ W = m
    · rw [S.standardFormUniversalRealizedSink_replaceAtHeight_eq
        x₀ D m g W hW]
      exact hg W hW
    · rw [S.standardFormUniversalRealizedSink_replaceAtHeight_eq_of_ne
        x₀ D m g W hW]
      exact hD.rightAlmostSplit W
  rightMinimal W := by
    by_cases hW : MeshCategory.RightMeshData.UniversalCover.vertexHeight
        S.standardFormRightMeshData x₀ W = m
    · rw [S.standardFormUniversalRealizedSink_replaceAtHeight_eq
        x₀ D m g W hW]
      exact hgmin W hW
    · rw [S.standardFormUniversalRealizedSink_replaceAtHeight_eq_of_ne
        x₀ D m g W hW]
      exact hD.rightMinimal W

end UniversalCover

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
