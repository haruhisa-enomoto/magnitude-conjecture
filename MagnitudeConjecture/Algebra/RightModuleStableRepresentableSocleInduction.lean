import MagnitudeConjecture.Algebra.RightModuleStableRepresentableInitialization
import MagnitudeConjecture.Algebra.RightModuleStableRepresentableSuccessor
import MagnitudeConjecture.CategoryTheory.EssentialUniserialExtension

/-!
# Ascending socle induction for stable representables

This file connects the distinguished essential stable socle associated to an
irreducible projective submodule with the abstract uniserial-extension step.
The remaining source-specific task is to identify and control the successive
socles of the displayed cokernels.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] FintypeCat.fintype

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Restricted contravariant Yoneda, with both source and target kept in the
finite module categories used by the stable-representable argument. -/
def finiteRestrictedContravariantRepresentableFunctor :
    RightModule.FinitelyGeneratedCategory A ⥤
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k where
  obj := S.finiteRestrictedContravariantRepresentable
  map := S.finiteRestrictedContravariantRepresentableMap
  map_id := S.finiteRestrictedContravariantRepresentableMap_id
  map_comp := S.finiteRestrictedContravariantRepresentableMap_comp

instance finiteRestrictedContravariantRepresentableFunctor_additive :
    S.finiteRestrictedContravariantRepresentableFunctor.Additive where
  map_add := by
    intro X Y f g
    change S.finiteRestrictedContravariantRepresentableMap (f + g) =
      S.finiteRestrictedContravariantRepresentableMap f +
        S.finiteRestrictedContravariantRepresentableMap g
    exact S.finiteRestrictedContravariantRepresentableMap_add f g

/-- Restricted representables of arbitrary finitely generated modules are
projective: decompose the module into chosen indecomposables and use
additivity of restricted Yoneda. -/
theorem finiteRestrictedContravariantRepresentable_projective
    (C : RightModule.FinitelyGeneratedCategory A) :
    Projective (S.finiteRestrictedContravariantRepresentable C) := by
  letI : Module.Finite k C :=
    RightModule.finite_over_field_of_finitelyGenerated k A C
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) C
  have hdense (j : Fin d.n) :
      ∃ i : S.IndecCategory, Nonempty (d.summand j ≅ S.fgObj i) :=
    S.fgObj_complete (d.summand j) (d.indecomposable j)
  choose i e using hdense
  let eModule : C ≅ ⨁ fun j : Fin d.n ↦ S.fgObj (i j) :=
    d.isoBiproduct ≪≫ biproduct.mapIso (fun j ↦ Classical.choice (e j))
  let F := S.finiteRestrictedContravariantRepresentableFunctor
  let eRepresentable : F.obj C ≅ ⨁ fun j : Fin d.n ↦ F.obj (S.fgObj (i j)) :=
    F.mapIso eModule ≪≫ F.mapBiproduct (fun j : Fin d.n ↦ S.fgObj (i j))
  have hProjective : Projective
      (⨁ fun j : Fin d.n ↦ F.obj (S.fgObj (i j))) := by
    constructor
    intro E X f q hq
    letI : Epi q := hq
    have hfactor (j : Fin d.n) :
        ∃ l : F.obj (S.fgObj (i j)) ⟶ E,
          l ≫ q = biproduct.ι (fun j : Fin d.n ↦
            F.obj (S.fgObj (i j))) j ≫ f := by
      letI : Projective (F.obj (S.fgObj (i j))) := by
        change Projective
          (S.finiteRestrictedContravariantRepresentable (S.fgObj (i j)))
        infer_instance
      exact Projective.factors
          (biproduct.ι (fun j : Fin d.n ↦ F.obj (S.fgObj (i j))) j ≫ f) q
    choose l hl using hfactor
    refine ⟨biproduct.desc l, ?_⟩
    apply biproduct.hom_ext'
    intro j
    rw [biproduct.ι_desc_assoc, hl]
  exact Projective.of_iso eRepresentable.symm hProjective

/-- Restricted Yoneda is full for maps whose source is one chosen
indecomposable, even when the represented target is decomposable. -/
theorem exists_eq_finiteRestrictedContravariantRepresentableMap
    (i : S.IndecCategory) (C : RightModule.FinitelyGeneratedCategory A)
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶
      S.finiteRestrictedContravariantRepresentable C) :
    ∃ h : S.fgObj i ⟶ C,
      S.finiteRestrictedContravariantRepresentableMap h = p := by
  let h : S.fgObj i ⟶ C := ObjectProperty.homMk (by
    change S.inclusion.obj i ⟶ C.obj
    exact p.hom.hom.app (Opposite.op i) (𝟙 (S.inclusion.obj i)))
  refine ⟨h, ?_⟩
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change r ≫ p.hom.hom.app (Opposite.op i)
      (𝟙 (S.inclusion.obj i)) = p.hom.hom.app X r
  let r' : X.unop ⟶ i := InducedCategory.homMk (by exact r)
  exact (ConcreteCategory.congr_hom
    (p.hom.hom.naturality r'.op)
    (𝟙 (S.inclusion.obj i))).symm

/-- Restricted Yoneda detects equality of maps out of a chosen
indecomposable. -/
theorem finiteRestrictedContravariantRepresentableMap_injective_from_fgObj
    (i : S.IndecCategory) (C : RightModule.FinitelyGeneratedCategory A) :
    Function.Injective (fun h : S.fgObj i ⟶ C ↦
      S.finiteRestrictedContravariantRepresentableMap h) := by
  intro f g hfg
  have happ := congrArg
    (fun q ↦ q.hom.hom.app (Opposite.op i)
      (𝟙 (S.inclusion.obj i))) hfg
  change f.hom = g.hom at happ
  apply ObjectProperty.hom_ext
  exact happ

/-- Restricted Yoneda detects equality of maps between arbitrary finitely
generated modules.  Decomposing the source reduces this to detection from
the chosen indecomposable representatives. -/
theorem finiteRestrictedContravariantRepresentableMap_injective
    (B C : RightModule.FinitelyGeneratedCategory A) :
    Function.Injective (fun h : B ⟶ C ↦
      S.finiteRestrictedContravariantRepresentableMap h) := by
  intro f g hfg
  let D := S.chosenLabelDecomposition B
  apply (cancel_epi D.iso.inv).1
  apply biproduct.hom_ext'
  intro j
  apply S.finiteRestrictedContravariantRepresentableMap_injective_from_fgObj
    (D.label j) C
  change
    S.finiteRestrictedContravariantRepresentableMap
        (biproduct.ι (fun i ↦ S.fgObj (D.label i)) j ≫ D.iso.inv ≫ f) =
      S.finiteRestrictedContravariantRepresentableMap
        (biproduct.ι (fun i ↦ S.fgObj (D.label i)) j ≫ D.iso.inv ≫ g)
  have hfg' : S.finiteRestrictedContravariantRepresentableMap f =
      S.finiteRestrictedContravariantRepresentableMap g := hfg
  rw [S.finiteRestrictedContravariantRepresentableMap_comp,
    S.finiteRestrictedContravariantRepresentableMap_comp,
    S.finiteRestrictedContravariantRepresentableMap_comp,
    S.finiteRestrictedContravariantRepresentableMap_comp, hfg']

/-- Restricted Yoneda is full for maps into a chosen indecomposable as well;
the source is first decomposed into chosen indecomposables. -/
theorem exists_eq_finiteRestrictedContravariantRepresentableMap_to_fgObj
    (B : RightModule.FinitelyGeneratedCategory A) (i : S.IndecCategory)
    (p : S.finiteRestrictedContravariantRepresentable B ⟶
      S.finiteRestrictedContravariantRepresentable (S.fgObj i)) :
    ∃ h : B ⟶ S.fgObj i,
      S.finiteRestrictedContravariantRepresentableMap h = p := by
  letI : Module.Finite k B :=
    RightModule.finite_over_field_of_finitelyGenerated k A B
  obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) B
  have hdense (j : Fin d.n) :
      ∃ t : S.IndecCategory, Nonempty (d.summand j ≅ S.fgObj t) :=
    S.fgObj_complete (d.summand j) (d.indecomposable j)
  choose t et using hdense
  let Q := ⨁ fun j : Fin d.n ↦ S.fgObj (t j)
  let eB : B ≅ Q :=
    d.isoBiproduct ≪≫ biproduct.mapIso (fun j ↦ Classical.choice (et j))
  let F := S.finiteRestrictedContravariantRepresentableFunctor
  let pQ : F.obj Q ⟶ F.obj (S.fgObj i) := F.map eB.inv ≫ p
  let a (j : Fin d.n) : F.obj (S.fgObj (t j)) ⟶ F.obj (S.fgObj i) :=
    F.map (biproduct.ι (fun j : Fin d.n ↦ S.fgObj (t j)) j) ≫ pQ
  have ha (j : Fin d.n) :
      ∃ r : S.fgObj (t j) ⟶ S.fgObj i, F.map r = a j := by
    simpa only [F, finiteRestrictedContravariantRepresentableFunctor] using
      S.exists_eq_finiteRestrictedContravariantRepresentableMap
        (t j) (S.fgObj i) (a j)
  choose r hr using ha
  let rQ : Q ⟶ S.fgObj i := biproduct.desc r
  have hrQ : F.map rQ = pQ := by
    let eQ := F.mapBiproduct (fun j : Fin d.n ↦ S.fgObj (t j))
    apply (cancel_epi eQ.inv).1
    rw [biproduct.mapBiproduct_inv_map_desc]
    apply biproduct.hom_ext'
    intro j
    calc
      biproduct.ι (fun j : Fin d.n ↦ F.obj (S.fgObj (t j))) j ≫
            biproduct.desc (fun j : Fin d.n ↦ F.map (r j)) =
          F.map (r j) := biproduct.ι_desc _ _
      _ = a j := hr j
      _ = F.map
            (biproduct.ι (fun j : Fin d.n ↦ S.fgObj (t j)) j) ≫
          pQ := rfl
      _ = biproduct.ι (fun j : Fin d.n ↦
              F.obj (S.fgObj (t j))) j ≫ eQ.inv ≫ pQ := by
            dsimp only [eQ]
            rw [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc]
  let h : B ⟶ S.fgObj i := eB.hom ≫ rQ
  refine ⟨h, ?_⟩
  dsimp only [h]
  rw [S.finiteRestrictedContravariantRepresentableMap_comp]
  rw [show S.finiteRestrictedContravariantRepresentableMap rQ = pQ from hrQ]
  dsimp only [pQ, F, finiteRestrictedContravariantRepresentableFunctor]
  rw [← Category.assoc,
    ← S.finiteRestrictedContravariantRepresentableMap_comp,
    Iso.hom_inv_id,
    S.finiteRestrictedContravariantRepresentableMap_id,
    Category.id_comp]

/-- A split epimorphism from an arbitrary restricted representable onto a
chosen indecomposable representable is induced by a split epimorphism of
modules, with the inducing equation retained. -/
theorem exists_splitEpi_with_map_eq_of_finiteRestrictedContravariantRepresentable_splitEpi
    (B : RightModule.FinitelyGeneratedCategory A) (i : S.IndecCategory)
    (a : S.finiteRestrictedContravariantRepresentable B ⟶
      S.finiteRestrictedContravariantRepresentable (S.fgObj i))
    (ha : IsSplitEpi a) :
    ∃ r : B ⟶ S.fgObj i,
      IsSplitEpi r ∧
        S.finiteRestrictedContravariantRepresentableMap r = a := by
  letI : IsSplitEpi a := ha
  obtain ⟨r, hr⟩ :=
    S.exists_eq_finiteRestrictedContravariantRepresentableMap_to_fgObj B i a
  obtain ⟨s, hs⟩ :=
    S.exists_eq_finiteRestrictedContravariantRepresentableMap
      i B (section_ a)
  have hsr : s ≫ r = 𝟙 (S.fgObj i) := by
    apply S.finiteRestrictedContravariantRepresentableMap_injective_from_fgObj
      i (S.fgObj i)
    change S.finiteRestrictedContravariantRepresentableMap (s ≫ r) =
      S.finiteRestrictedContravariantRepresentableMap (𝟙 (S.fgObj i))
    rw [S.finiteRestrictedContravariantRepresentableMap_comp, hs, hr,
      IsSplitEpi.id,
      S.finiteRestrictedContravariantRepresentableMap_id]
  exact ⟨r, IsSplitEpi.mk' { section_ := s, id := hsr }, hr⟩

/-- A split epimorphism between restricted representables reflects to a split
epimorphism of the representing modules. -/
theorem exists_splitEpi_of_finiteRestrictedContravariantRepresentable_splitEpi
    (B : RightModule.FinitelyGeneratedCategory A) (i : S.IndecCategory)
    (a : S.finiteRestrictedContravariantRepresentable B ⟶
      S.finiteRestrictedContravariantRepresentable (S.fgObj i))
    (ha : IsSplitEpi a) :
    ∃ r : B ⟶ S.fgObj i, IsSplitEpi r := by
  obtain ⟨r, hr, -⟩ :=
    S.exists_splitEpi_with_map_eq_of_finiteRestrictedContravariantRepresentable_splitEpi
      B i a ha
  exact ⟨r, hr⟩

/-- Equality after passing to the restricted projective-stable representable
lifts, at the representable level, to a difference through a chosen
projective epimorphism.  This is the exactness step needed to retain the
actual projective coordinate in the multiplicity-sensitive first-socle
comparison. -/
theorem exists_projectiveFactor_of_finiteRestrictedStableComposites_eq
    {B C : RightModule.FinitelyGeneratedCategory A} (p : Fin S.n)
    (q : S.fgObj p ⟶ C) [Epi q] (hp : Projective (S.fgObj p))
    (f g : B ⟶ C)
    (hfg :
      S.finiteRestrictedContravariantRepresentableMap f ≫
          S.finiteProjectiveStableQuotient C =
        S.finiteRestrictedContravariantRepresentableMap g ≫
          S.finiteProjectiveStableQuotient C) :
    ∃ s : B ⟶ S.fgObj p,
      S.finiteRestrictedContravariantRepresentableMap (s ≫ q) =
        S.finiteRestrictedContravariantRepresentableMap f -
          S.finiteRestrictedContravariantRepresentableMap g := by
  let Q := S.finiteProjectiveStableQuotient C
  let Fq := S.finiteRestrictedContravariantRepresentableMap q
  let x := S.finiteRestrictedContravariantRepresentableMap f -
    S.finiteRestrictedContravariantRepresentableMap g
  have hx : x ≫ Q = 0 := by
    dsimp only [x, Q]
    rw [Preadditive.sub_comp, hfg, sub_self]
  have hpModule : Module.Projective Aᵐᵒᵖ (S.fgObj p) :=
    MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj p) hp
  letI : Module.Projective Aᵐᵒᵖ (S.fgObj p) := hpModule
  have hpObj : Projective (S.fgObj p).obj := inferInstance
  let T := ShortComplex.mk Fq Q
    (S.finiteRestrictedMap_comp_stableQuotient_eq_zero q hpObj)
  have hT : T.Exact :=
    S.finiteRestrictedMap_stableQuotient_exact q hpObj
  let kx : S.finiteRestrictedContravariantRepresentable B ⟶ kernel Q :=
    kernel.lift Q x hx
  let kq : S.finiteRestrictedContravariantRepresentable (S.fgObj p) ⟶ kernel Q :=
    kernel.lift Q Fq T.zero
  letI : Epi kq := (T.exact_iff_epi_kernel_lift).1 hT
  letI : Projective (S.finiteRestrictedContravariantRepresentable B) :=
    S.finiteRestrictedContravariantRepresentable_projective B
  obtain ⟨a, ha⟩ := Projective.factors kx kq
  obtain ⟨s, hs⟩ :=
    S.exists_eq_finiteRestrictedContravariantRepresentableMap_to_fgObj
      B p a
  refine ⟨s, ?_⟩
  rw [S.finiteRestrictedContravariantRepresentableMap_comp, hs]
  change a ≫ Fq = x
  calc
    a ≫ Fq = a ≫ (kq ≫ kernel.ι Q) := by
      rw [show kq ≫ kernel.ι Q = Fq from kernel.lift_ι Q Fq T.zero]
    _ = (a ≫ kq) ≫ kernel.ι Q := (Category.assoc _ _ _).symm
    _ = kx ≫ kernel.ι Q := congrArg (fun z ↦ z ≫ kernel.ι Q) ha
    _ = x := kernel.lift_ι Q x hx

/-- A chosen indecomposable split quotient of a minimal right almost-split
middle contributes a positive incoming-arrow multiplicity. -/
theorem arrowMultiplicity_pos_of_splitEpi_minimalRightAlmostSplitMiddle
    (i c : S.IndecCategory) (hi : ¬ Projective (S.fgObj i))
    (r : (S.minimalRightAlmostSplitAt i).middle ⟶ S.fgObj c)
    (hr : IsSplitEpi r) :
    0 < FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData c i := by
  letI : IsSplitEpi r := hr
  let D := splitMonoComplement (section_ r)
  let eSplit : (S.minimalRightAlmostSplitAt i).middle ≅
      S.fgObj c ⊞ D.complement :=
    D.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hpositive : 0 < S.indecomposableMultiplicity c
      (S.minimalRightAlmostSplitAt i).middle := by
    rw [S.indecomposableMultiplicity_iso_invariant c eSplit,
      S.indecomposableMultiplicity_biprod,
      S.indecomposableMultiplicity_fgObj]
    simp
  rw [← S.indecomposableMultiplicity_meshRightMiddle c i,
    S.meshRightAlmostSplitAt_eq_of_not_projective i hi]
  exact hpositive

/-- Projecting the Auslander--Reiten kernel inclusion to an indecomposable
split quotient of the middle term gives the corresponding translated
irreducible arm. -/
theorem rightKernelMap_comp_splitEpi_isIrreducible
    (i c : S.IndecCategory) (hi : ¬ Projective (S.fgObj i))
    (r : (S.minimalRightAlmostSplitAt i).middle ⟶ S.fgObj c)
    (hr : IsSplitEpi r) :
    IsIrreducibleMorphism
      (S.rightKernelMap ⟨i, hi⟩ ≫ r) := by
  letI : IsSplitEpi r := hr
  exact
    (S.rightKernelMap_leftAlmostSplit ⟨i, hi⟩).comp_irreducible_of_splitSummand
      (S.rightKernelMap ⟨i, hi⟩)
      (S.rightKernelMap_leftMinimal ⟨i, hi⟩)
      r (section_ r) (IsSplitEpi.id r)
      (S.fgObj_indecomposable (S.rightTranslationLabel ⟨i, hi⟩))
      (S.fgObj_indecomposable c)

/-- For a fixed simple cover, two split quotient coordinates from the same
minimal right almost-split middle induce scalar-proportional maps.  Indeed,
after subtracting the scalar detected on one chosen section, an independent
split quotient would exhibit two copies of the same indecomposable in the
middle.  Representation-finite square-freeness rules this out. -/
theorem minimalRightAlmostSplit_splitEpi_simpleCover_proportional
    (i c : S.IndecCategory) (hi : ¬ Projective (S.fgObj i))
    {L : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    [Simple L]
    (pL : S.finiteRestrictedContravariantRepresentable (S.fgObj c) ⟶ L)
    (hpL : pL ≠ 0)
    (r r' : (S.minimalRightAlmostSplitAt i).middle ⟶ S.fgObj c)
    (hr : IsSplitEpi r) (hr' : IsSplitEpi r') :
    ∃ a : k,
      S.finiteRestrictedContravariantRepresentableMap r' ≫ pL =
        a • (S.finiteRestrictedContravariantRepresentableMap r ≫ pL) := by
  letI : IsSplitEpi r := hr
  letI : IsSplitEpi r' := hr'
  let s : S.fgObj c ⟶ (S.minimalRightAlmostSplitAt i).middle := section_ r
  let e : S.fgObj c ⟶ S.fgObj c := s ≫ r'
  obtain ⟨a, ha⟩ :=
    S.almostSplitSkeleton.exists_scalar_sub_isRadicalMorphism (K := k) c e
  let d : (S.minimalRightAlmostSplitAt i).middle ⟶ S.fgObj c :=
    r' - a • r
  have hsd : s ≫ d = e - a • 𝟙 (S.fgObj c) := by
    dsimp only [s, d, e]
    rw [Preadditive.comp_sub, Linear.comp_smul, IsSplitEpi.id]
  have hsdRadical : CategoricalRadical.IsRadicalMorphism (s ≫ d) := by
    rw [hsd]
    exact ha
  have hdNotSplit : ¬ IsSplitEpi d := by
    intro hd
    letI : IsSplitEpi d := hd
    let t : S.fgObj c ⟶ (S.minimalRightAlmostSplitAt i).middle := section_ d
    let v : S.fgObj c ⟶ S.fgObj c :=
      𝟙 (S.fgObj c) - (t ≫ r) ≫ (s ≫ d)
    have hsdNotSplit : ¬ IsSplitEpi (s ≫ d) :=
      (S.almostSplitSkeleton.isRadicalMorphism_iff_not_isSplitEpi_to_obj
        (s ≫ d)).1 hsdRadical
    have hprodNotUnit : ¬ IsUnit
        (End.of ((t ≫ r) ≫ (s ≫ d)) : End (S.fgObj c)) := by
      intro hunit
      haveI : IsIso ((t ≫ r) ≫ (s ≫ d)) :=
        (isUnit_iff_isIso ((t ≫ r) ≫ (s ≫ d))).1 hunit
      haveI : IsSplitEpi (s ≫ d) := by
        apply IsSplitEpi.mk'
        refine
          { section_ := inv ((t ≫ r) ≫ (s ≫ d)) ≫ (t ≫ r)
            id := ?_ }
        rw [Category.assoc, IsIso.inv_hom_id]
      exact hsdNotSplit inferInstance
    letI : IsLocalRing (End (S.fgObj c)) := S.fgObj_end_isLocalRing c
    have hvIso : IsIso v := by
      have hunit : IsUnit (End.of v : End (S.fgObj c)) := by
        rw [show (End.of v : End (S.fgObj c)) =
          1 - End.of ((t ≫ r) ≫ (s ≫ d)) by rfl]
        exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add
          (show IsUnit
            ((End.of ((t ≫ r) ≫ (s ≫ d)) : End (S.fgObj c)) +
              (1 - End.of ((t ≫ r) ≫ (s ≫ d)))) by
            rw [add_sub_cancel]
            exact isUnit_one)).resolve_left hprodNotUnit
      exact (isUnit_iff_isIso v).1 hunit
    let d' : (S.minimalRightAlmostSplitAt i).middle ⟶ S.fgObj c :=
      d - r ≫ (s ≫ d)
    have hsd' : s ≫ d' = 0 := by
      dsimp only [d', s]
      rw [Preadditive.comp_sub, ← Category.assoc, IsSplitEpi.id,
        Category.id_comp, sub_self]
    have htd' : t ≫ d' = v := by
      dsimp only [d', v]
      rw [Preadditive.comp_sub, IsSplitEpi.id]
      simp only [Category.assoc]
    let t₀ : S.fgObj c ⟶ (S.minimalRightAlmostSplitAt i).middle :=
      inv v ≫ t
    have ht₀d' : t₀ ≫ d' = 𝟙 (S.fgObj c) := by
      dsimp only [t₀]
      rw [Category.assoc, htd', IsIso.inv_hom_id]
    let t₁ : S.fgObj c ⟶ (S.minimalRightAlmostSplitAt i).middle :=
      t₀ - (t₀ ≫ r) ≫ s
    have ht₁r : t₁ ≫ r = 0 := by
      have hsecond : ((t₀ ≫ r) ≫ s) ≫ r = t₀ ≫ r := by
        rw [Category.assoc, IsSplitEpi.id, Category.comp_id]
      dsimp only [t₁]
      rw [Preadditive.sub_comp, hsecond, sub_self]
    have ht₁d' : t₁ ≫ d' = 𝟙 (S.fgObj c) := by
      have hsecond : ((t₀ ≫ r) ≫ s) ≫ d' = 0 := by
        rw [Category.assoc, hsd', comp_zero]
      dsimp only [t₁]
      rw [Preadditive.sub_comp, hsecond, sub_zero, ht₀d']
    let j : S.fgObj c ⊞ S.fgObj c ⟶
        (S.minimalRightAlmostSplitAt i).middle := biprod.desc s t₁
    let q : (S.minimalRightAlmostSplitAt i).middle ⟶
        S.fgObj c ⊞ S.fgObj c := biprod.lift r d'
    have hjq : j ≫ q = 𝟙 (S.fgObj c ⊞ S.fgObj c) := by
      apply biprod.hom_ext'
      · simp only [j, q, biprod.inl_desc_assoc]
        apply biprod.hom_ext
        · rw [Category.assoc, biprod.lift_fst, IsSplitEpi.id]
          simp
        · rw [Category.assoc, biprod.lift_snd, hsd']
          simp
      · simp only [j, q, biprod.inr_desc_assoc]
        apply biprod.hom_ext
        · rw [Category.assoc, biprod.lift_fst, ht₁r]
          simp
        · rw [Category.assoc, biprod.lift_snd, ht₁d']
          simp
    letI : IsSplitMono j := IsSplitMono.mk' { retraction := q, id := hjq }
    let D := splitMonoComplement j
    let eSplit : (S.minimalRightAlmostSplitAt i).middle ≅
        (S.fgObj c ⊞ S.fgObj c) ⊞ D.complement :=
      D.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
        (BinaryBiproduct.isLimit _ _)
    have htwo : 2 ≤ S.indecomposableMultiplicity c
        (S.minimalRightAlmostSplitAt i).middle := by
      rw [S.indecomposableMultiplicity_iso_invariant c eSplit,
        S.indecomposableMultiplicity_biprod,
        S.indecomposableMultiplicity_biprod,
        S.indecomposableMultiplicity_fgObj]
      simp
    have hone : S.indecomposableMultiplicity c
        (S.minimalRightAlmostSplitAt i).middle ≤ 1 := by
      rw [← S.meshRightAlmostSplitAt_eq_of_not_projective i hi,
        S.indecomposableMultiplicity_meshRightMiddle]
      exact S.arrowMultiplicity_le_one c i
    omega
  refine ⟨a, ?_⟩
  have hkill :
      S.finiteRestrictedContravariantRepresentableMap d ≫ pL = 0 :=
    S.finiteRestrictedContravariantRepresentableMap_comp_nonzero_to_simple_eq_zero
      c d hdNotSplit pL hpL
  dsimp only [d] at hkill
  have hmapSmul :
      S.finiteRestrictedContravariantRepresentableMap (a • r) =
        a • S.finiteRestrictedContravariantRepresentableMap r := by
    apply ObjectProperty.hom_ext
    exact (CoveringHom.restrictedLinearYonedaFunctor
      (k := k) S.inclusion).map_smul a r.hom
  rw [sub_eq_add_neg,
    S.finiteRestrictedContravariantRepresentableMap_add,
    S.finiteRestrictedContravariantRepresentableMap_neg,
    hmapSmul, Preadditive.add_comp, Preadditive.neg_comp,
    Linear.smul_comp] at hkill
  rw [← sub_eq_add_neg] at hkill
  exact sub_eq_zero.mp hkill

/-- If two maps out of one indecomposable restricted representable have
scalar-proportional restrictions along the minimal right almost-split map,
then they become scalar-proportional after quotienting by an essential simple
subobject. -/
theorem minimalRightAlmostSplit_quotientMaps_proportional_of_boundary
    (i : S.IndecCategory)
    {L G : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    [Simple L] (l : L ⟶ G) [Mono l] (hl : IsEssentialMono l)
    (H H' : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G)
    (a a' : S.finiteRestrictedContravariantRepresentable
        (S.minimalRightAlmostSplitAt i).middle ⟶ L)
    (ha : a ≫ l =
      S.finiteRestrictedContravariantRepresentableMap
        (S.minimalRightAlmostSplitAt i).map ≫ H)
    (ha' : a' ≫ l =
      S.finiteRestrictedContravariantRepresentableMap
        (S.minimalRightAlmostSplitAt i).map ≫ H')
    (α : k) (hprop : a' = α • a) :
    H' ≫ cokernel.π l = (α • H) ≫ cokernel.π l := by
  let r := S.finiteRestrictedContravariantRepresentableRadicalInclusion i
  let b : (S.minimalRightAlmostSplitAt i).middle ⟶ S.fgObj i :=
    (S.minimalRightAlmostSplitAt i).map
  let d := H' - α • H
  change a ≫ l =
    S.finiteRestrictedContravariantRepresentableMap b ≫ H at ha
  change a' ≫ l =
    S.finiteRestrictedContravariantRepresentableMap b ≫ H' at ha'
  have hbd : S.finiteRestrictedContravariantRepresentableMap b ≫ d = 0 := by
    dsimp only [d]
    rw [Preadditive.comp_sub, Linear.comp_smul, ← ha', ← ha, hprop,
      Linear.smul_comp, sub_self]
  have himage :=
    S.imageSubobject_radicalInclusion_comp_eq_rightAlmostSplit_comp
      i b (S.minimalRightAlmostSplitAt i).rightAlmostSplit d
  have hrd : r ≫ d = 0 := by
    have himageBot : imageSubobject (r ≫ d) = ⊥ := by
      rw [himage, hbd, imageSubobject_zero]
    have harrow : (imageSubobject (r ≫ d)).arrow = 0 := by
      rw [himageBot, Subobject.bot_arrow]
    rw [← imageSubobject_arrow_comp (r ≫ d), harrow, comp_zero]
  let w : cokernel r ⟶ G := cokernel.desc r d hrd
  have hw : cokernel.π r ≫ w = d := cokernel.π_desc r d hrd
  haveI : Simple (cokernel r) :=
    MagnitudeConjecture.CategoryTheory.simple_cokernel_of_mono_rightAlmostSplit_projective
      r
      (S.finiteRestrictedContravariantRepresentableRadicalInclusion_isRightAlmostSplit i)
  have hwzero : w ≫ cokernel.π l = 0 :=
    MagnitudeConjecture.simple_comp_cokernel_π_eq_zero_of_isEssentialMono
      l hl w
  rw [← sub_eq_zero]
  rw [← Preadditive.sub_comp]
  change d ≫ cokernel.π l = 0
  rw [← hw, Category.assoc, hwzero, comp_zero]

/-- A nonzero stable map cannot be generated by a projective module. -/
theorem not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0) :
    ¬ Projective (S.fgObj i) := by
  intro hi
  have hiModule : Module.Projective Aᵐᵒᵖ (S.fgObj i) :=
    MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj i) hi
  letI : Module.Projective Aᵐᵒᵖ (S.fgObj i) := hiModule
  have hiObj : Projective (S.fgObj i).obj := inferInstance
  exact hstable
    (S.finiteRestrictedMap_comp_stableQuotient_eq_zero h hiObj)

/-- Every map from a chosen indecomposable restricted representable to a
stable representable is induced by an actual module morphism. -/
theorem exists_eq_finiteRestrictedToProjectiveStableMap
    (i : S.IndecCategory) (C : RightModule.FinitelyGeneratedCategory A)
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶
      S.finiteProjectiveStableContravariantRepresentable C) :
    ∃ h : S.fgObj i ⟶ C,
      S.finiteRestrictedToProjectiveStableMap i h = p := by
  let q := S.finiteProjectiveStableQuotient C
  let a : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶
      S.finiteRestrictedContravariantRepresentable C :=
    Projective.factorThru p q
  have haq : a ≫ q = p := Projective.factorThru_comp p q
  let h : S.fgObj i ⟶ C := ObjectProperty.homMk (by
    change S.inclusion.obj i ⟶ C.obj
    exact a.hom.hom.app (Opposite.op i) (𝟙 (S.inclusion.obj i)))
  have hmap : S.finiteRestrictedContravariantRepresentableMap h = a := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r ≫ a.hom.hom.app (Opposite.op i)
        (𝟙 (S.inclusion.obj i)) = a.hom.hom.app X r
    let r' : X.unop ⟶ i := InducedCategory.homMk (by exact r)
    have hnaturality := ConcreteCategory.congr_hom
      (a.hom.hom.naturality r'.op) (𝟙 (S.inclusion.obj i))
    exact hnaturality.symm
  refine ⟨h, ?_⟩
  dsimp only [finiteRestrictedToProjectiveStableMap]
  rw [hmap]
  exact haq

/-- Every chosen simple subobject of a nonzero cokernel lifts from one
indecomposable restricted representable.  This projective lifting statement
does not require the subobject being quotiented out to be simple or
essential. -/
theorem exists_restrictedRepresentable_lift_of_nonzero_cokernel
    {H G : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (m : H ⟶ G) [Mono m] (hquotient : ¬ IsZero (cokernel m)) :
    ∃ (T : CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k)
      (t : T ⟶ cokernel m) (i : S.IndecCategory)
      (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
      (h : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G),
      Simple T ∧ Mono t ∧ p ≠ 0 ∧ h ≠ 0 ∧
        h ≫ cokernel.π m = p ≫ t := by
  obtain ⟨T, t, hT, ht⟩ :=
    CoveringHom.finiteDimensionalModule_exists_simple_subobject
      (cokernel m) hquotient
  letI : Simple T := hT
  letI : Mono t := ht
  obtain ⟨i, p, hp⟩ :=
    S.finiteDimensionalModule_exists_nonzero_restrictedRepresentableMap
      (Simple.not_isZero T)
  letI : Epi p := epi_of_nonzero_to_simple hp
  let h : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G :=
    Projective.factorThru (p ≫ t) (cokernel.π m)
  have hh : h ≫ cokernel.π m = p ≫ t :=
    Projective.factorThru_comp (p ≫ t) (cokernel.π m)
  have hpt : p ≫ t ≠ 0 := by
    intro hzero
    apply hp
    apply (cancel_mono t).1
    simpa only [zero_comp] using hzero
  have hhnonzero : h ≠ 0 := by
    intro hzero
    apply hpt
    rw [← hh, hzero, zero_comp]
  exact ⟨T, t, i, p, h, hT, ht, hp, hhnonzero, hh⟩

/-- A representable lift which is nonzero modulo a waist subobject contains
that subobject. -/
theorem restrictedRepresentableLift_contains_of_waist
    {H G T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (m : H ⟶ G) [Mono m]
    (hm : IsUniserialObject.IsWaistSubobject (Subobject.mk m))
    (t : T ⟶ cokernel m) [Mono t]
    (i : S.IndecCategory)
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hp : p ≠ 0)
    (h : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G)
    (hcomp : h ≫ cokernel.π m = p ≫ t) :
    Subobject.mk m ≤ imageSubobject h := by
  apply (hm (imageSubobject h)).resolve_right
  intro himageLe
  have himageLe' : Subobject.mk (imageSubobject h).arrow ≤
      Subobject.mk m := by
    simpa only [(imageSubobject h).mk_arrow] using himageLe
  let a : (imageSubobject h :
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) ⟶ H :=
    Subobject.ofMkLEMk (imageSubobject h).arrow m himageLe'
  have ha : a ≫ m = (imageSubobject h).arrow :=
    Subobject.ofMkLEMk_comp himageLe'
  have hzero : h ≫ cokernel.π m = 0 := by
    calc
      h ≫ cokernel.π m =
          (factorThruImageSubobject h ≫ (imageSubobject h).arrow) ≫
            cokernel.π m := by rw [imageSubobject_arrow_comp]
      _ = factorThruImageSubobject h ≫
          ((a ≫ m) ≫ cokernel.π m) := by rw [ha, Category.assoc]
      _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero,
        comp_zero]
  apply hp
  apply (cancel_mono t).1
  rw [← hcomp, hzero, zero_comp]

/-- Above a simple essential layer, every chosen simple subobject of the
cokernel lifts from a single indecomposable representable.  Essentiality
forces the lifted cyclic image to contain the preceding layer. -/
theorem exists_restrictedRepresentable_lift_of_nonzero_essentialSimpleCokernel
    {L G : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    [Simple L] (l : L ⟶ G) [Mono l] (hl : IsEssentialMono l)
    (hquotient : ¬ IsZero (cokernel l)) :
    ∃ (T : CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k)
      (t : T ⟶ cokernel l) (i : S.IndecCategory)
      (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
      (h : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G),
      Simple T ∧ Mono t ∧ p ≠ 0 ∧ h ≠ 0 ∧
        h ≫ cokernel.π l = p ≫ t ∧
        Subobject.mk l ≤ imageSubobject h := by
  obtain ⟨T, t, i, p, h, hT, ht, hp, hhnonzero, hh⟩ :=
    S.exists_restrictedRepresentable_lift_of_nonzero_cokernel l hquotient
  letI : Simple T := hT
  letI : Mono t := ht
  have himage : imageSubobject h ≠ ⊥ := by
    intro himage
    apply hhnonzero
    have harrow : (imageSubobject h).arrow = 0 := by
      rw [← Subobject.mk_eq_bot_iff_zero]
      simpa only [Subobject.mk_arrow] using himage
    rw [← imageSubobject_arrow_comp h, harrow, comp_zero]
  exact ⟨T, t, i, p, h, hT, ht, hp, hhnonzero, hh,
    IsUniserialObject.simple_le_nonzero_subobject_of_essential
      l hl (imageSubobject h) himage⟩

/-- The lifted cyclic image is the next one-step extension of the preceding
essential layer: its quotient by that layer is the chosen simple subobject of
the ambient cokernel. -/
theorem restrictedRepresentableLift_cokernel_simple
    {L G T : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (l : L ⟶ G) [Mono l]
    [Simple T] (t : T ⟶ cokernel l) [Mono t]
    (i : S.IndecCategory)
    (p : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ T)
    (hp : p ≠ 0)
    (h : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G)
    (hcomp : h ≫ cokernel.π l = p ≫ t)
    (hle : Subobject.mk l ≤ imageSubobject h) :
    ∃ lH : L ⟶ S.finiteRepresentableImage i h,
      Mono lH ∧
        lH ≫ S.finiteRepresentableImageInclusion i h = l ∧
        Simple (cokernel lH) := by
  letI : Epi p := epi_of_nonzero_to_simple hp
  let m := S.finiteRepresentableImageInclusion i h
  have hle' : Subobject.mk l ≤ Subobject.mk m := by
    have hm : Subobject.mk m = imageSubobject h := by
      dsimp only [m, finiteRepresentableImageInclusion]
      exact (imageSubobject h).mk_arrow
    rw [hm]
    exact hle
  let lH : L ⟶ S.finiteRepresentableImage i h :=
    Subobject.ofMkLEMk l m hle'
  have hlH : lH ≫ m = l := Subobject.ofMkLEMk_comp hle'
  letI : Mono lH := inferInstance
  have sq : IsPullback lH (𝟙 L) m l :=
    IsPullback.of_vert_isIso_mono ⟨by
      simpa only [hlH, Category.id_comp]⟩
  let b : cokernel lH ⟶ cokernel l :=
    cokernel.map lH l (𝟙 L) m sq.w
  letI : Mono b := Abelian.mono_cokernel_map_of_isPullback sq
  have hb : cokernel.π lH ≫ b = m ≫ cokernel.π l :=
    cokernel.π_desc _ _ _
  let r := S.finiteRepresentableImagePresentation i h
  have hrm : r ≫ m = h :=
    S.finiteRepresentableImagePresentation_comp_inclusion i h
  have hwhole : (r ≫ cokernel.π lH) ≫ b = p ≫ t := by
    calc
      (r ≫ cokernel.π lH) ≫ b = r ≫ m ≫ cokernel.π l := by
        rw [Category.assoc, hb]
      _ = h ≫ cokernel.π l := by rw [← Category.assoc, hrm]
      _ = p ≫ t := hcomp
  have himage : imageSubobject b = imageSubobject t := by
    calc
      imageSubobject b = imageSubobject ((r ≫ cokernel.π lH) ≫ b) :=
        (imageSubobject_comp_eq_of_epi (r ≫ cokernel.π lH) b).symm
      _ = imageSubobject (p ≫ t) := by rw [hwhole]
      _ = imageSubobject t := imageSubobject_comp_eq_of_epi p t
  let eb : (imageSubobject b :
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) ≅ cokernel lH :=
    imageSubobjectIso b ≪≫ imageMonoIsoSource b
  let et : (imageSubobject t :
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) ≅ T :=
    imageSubobjectIso t ≪≫ imageMonoIsoSource t
  let eImage : (imageSubobject b :
      CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) ≅
      (imageSubobject t :
        CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k) :=
    eqToIso (congrArg
      (fun Q : Subobject (cokernel l) ↦
        (Q : CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k)) himage)
  exact ⟨lH, inferInstance, hlH,
    Simple.of_iso (eb.symm ≪≫ eImage ≪≫ et)⟩

/-- In a nonzero cyclic stable image, any simple essential layer with simple
quotient is exactly the pushed-forward representable radical. -/
theorem finiteProjectiveStableImageRadical_eq_of_essentialSimpleCokernel
    {L : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    [Simple L]
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (l : L ⟶ S.finiteProjectiveStableImage i h) [Mono l]
    (hl : IsEssentialMono l) [Simple (cokernel l)] :
    imageSubobject
        (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
          S.finiteProjectiveStableImagePresentation i h) =
      Subobject.mk l := by
  let R := imageSubobject
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
      S.finiteProjectiveStableImagePresentation i h)
  have hRradical : IsUniserialObject.IsRadicalSubobject R :=
    S.finiteProjectiveStableImageRadical_isRadicalSubobject i h
  have hRproper : R ≠ ⊤ :=
    S.finiteProjectiveStableImageRadical_ne_top i h hstable
  have hlradical : IsUniserialObject.IsRadicalSubobject (Subobject.mk l) :=
    IsUniserialObject.isRadicalSubobject_of_essential_simple_cokernel l hl
  have hlproper : Subobject.mk l ≠ ⊤ := by
    intro htop
    letI : IsIso l := (Subobject.isIso_iff_mk_eq_top l).2 htop
    have hzero : IsZero (cokernel l) :=
      IsZero.of_epi_eq_zero (cokernel.π l) (cokernel.π_of_epi l)
    exact Simple.not_isZero (cokernel l) hzero
  exact le_antisymm
    (hlradical R hRproper)
    (hRradical (Subobject.mk l) hlproper)

/-- In a uniserial cyclic stable image, any subobject with simple cokernel is
the pushed-forward representable radical. -/
theorem finiteProjectiveStableImageRadical_eq_of_uniserialSimpleCokernel
    {L : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (hH : IsUniserialObject (S.finiteProjectiveStableImage i h))
    (l : L ⟶ S.finiteProjectiveStableImage i h) [hlmono : Mono l]
    [hlsimple : Simple (cokernel l)] :
    imageSubobject
        (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
          S.finiteProjectiveStableImagePresentation i h) =
      Subobject.mk l := by
  let R := imageSubobject
    (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
      S.finiteProjectiveStableImagePresentation i h)
  have hRradical : IsUniserialObject.IsRadicalSubobject R :=
    S.finiteProjectiveStableImageRadical_isRadicalSubobject i h
  have hRproper : R ≠ ⊤ :=
    S.finiteProjectiveStableImageRadical_ne_top i h hstable
  have hlradical : IsUniserialObject.IsRadicalSubobject (Subobject.mk l) :=
    IsUniserialObject.isRadicalSubobject_of_uniserial_simple_cokernel hH l
  have hlproper : Subobject.mk l ≠ ⊤ := by
    intro htop
    letI : IsIso l := (Subobject.isIso_iff_mk_eq_top l).2 htop
    have hzero : IsZero (cokernel l) :=
      IsZero.of_epi_eq_zero (cokernel.π l) (cokernel.π_of_epi l)
    exact Simple.not_isZero (cokernel l) hzero
  exact le_antisymm
    (hlradical R hRproper)
    (hRradical (Subobject.mk l) hlproper)

/-- The projective cover of the preceding simple layer splits from the
restricted representable of the right almost-split middle at the next cyclic
generator.  This is the projective-cover comparison underlying the special
case of Auslander--Reiten Proposition 2.6 used in the socle induction. -/
theorem finiteProjectiveStableImage_projectiveCover_split_from_rightAlmostSplitMiddle
    {L : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    [Simple L]
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (l : L ⟶ S.finiteProjectiveStableImage i h) [Mono l]
    (hl : IsEssentialMono l) [Simple (cokernel l)]
    (P : MinimalProjectivePresentation L)
    {B : RightModule.FinitelyGeneratedCategory A}
    (b : B ⟶ S.fgObj i) (hb : IsRightAlmostSplit b) :
    ∃ a : S.finiteRestrictedContravariantRepresentable B ⟶ P.p,
      IsSplitEpi a ∧
        a ≫ P.f ≫ l =
          S.finiteRestrictedContravariantRepresentableMap b ≫
            S.finiteProjectiveStableImagePresentation i h := by
  let m := S.finiteRestrictedContravariantRepresentableMap b ≫
    S.finiteProjectiveStableImagePresentation i h
  have hrad :=
    S.finiteProjectiveStableImageRadical_eq_of_essentialSimpleCokernel
      i h hstable l hl
  have has :=
    S.imageSubobject_radicalInclusion_comp_eq_rightAlmostSplit_comp
      i b hb (S.finiteProjectiveStableImagePresentation i h)
  have himage : imageSubobject m = Subobject.mk l := by
    exact has.symm.trans hrad
  let e :
      (imageSubobject m : CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) ≅ L :=
    eqToIso (congrArg
      (fun Q : Subobject (S.finiteProjectiveStableImage i h) ↦
        (Q : CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k)) himage) ≪≫
      Subobject.underlyingIso l
  let q : S.finiteRestrictedContravariantRepresentable B ⟶ L :=
    factorThruImageSubobject m ≫ e.hom
  letI : Projective (S.finiteRestrictedContravariantRepresentable B) :=
    S.finiteRestrictedContravariantRepresentable_projective B
  obtain ⟨a, ha, hacomp⟩ := P.exists_splitEpi_factor q
  refine ⟨a, ha, ?_⟩
  rw [← Category.assoc, hacomp]
  change q ≫ l = m
  dsimp only [q]
  rw [Category.assoc]
  have he : e.hom ≫ l = (imageSubobject m).arrow := by
    simpa only [e, Iso.trans_hom, eqToIso.hom, Category.assoc,
      Subobject.underlyingIso_hom_comp_eq_mk] using
        Subobject.arrow_congr (imageSubobject m) (Subobject.mk l) himage
  rw [he, imageSubobject_arrow_comp]

/-- The projective-cover comparison does not require the preceding layer to
be simple: it is enough that the candidate cyclic image is uniserial and the
preceding layer has simple quotient. -/
theorem finiteProjectiveStableImage_projectiveCover_split_from_rightAlmostSplitMiddle_of_uniserial
    {L : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    {C : RightModule.FinitelyGeneratedCategory A}
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (hH : IsUniserialObject (S.finiteProjectiveStableImage i h))
    (l : L ⟶ S.finiteProjectiveStableImage i h) [Mono l]
    [Simple (cokernel l)]
    (P : MinimalProjectivePresentation L)
    {B : RightModule.FinitelyGeneratedCategory A}
    (b : B ⟶ S.fgObj i) (hb : IsRightAlmostSplit b) :
    ∃ a : S.finiteRestrictedContravariantRepresentable B ⟶ P.p,
      IsSplitEpi a ∧
        a ≫ P.f ≫ l =
          S.finiteRestrictedContravariantRepresentableMap b ≫
            S.finiteProjectiveStableImagePresentation i h := by
  let m := S.finiteRestrictedContravariantRepresentableMap b ≫
    S.finiteProjectiveStableImagePresentation i h
  have hrad :=
    S.finiteProjectiveStableImageRadical_eq_of_uniserialSimpleCokernel
      i h hstable hH l
  have has :=
    S.imageSubobject_radicalInclusion_comp_eq_rightAlmostSplit_comp
      i b hb (S.finiteProjectiveStableImagePresentation i h)
  have himage : imageSubobject m = Subobject.mk l := by
    exact has.symm.trans hrad
  let e :
      (imageSubobject m : CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) ≅ L :=
    eqToIso (congrArg
      (fun Q : Subobject (S.finiteProjectiveStableImage i h) ↦
        (Q : CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k)) himage) ≪≫
      Subobject.underlyingIso l
  let q : S.finiteRestrictedContravariantRepresentable B ⟶ L :=
    factorThruImageSubobject m ≫ e.hom
  letI : Projective (S.finiteRestrictedContravariantRepresentable B) :=
    S.finiteRestrictedContravariantRepresentable_projective B
  obtain ⟨a, ha, hacomp⟩ := P.exists_splitEpi_factor q
  refine ⟨a, ha, ?_⟩
  rw [← Category.assoc, hacomp]
  change q ≫ l = m
  dsimp only [q]
  rw [Category.assoc]
  have he : e.hom ≫ l = (imageSubobject m).arrow := by
    simpa only [e, Iso.trans_hom, eqToIso.hom, Category.assoc,
      Subobject.underlyingIso_hom_comp_eq_mk] using
        Subobject.arrow_congr (imageSubobject m) (Subobject.mk l) himage
  rw [he, imageSubobject_arrow_comp]

/-- At an arbitrary uniserial cyclic stage, the module generating the
preceding layer splits from the minimal right almost-split middle of a
one-step cyclic extension. -/
theorem finiteProjectiveStableImage_moduleCover_split_from_rightAlmostSplitMiddle_of_uniserial
    {C : RightModule.FinitelyGeneratedCategory A}
    (j : S.IndecCategory) (g : S.fgObj j ⟶ C)
    (gstable : S.finiteRestrictedToProjectiveStableMap j g ≠ 0)
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (lH : S.finiteProjectiveStableImage j g ⟶
      S.finiteProjectiveStableImage i h)
    [Mono lH]
    (hH : IsUniserialObject (S.finiteProjectiveStableImage i h))
    [Simple (cokernel lH)] :
    ∃ r : (S.minimalRightAlmostSplitAt i).middle ⟶ S.fgObj j,
      IsSplitEpi r ∧
        IsIrreducibleMorphism
          (S.rightKernelMap
              ⟨i,
                S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
                  i h hstable⟩ ≫ r) ∧
        S.finiteRestrictedContravariantRepresentableMap r ≫
              S.finiteProjectiveStableImagePresentation j g ≫ lH =
          S.finiteRestrictedContravariantRepresentableMap
              (S.minimalRightAlmostSplitAt i).map ≫
            S.finiteProjectiveStableImagePresentation i h := by
  let P := S.finiteProjectiveStableImageMinimalProjectivePresentation j g gstable
  obtain ⟨a, ha, hcompat⟩ :=
    S.finiteProjectiveStableImage_projectiveCover_split_from_rightAlmostSplitMiddle_of_uniserial
      i h hstable hH lH P
      (S.minimalRightAlmostSplitAt i).map
      (S.minimalRightAlmostSplitAt i).rightAlmostSplit
  obtain ⟨r, hr, hrmap⟩ :=
    S.exists_splitEpi_with_map_eq_of_finiteRestrictedContravariantRepresentable_splitEpi
      (S.minimalRightAlmostSplitAt i).middle j a ha
  refine ⟨r, hr,
    S.rightKernelMap_comp_splitEpi_isIrreducible i j
      (S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
        i h hstable) r hr, ?_⟩
  rw [hrmap]
  exact hcompat

set_option backward.isDefEq.respectTransparency.types false in
/-- Above a cyclic predecessor with nonzero radical, two one-step uniserial
extensions have the same generator label.  Their translated kernel arms are
both irreducible incoming arms killed by the predecessor generator, whose
source is unique under the two-arm bound. -/
theorem finiteProjectiveStableImage_nextExtension_label_eq_of_nonzeroRadical
    (harity : ∀ (z : S.IndecCategory),
      ¬ Projective (S.fgObj z) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData z ≤ 2)
    {C : RightModule.FinitelyGeneratedCategory A}
    (j : S.IndecCategory) (g : S.fgObj j ⟶ C)
    (gstable : S.finiteRestrictedToProjectiveStableMap j g ≠ 0)
    (hRzero : ¬ IsZero
      ((imageSubobject
          (S.finiteRestrictedContravariantRepresentableRadicalInclusion j ≫
            S.finiteProjectiveStableImagePresentation j g) :
        CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k)))
    (i i' : S.IndecCategory) (h : S.fgObj i ⟶ C) (h' : S.fgObj i' ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (hstable' : S.finiteRestrictedToProjectiveStableMap i' h' ≠ 0)
    (lH : S.finiteProjectiveStableImage j g ⟶
      S.finiteProjectiveStableImage i h)
    (lH' : S.finiteProjectiveStableImage j g ⟶
      S.finiteProjectiveStableImage i' h')
    [Mono lH] [Simple (cokernel lH)]
    [Mono lH'] [Simple (cokernel lH')]
    (hH : IsUniserialObject (S.finiteProjectiveStableImage i h))
    (hH' : IsUniserialObject (S.finiteProjectiveStableImage i' h'))
    (hlHcomp : lH ≫ S.finiteProjectiveStableImageInclusion i h =
      S.finiteProjectiveStableImageInclusion j g)
    (hlHcomp' : lH' ≫ S.finiteProjectiveStableImageInclusion i' h' =
      S.finiteProjectiveStableImageInclusion j g) :
    i' = i := by
  let hi :=
    S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
      i h hstable
  let hi' :=
    S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
      i' h' hstable'
  let κ := S.rightKernelMap ⟨i, hi⟩
  let κ' := S.rightKernelMap ⟨i', hi'⟩
  obtain ⟨r, hr, hirred, hboundary⟩ :=
    S.finiteProjectiveStableImage_moduleCover_split_from_rightAlmostSplitMiddle_of_uniserial
      j g gstable i h hstable lH hH
  obtain ⟨r', hr', hirred', hboundary'⟩ :=
    S.finiteProjectiveStableImage_moduleCover_split_from_rightAlmostSplitMiddle_of_uniserial
      j g gstable i' h' hstable' lH' hH'
  have hambient :
      S.finiteRestrictedContravariantRepresentableMap r ≫
          S.finiteRestrictedToProjectiveStableMap j g =
        S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫
          S.finiteRestrictedToProjectiveStableMap i h := by
    have hcompat := congrArg
      (fun z ↦ z ≫ S.finiteProjectiveStableImageInclusion i h) hboundary
    simp only [Category.assoc] at hcompat
    rw [hlHcomp] at hcompat
    rw [S.finiteProjectiveStableImagePresentation_comp_inclusion] at hcompat
    exact hcompat.trans (congrArg
      (fun z ↦ S.finiteRestrictedContravariantRepresentableMap
        (S.minimalRightAlmostSplitAt i).map ≫ z)
      (S.finiteProjectiveStableImagePresentation_comp_inclusion i h))
  have hambient' :
      S.finiteRestrictedContravariantRepresentableMap r' ≫
          S.finiteRestrictedToProjectiveStableMap j g =
        S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i').map ≫
          S.finiteRestrictedToProjectiveStableMap i' h' := by
    have hcompat := congrArg
      (fun z ↦ z ≫ S.finiteProjectiveStableImageInclusion i' h') hboundary'
    simp only [Category.assoc] at hcompat
    rw [hlHcomp'] at hcompat
    rw [S.finiteProjectiveStableImagePresentation_comp_inclusion] at hcompat
    exact hcompat.trans (congrArg
      (fun z ↦ S.finiteRestrictedContravariantRepresentableMap
        (S.minimalRightAlmostSplitAt i').map ≫ z)
      (S.finiteProjectiveStableImagePresentation_comp_inclusion i' h'))
  have hκB : κ ≫ (S.minimalRightAlmostSplitAt i).map = 0 := by
    dsimp only [κ, rightKernelMap]
    simp only [Category.assoc, kernel.condition, comp_zero]
  have hκB' : κ' ≫ (S.minimalRightAlmostSplitAt i').map = 0 := by
    dsimp only [κ', rightKernelMap]
    simp only [Category.assoc, kernel.condition, comp_zero]
  have hkill :
      S.finiteRestrictedContravariantRepresentableMap (κ ≫ r) ≫
        S.finiteRestrictedToProjectiveStableMap j g = 0 := by
    rw [S.finiteRestrictedContravariantRepresentableMap_comp,
      Category.assoc, hambient]
    rw [← Category.assoc,
      ← S.finiteRestrictedContravariantRepresentableMap_comp, hκB,
      S.finiteRestrictedContravariantRepresentableMap_zero, zero_comp]
  have hkill' :
      S.finiteRestrictedContravariantRepresentableMap (κ' ≫ r') ≫
        S.finiteRestrictedToProjectiveStableMap j g = 0 := by
    rw [S.finiteRestrictedContravariantRepresentableMap_comp,
      Category.assoc, hambient']
    rw [← Category.assoc,
      ← S.finiteRestrictedContravariantRepresentableMap_comp, hκB',
      S.finiteRestrictedContravariantRepresentableMap_zero, zero_comp]
  have htranslationLabel :
      S.rightTranslationLabel ⟨i', hi'⟩ =
        S.rightTranslationLabel ⟨i, hi⟩ :=
    S.killedIrreducible_source_eq_of_nonzero_stableImageRadical
      harity j g gstable hRzero
      (S.rightTranslationLabel ⟨i, hi⟩) (κ ≫ r) hirred hkill
      (S.rightTranslationLabel ⟨i', hi'⟩) (κ' ≫ r') hirred' hkill'
  have htranslation : S.rightTranslation ⟨i', hi'⟩ =
      S.rightTranslation ⟨i, hi⟩ := Subtype.ext htranslationLabel
  have hsource : (⟨i', hi'⟩ :
      {z : S.IndecCategory // ¬ Projective (S.fgObj z)}) =
      ⟨i, hi⟩ := S.rightTranslation_injective htranslation
  exact congrArg Subtype.val hsource
set_option backward.isDefEq.respectTransparency.types false in
/-- At an arbitrary noninitial cyclic stage, scalar proportionality on the
simple top of the predecessor descends through the two-step quotient.  The
essentiality of that simple top in the ambient quotient is the induction
invariant supplied by the preceding successor step. -/
theorem finiteProjectiveStableImage_nextExtension_quotientMaps_proportional
    {C : RightModule.FinitelyGeneratedCategory A}
    (j : S.IndecCategory) (g : S.fgObj j ⟶ C)
    (gstable : S.finiteRestrictedToProjectiveStableMap j g ≠ 0)
    {R : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (s : R ⟶ S.finiteProjectiveStableImage j g) [Mono s]
    [Simple (cokernel s)]
    (i : S.IndecCategory) (h h' : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (hstable' : S.finiteRestrictedToProjectiveStableMap i h' ≠ 0)
    (lH : S.finiteProjectiveStableImage j g ⟶
      S.finiteProjectiveStableImage i h)
    (lH' : S.finiteProjectiveStableImage j g ⟶
      S.finiteProjectiveStableImage i h')
    [Mono lH] [Simple (cokernel lH)]
    [Mono lH'] [Simple (cokernel lH')]
    (hH : IsUniserialObject (S.finiteProjectiveStableImage i h))
    (hH' : IsUniserialObject (S.finiteProjectiveStableImage i h'))
    (hlHcomp : lH ≫ S.finiteProjectiveStableImageInclusion i h =
      S.finiteProjectiveStableImageInclusion j g)
    (hlHcomp' : lH' ≫ S.finiteProjectiveStableImageInclusion i h' =
      S.finiteProjectiveStableImageInclusion j g)
    (htopEssential : IsEssentialMono
      (cokernelInclusionOfComp s
        (S.finiteProjectiveStableImageInclusion j g))) :
    ∃ α : k,
      S.finiteRestrictedToProjectiveStableMap i h' ≫
          cokernel.π (S.finiteProjectiveStableImageInclusion j g) =
        (α • S.finiteRestrictedToProjectiveStableMap i h) ≫
          cokernel.π (S.finiteProjectiveStableImageInclusion j g) := by
  let m := S.finiteProjectiveStableImageInclusion j g
  let n := s ≫ m
  let t := cokernelInclusionOfComp s m
  let H := S.finiteRestrictedToProjectiveStableMap i h
  let H' := S.finiteRestrictedToProjectiveStableMap i h'
  let aPres := S.finiteProjectiveStableImagePresentation j g
  let pTop := aPres ≫ cokernel.π s
  let hi := S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
    i h hstable
  have hpTop : pTop ≠ 0 := by
    intro hpzero
    haveI : Epi pTop := by
      dsimp only [pTop, aPres]
      infer_instance
    exact Simple.not_isZero (cokernel s)
      (IsZero.of_epi_eq_zero pTop hpzero)
  obtain ⟨r, hr, -, hboundary⟩ :=
    S.finiteProjectiveStableImage_moduleCover_split_from_rightAlmostSplitMiddle_of_uniserial
      j g gstable i h hstable lH hH
  obtain ⟨r', hr', -, hboundary'⟩ :=
    S.finiteProjectiveStableImage_moduleCover_split_from_rightAlmostSplitMiddle_of_uniserial
      j g gstable i h' hstable' lH' hH'
  obtain ⟨α, hprop⟩ :=
    S.minimalRightAlmostSplit_splitEpi_simpleCover_proportional
      i j hi pTop hpTop r r' hr hr'
  let a := S.finiteRestrictedContravariantRepresentableMap r ≫ aPres
  let a' := S.finiteRestrictedContravariantRepresentableMap r' ≫ aPres
  have hpropTop : a' ≫ cokernel.π s =
      α • (a ≫ cokernel.π s) := by
    simpa only [a, a', pTop, aPres, Category.assoc] using hprop
  have hboundaryAmbient : a ≫ m =
      S.finiteRestrictedContravariantRepresentableMap
          (S.minimalRightAlmostSplitAt i).map ≫ H := by
    have hcompat := congrArg
      (fun z ↦ z ≫ S.finiteProjectiveStableImageInclusion i h) hboundary
    simp only [Category.assoc] at hcompat
    rw [hlHcomp] at hcompat
    calc
      a ≫ m =
          (S.finiteRestrictedContravariantRepresentableMap r ≫ aPres) ≫ m := rfl
      _ = S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫
          (S.finiteProjectiveStableImagePresentation i h ≫
            S.finiteProjectiveStableImageInclusion i h) := by
        simpa only [aPres, Category.assoc] using hcompat
      _ = _ := congrArg
        (fun z ↦ S.finiteRestrictedContravariantRepresentableMap
          (S.minimalRightAlmostSplitAt i).map ≫ z)
        (S.finiteProjectiveStableImagePresentation_comp_inclusion i h)
  have hboundaryAmbient' : a' ≫ m =
      S.finiteRestrictedContravariantRepresentableMap
          (S.minimalRightAlmostSplitAt i).map ≫ H' := by
    have hcompat := congrArg
      (fun z ↦ z ≫ S.finiteProjectiveStableImageInclusion i h') hboundary'
    simp only [Category.assoc] at hcompat
    rw [hlHcomp'] at hcompat
    calc
      a' ≫ m =
          (S.finiteRestrictedContravariantRepresentableMap r' ≫ aPres) ≫ m := rfl
      _ = S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫
          (S.finiteProjectiveStableImagePresentation i h' ≫
            S.finiteProjectiveStableImageInclusion i h') := by
        simpa only [aPres, Category.assoc] using hcompat
      _ = _ := congrArg
        (fun z ↦ S.finiteRestrictedContravariantRepresentableMap
          (S.minimalRightAlmostSplitAt i).map ≫ z)
        (S.finiteProjectiveStableImagePresentation_comp_inclusion i h')
  have hboundaryQuotient :
      (a ≫ cokernel.π s) ≫ t =
        S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫
          (H ≫ cokernel.π n) := by
    calc
      (a ≫ cokernel.π s) ≫ t =
          a ≫ (cokernel.π s ≫ t) := Category.assoc _ _ _
      _ = a ≫ (m ≫ cokernel.π n) := by
        rw [cokernel_π_comp_cokernelInclusionOfComp]
      _ = (a ≫ m) ≫ cokernel.π n := (Category.assoc _ _ _).symm
      _ = (S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫ H) ≫
          cokernel.π n := by rw [hboundaryAmbient]
      _ = _ := Category.assoc _ _ _
  have hboundaryQuotient' :
      (a' ≫ cokernel.π s) ≫ t =
        S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫
          (H' ≫ cokernel.π n) := by
    calc
      (a' ≫ cokernel.π s) ≫ t =
          a' ≫ (cokernel.π s ≫ t) := Category.assoc _ _ _
      _ = a' ≫ (m ≫ cokernel.π n) := by
        rw [cokernel_π_comp_cokernelInclusionOfComp]
      _ = (a' ≫ m) ≫ cokernel.π n := (Category.assoc _ _ _).symm
      _ = (S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫ H') ≫
          cokernel.π n := by rw [hboundaryAmbient']
      _ = _ := Category.assoc _ _ _
  have hiter :=
    S.minimalRightAlmostSplit_quotientMaps_proportional_of_boundary
      i t htopEssential
      (H ≫ cokernel.π n) (H' ≫ cokernel.π n)
      (a ≫ cokernel.π s) (a' ≫ cokernel.π s)
      hboundaryQuotient hboundaryQuotient' α hpropTop
  refine ⟨α, ?_⟩
  apply comp_cokernel_π_eq_of_comp_cokernelTower_eq s m H' (α • H)
  simpa only [n, t, H, H', Linear.smul_comp] using hiter


/-- A nonterminal cyclic waist layer admits a larger cyclic layer with simple
quotient.  The waist property supplies the containment which, at later stages,
cannot be obtained from essentiality alone. -/
theorem exists_nextCyclicWaistExtension_of_nonzero_cokernel
    {H G : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (m : H ⟶ G) [Mono m]
    (hmEssential : IsEssentialMono m)
    (hmWaist : IsUniserialObject.IsWaistSubobject (Subobject.mk m))
    (hH : IsUniserialObject H)
    (hquotient : ¬ IsZero (cokernel m)) :
    ∃ (i : S.IndecCategory)
      (h : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G)
      (mK : H ⟶ S.finiteRepresentableImage i h),
      h ≠ 0 ∧ Mono mK ∧
        mK ≫ S.finiteRepresentableImageInclusion i h = m ∧
        Simple (cokernel mK) ∧
        IsUniserialObject (S.finiteRepresentableImage i h) ∧
        IsEssentialMono (S.finiteRepresentableImageInclusion i h) := by
  obtain ⟨T, t, i, p, h, hT, ht, hp, hh, hcomp⟩ :=
    S.exists_restrictedRepresentable_lift_of_nonzero_cokernel m hquotient
  letI : Simple T := hT
  letI : Mono t := ht
  have hle : Subobject.mk m ≤ imageSubobject h :=
    S.restrictedRepresentableLift_contains_of_waist
      m hmWaist t i p hp h hcomp
  obtain ⟨mK, hmKmono, hmKcomp, hmKsimple⟩ :=
    S.restrictedRepresentableLift_cokernel_simple
      m t i p hp h hcomp hle
  letI : Mono mK := hmKmono
  let n := S.finiteRepresentableImageInclusion i h
  have hmKWaist : IsUniserialObject.IsWaistSubobject
      (Subobject.mk mK) := by
    apply IsUniserialObject.isWaistSubobject_restrict mK n
    simpa only [n, hmKcomp] using hmWaist
  letI : Simple (cokernel mK) := hmKsimple
  have hKUniserial : IsUniserialObject (S.finiteRepresentableImage i h) :=
    IsUniserialObject.of_waist_simple_cokernel hH mK hmKWaist
  have hnEssential : IsEssentialMono n := by
    constructor
    · infer_instance
    · intro Z q hnq
      apply hmEssential.2 q
      rw [← hmKcomp, Category.assoc]
      infer_instance
  exact ⟨i, h, mK, hh, hmKmono, hmKcomp, hmKsimple,
    hKUniserial, hnEssential⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- At an arbitrary noninitial cyclic stage, a chosen one-step extension gives
an essential simple top in the quotient by its predecessor. -/
theorem finiteProjectiveStableImage_nextExtension_cokernelMap_essential
    (harity : ∀ (z : S.IndecCategory),
      ¬ Projective (S.fgObj z) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData z ≤ 2)
    {C : RightModule.FinitelyGeneratedCategory A}
    (j : S.IndecCategory) (g : S.fgObj j ⟶ C)
    (gstable : S.finiteRestrictedToProjectiveStableMap j g ≠ 0)
    (hRzero : ¬ IsZero
      ((imageSubobject
          (S.finiteRestrictedContravariantRepresentableRadicalInclusion j ≫
            S.finiteProjectiveStableImagePresentation j g) :
        CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k)))
    {R : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (s : R ⟶ S.finiteProjectiveStableImage j g) [Mono s]
    [Simple (cokernel s)]
    (hJ : IsUniserialObject (S.finiteProjectiveStableImage j g))
    (hjWaist : IsUniserialObject.IsWaistSubobject
      (Subobject.mk (S.finiteProjectiveStableImageInclusion j g)))
    (htopEssential : IsEssentialMono
      (cokernelInclusionOfComp s
        (S.finiteProjectiveStableImageInclusion j g)))
    (i : S.IndecCategory) (h : S.fgObj i ⟶ C)
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (lH : S.finiteProjectiveStableImage j g ⟶
      S.finiteProjectiveStableImage i h)
    [hlHmono : Mono lH] [hlHsimple : Simple (cokernel lH)]
    (hH : IsUniserialObject (S.finiteProjectiveStableImage i h))
    (hlHcomp : lH ≫ S.finiteProjectiveStableImageInclusion i h =
      S.finiteProjectiveStableImageInclusion j g) :
    ∃ t₀ : cokernel lH ⟶
        cokernel (S.finiteProjectiveStableImageInclusion j g),
      Mono t₀ ∧ IsEssentialMono t₀ ∧
        cokernel.π lH ≫ t₀ =
          S.finiteProjectiveStableImageInclusion i h ≫
            cokernel.π (S.finiteProjectiveStableImageInclusion j g) ∧
        IsEssentialMono
          (cokernelInclusionOfComp lH
            (S.finiteProjectiveStableImageInclusion i h)) := by
  let m := S.finiteProjectiveStableImageInclusion j g
  let n := S.finiteProjectiveStableImageInclusion i h
  let H := S.finiteRestrictedToProjectiveStableMap i h
  have sq : IsPullback lH (𝟙 (S.finiteProjectiveStableImage j g)) n m :=
    IsPullback.of_vert_isIso_mono ⟨by
      simpa only [hlHcomp, Category.id_comp]⟩
  let t₀ : cokernel lH ⟶ cokernel m :=
    cokernel.map lH m (𝟙 (S.finiteProjectiveStableImage j g)) n sq.w
  letI : Mono t₀ := Abelian.mono_cokernel_map_of_isPullback sq
  have ht₀ : cokernel.π lH ≫ t₀ = n ≫ cokernel.π m :=
    cokernel.π_desc _ _ _
  have ht₀essential : IsEssentialMono t₀ := by
    apply S.finiteDimensionalModule_isEssentialMono_of_simple_restrictedRepresentable_factors
      t₀
    intro T hT t ht i' p' hp'
    letI : Simple T := hT
    letI : Mono t := ht
    let HNat' : S.finiteRestrictedContravariantRepresentable (S.fgObj i') ⟶
        S.finiteProjectiveStableContravariantRepresentable C :=
      Projective.factorThru (p' ≫ t) (cokernel.π m)
    have hHNat'comp : HNat' ≫ cokernel.π m = p' ≫ t :=
      Projective.factorThru_comp (p' ≫ t) (cokernel.π m)
    have hp't : p' ≫ t ≠ 0 := by
      intro hzero
      apply hp'
      apply (cancel_mono t).1
      simpa only [zero_comp] using hzero
    have hHNat' : HNat' ≠ 0 := by
      intro hzero
      apply hp't
      rw [← hHNat'comp, hzero, zero_comp]
    have hle : Subobject.mk m ≤ imageSubobject HNat' :=
      S.restrictedRepresentableLift_contains_of_waist
        m hjWaist t i' p' hp' HNat' hHNat'comp
    obtain ⟨h', hh'⟩ :=
      S.exists_eq_finiteRestrictedToProjectiveStableMap i' C HNat'
    have hstable' : S.finiteRestrictedToProjectiveStableMap i' h' ≠ 0 := by
      rw [hh']
      exact hHNat'
    have hstableComp' :
        S.finiteRestrictedToProjectiveStableMap i' h' ≫ cokernel.π m =
          p' ≫ t := by
      rw [hh']
      exact hHNat'comp
    have hstableLe' : Subobject.mk m ≤ imageSubobject
        (S.finiteRestrictedToProjectiveStableMap i' h') := by
      rw [hh']
      exact hle
    obtain ⟨lH', hlH'mono, hlH'comp, hlH'simple⟩ :=
      S.restrictedRepresentableLift_cokernel_simple
        m t i' p' hp' (S.finiteRestrictedToProjectiveStableMap i' h')
          hstableComp' hstableLe'
    let lHstable : S.finiteProjectiveStableImage j g ⟶
        S.finiteProjectiveStableImage i' h' := lH'
    have hlHstableMono : Mono lHstable := by
      dsimp only [lHstable]
      exact hlH'mono
    letI : Mono lHstable := hlHstableMono
    have hlHstableSimple : Simple (cokernel lHstable) := by
      dsimp only [lHstable]
      exact hlH'simple
    letI : Simple (cokernel lHstable) := hlHstableSimple
    have hlHstableComp :
        lHstable ≫ S.finiteProjectiveStableImageInclusion i' h' = m := by
      dsimp only [lHstable]
      exact hlH'comp
    have hlHstableWaist : IsUniserialObject.IsWaistSubobject
        (Subobject.mk lHstable) := by
      apply IsUniserialObject.isWaistSubobject_restrict lHstable
        (S.finiteProjectiveStableImageInclusion i' h')
      simpa only [hlHstableComp] using hjWaist
    have hH' : IsUniserialObject (S.finiteProjectiveStableImage i' h') :=
      IsUniserialObject.of_waist_simple_cokernel
        hJ lHstable hlHstableWaist
    have hii : i' = i :=
      S.finiteProjectiveStableImage_nextExtension_label_eq_of_nonzeroRadical
        harity j g gstable hRzero i i' h h' hstable hstable'
        lH lHstable hH hH' hlHcomp hlHstableComp
    subst i'
    letI : Mono lHstable := hlHstableMono
    letI : Simple (cokernel lHstable) := hlHstableSimple
    obtain ⟨α, hproportional⟩ :=
      S.finiteProjectiveStableImage_nextExtension_quotientMaps_proportional
        j g gstable s i h h' hstable hstable' lH lHstable hH hH'
        hlHcomp hlHstableComp htopEssential
    let p₀ := S.finiteProjectiveStableImagePresentation i h ≫ cokernel.π lH
    have hfixed : H ≫ cokernel.π m = p₀ ≫ t₀ := by
      calc
        H ≫ cokernel.π m =
            (S.finiteProjectiveStableImagePresentation i h ≫ n) ≫
              cokernel.π m := by
          rw [S.finiteProjectiveStableImagePresentation_comp_inclusion]
        _ = S.finiteProjectiveStableImagePresentation i h ≫
              (n ≫ cokernel.π m) := Category.assoc _ _ _
        _ = S.finiteProjectiveStableImagePresentation i h ≫
              (cokernel.π lH ≫ t₀) := by rw [ht₀]
        _ = p₀ ≫ t₀ := (Category.assoc _ _ _).symm
    refine ⟨α • p₀, ?_⟩
    calc
      (α • p₀) ≫ t₀ = α • (p₀ ≫ t₀) := by rw [Linear.smul_comp]
      _ = α • (H ≫ cokernel.π m) := by rw [hfixed]
      _ = (α • H) ≫ cokernel.π m := by rw [Linear.smul_comp]
      _ = S.finiteRestrictedToProjectiveStableMap i h' ≫
          cokernel.π m := hproportional.symm
      _ = p' ≫ t := hstableComp'
  let tCanonical := cokernelInclusionOfComp lH n
  let e := eqToIso (congrArg
    (fun q : _ ⟶ _ ↦ cokernel q) hlHcomp)
  have ht₀eq : tCanonical ≫ e.hom = t₀ := by
    apply (cancel_epi (cokernel.π lH)).1
    calc
      cokernel.π lH ≫ (tCanonical ≫ e.hom) =
          (n ≫ cokernel.π (lH ≫ n)) ≫ e.hom := by
        rw [← Category.assoc]
        dsimp only [tCanonical]
        rw [cokernel_π_comp_cokernelInclusionOfComp]
      _ = n ≫ cokernel.π m := by
        dsimp only [e]
        rw [Category.assoc, cokernel_π_comp_eqToIso_of_eq hlHcomp]
      _ = cokernel.π lH ≫ t₀ := ht₀.symm
  have htCanonicalEssential : IsEssentialMono tCanonical := by
    apply IsUniserialObject.isEssentialMono_of_comp_iso tCanonical e
    rw [ht₀eq]
    exact ht₀essential
  exact ⟨t₀, inferInstance, ht₀essential, ht₀, htCanonicalEssential⟩


set_option backward.isDefEq.respectTransparency.types true in
/-- Finite ascending-socle induction from a noninitial cyclic waist stage.
The two-arm bound makes every successive simple top essential, so the waist
strictly grows until it is the whole stable representable. -/
theorem finiteProjectiveStableRepresentable_isUniserial_of_cyclicWaistStage
    (harity : ∀ (z : S.IndecCategory),
      ¬ Projective (S.fgObj z) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData z ≤ 2)
    {C : RightModule.FinitelyGeneratedCategory A}
    (j : S.IndecCategory) (g : S.fgObj j ⟶ C)
    (gstable : S.finiteRestrictedToProjectiveStableMap j g ≠ 0)
    (hRzero : ¬ IsZero
      ((imageSubobject
          (S.finiteRestrictedContravariantRepresentableRadicalInclusion j ≫
            S.finiteProjectiveStableImagePresentation j g) :
        CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k)))
    {R : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    (s : R ⟶ S.finiteProjectiveStableImage j g) [Mono s]
    [Simple (cokernel s)]
    (hJ : IsUniserialObject (S.finiteProjectiveStableImage j g))
    (hmEssential : IsEssentialMono
      (S.finiteProjectiveStableImageInclusion j g))
    (hmWaist : IsUniserialObject.IsWaistSubobject
      (Subobject.mk (S.finiteProjectiveStableImageInclusion j g)))
    (htopEssential : IsEssentialMono
      (cokernelInclusionOfComp s
        (S.finiteProjectiveStableImageInclusion j g))) :
    IsUniserialObject
      (S.finiteProjectiveStableContravariantRepresentable C) := by
  let main : ∀ d : ℕ,
      ∀ {D : RightModule.FinitelyGeneratedCategory A}
        (j' : S.IndecCategory) (g' : S.fgObj j' ⟶ D)
        {R' : CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k}
        (s' : R' ⟶ S.finiteProjectiveStableImage j' g')
        (hs'mono : Mono s') (hs'simple : Simple (cokernel s')),
        S.finiteRestrictedToProjectiveStableMap j' g' ≠ 0 →
        (¬ IsZero
          ((imageSubobject
              (S.finiteRestrictedContravariantRepresentableRadicalInclusion j' ≫
                S.finiteProjectiveStableImagePresentation j' g') :
            CoveringHom.FiniteDimensionalModuleCategory
              (C := S.IndecCategoryᵒᵖ) k))) →
        IsUniserialObject (S.finiteProjectiveStableImage j' g') →
        IsEssentialMono (S.finiteProjectiveStableImageInclusion j' g') →
        IsUniserialObject.IsWaistSubobject
          (Subobject.mk (S.finiteProjectiveStableImageInclusion j' g')) →
        IsEssentialMono
          (cokernelInclusionOfComp s'
            (S.finiteProjectiveStableImageInclusion j' g')) →
        CoveringHom.moduleTotalDimension
          (cokernel (S.finiteProjectiveStableImageInclusion j' g')) = d →
        IsUniserialObject
          (S.finiteProjectiveStableContravariantRepresentable D) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro D j' g' R' s' hs'mono hs'simple hg' hrad' hJ'
          hmEssential' hmWaist' htopEssential' hdim
        letI : Mono s' := hs'mono
        letI : Simple (cokernel s') := hs'simple
        by_cases hzero : IsZero
            (cokernel (S.finiteProjectiveStableImageInclusion j' g'))
        · have hπ : cokernel.π
              (S.finiteProjectiveStableImageInclusion j' g') = 0 :=
            hzero.eq_of_tgt _ _
          letI : Epi (S.finiteProjectiveStableImageInclusion j' g') :=
            Abelian.epi_of_cokernel_π_eq_zero _ hπ
          letI : IsIso (S.finiteProjectiveStableImageInclusion j' g') :=
            isIso_of_mono_of_epi _
          exact hJ'.congr
            (asIso (S.finiteProjectiveStableImageInclusion j' g'))
        · obtain ⟨i, hNat, lH, hhNat, hlHmono, hlHcomp, hlHsimple,
              hH, hnEssential⟩ :=
            S.exists_nextCyclicWaistExtension_of_nonzero_cokernel
              (S.finiteProjectiveStableImageInclusion j' g')
              hmEssential' hmWaist' hJ' hzero
          obtain ⟨h', hh'⟩ :=
            S.exists_eq_finiteRestrictedToProjectiveStableMap i D hNat
          subst hNat
          let lHstable : S.finiteProjectiveStableImage j' g' ⟶
              S.finiteProjectiveStableImage i h' := lH
          have hlHstableMono : Mono lHstable := by
            dsimp only [lHstable]
            exact hlHmono
          have hlHstableSimple : Simple (cokernel lHstable) := by
            dsimp only [lHstable]
            exact hlHsimple
          have hlHstableComp :
              lHstable ≫ S.finiteProjectiveStableImageInclusion i h' =
                S.finiteProjectiveStableImageInclusion j' g' := by
            dsimp only [lHstable]
            exact hlHcomp
          have hHstable :
              IsUniserialObject (S.finiteProjectiveStableImage i h') := by
            exact hH
          have hnStableEssential : IsEssentialMono
              (S.finiteProjectiveStableImageInclusion i h') := by
            exact hnEssential
          letI hlHmonoInstance : Mono lHstable := hlHstableMono
          letI hlHsimpleInstance : Simple (cokernel lHstable) :=
            hlHstableSimple
          obtain ⟨tTop, htTopMono, htTopEssential, htTop,
              hcanonicalTopEssential⟩ :=
            S.finiteProjectiveStableImage_nextExtension_cokernelMap_essential
              harity j' g' hg' hrad' s' hJ' hmWaist' htopEssential'
              i h' hhNat lHstable (hlHmono := hlHstableMono)
              (hlHsimple := hlHstableSimple) hHstable hlHstableComp
          letI htTopMonoInstance : Mono tTop := htTopEssential.1
          letI hnMono : Mono
              (S.finiteProjectiveStableImageInclusion i h') :=
            hnStableEssential.1
          have hnWaist : IsUniserialObject.IsWaistSubobject
              (Subobject.mk
                (S.finiteProjectiveStableImageInclusion i h')) := by
            apply IsUniserialObject.isWaistSubobject_of_essentialSimpleTop
              lHstable (S.finiteProjectiveStableImageInclusion i h')
            · simpa only [hlHstableComp] using hmWaist'
            · exact hcanonicalTopEssential
          have hJ'nonzero : ¬ IsZero
              (S.finiteProjectiveStableImage j' g') := by
            intro hzeroJ
            apply hg'
            rw [← S.finiteProjectiveStableImagePresentation_comp_inclusion]
            rw [hzeroJ.eq_of_tgt
              (S.finiteProjectiveStableImagePresentation j' g') 0,
              zero_comp]
          let Rad := imageSubobject
            (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
              S.finiteProjectiveStableImagePresentation i h')
          have hRadEq : Rad = Subobject.mk lHstable := by
            dsimp only [Rad]
            exact S.finiteProjectiveStableImageRadical_eq_of_uniserialSimpleCokernel
              i h' hhNat hHstable lHstable (hlmono := hlHstableMono)
              (hlsimple := hlHstableSimple)
          let eRad : (Rad : CoveringHom.FiniteDimensionalModuleCategory
              (C := S.IndecCategoryᵒᵖ) k) ≅
              S.finiteProjectiveStableImage j' g' :=
            eqToIso (congrArg
              (fun Q : Subobject (S.finiteProjectiveStableImage i h') ↦
                (Q : CoveringHom.FiniteDimensionalModuleCategory
                  (C := S.IndecCategoryᵒᵖ) k)) hRadEq) ≪≫
              Subobject.underlyingIso lHstable
          have hRadNonzero : ¬ IsZero
              (Rad : CoveringHom.FiniteDimensionalModuleCategory
                (C := S.IndecCategoryᵒᵖ) k) := by
            intro hzeroRad
            exact hJ'nonzero (hzeroRad.of_iso eRad.symm)
          have hmπn : S.finiteProjectiveStableImageInclusion j' g' ≫
              cokernel.π
                (S.finiteProjectiveStableImageInclusion i h') = 0 := by
            calc
              S.finiteProjectiveStableImageInclusion j' g' ≫
                    cokernel.π
                      (S.finiteProjectiveStableImageInclusion i h') =
                  (lHstable ≫
                    S.finiteProjectiveStableImageInclusion i h') ≫
                    cokernel.π
                      (S.finiteProjectiveStableImageInclusion i h') := by
                rw [hlHstableComp]
              _ = lHstable ≫
                    (S.finiteProjectiveStableImageInclusion i h' ≫
                      cokernel.π
                        (S.finiteProjectiveStableImageInclusion i h')) :=
                Category.assoc _ _ _
              _ = 0 := by rw [cokernel.condition, comp_zero]
          let q :
              cokernel (S.finiteProjectiveStableImageInclusion j' g') ⟶
                cokernel (S.finiteProjectiveStableImageInclusion i h') :=
            cokernel.desc
              (S.finiteProjectiveStableImageInclusion j' g')
              (cokernel.π
                (S.finiteProjectiveStableImageInclusion i h')) hmπn
          letI : Epi q := inferInstance
          have htTopq : tTop ≫ q = 0 := by
            apply (cancel_epi (cokernel.π lHstable)).1
            calc
              cokernel.π lHstable ≫ (tTop ≫ q) =
                  (cokernel.π lHstable ≫ tTop) ≫ q :=
                (Category.assoc _ _ _).symm
              _ = (S.finiteProjectiveStableImageInclusion i h' ≫
                    cokernel.π
                      (S.finiteProjectiveStableImageInclusion j' g')) ≫ q := by
                rw [htTop]
              _ = S.finiteProjectiveStableImageInclusion i h' ≫
                    (cokernel.π
                      (S.finiteProjectiveStableImageInclusion j' g') ≫ q) :=
                Category.assoc _ _ _
              _ = S.finiteProjectiveStableImageInclusion i h' ≫
                    cokernel.π
                      (S.finiteProjectiveStableImageInclusion i h') := by
                dsimp only [q]
                rw [cokernel.π_desc]
              _ = 0 := cokernel.condition _
              _ = cokernel.π lHstable ≫ 0 := by rw [comp_zero]
          have htTopNe : tTop ≠ 0 := by
            intro htZero
            exact Simple.not_isZero (cokernel lHstable)
              (IsZero.of_mono_eq_zero tTop htZero)
          have hqNotIso : ¬ IsIso q := by
            intro hq
            letI : IsIso q := hq
            apply htTopNe
            apply (cancel_mono q).1
            rw [htTopq, zero_comp]
          have hlt : CoveringHom.moduleTotalDimension
              (cokernel (S.finiteProjectiveStableImageInclusion i h')) < d := by
            rw [← hdim]
            exact CoveringHom.moduleTotalDimension_lt_of_epi_not_isIso
              (cokernel (S.finiteProjectiveStableImageInclusion j' g'))
              (cokernel (S.finiteProjectiveStableImageInclusion i h'))
              q hqNotIso
          exact ih (CoveringHom.moduleTotalDimension
              (cokernel (S.finiteProjectiveStableImageInclusion i h'))) hlt
            i h' lHstable hlHstableMono hlHstableSimple hhNat
            (by simpa only [Rad] using hRadNonzero)
            hHstable hnStableEssential hnWaist hcanonicalTopEssential rfl
  exact main
    (CoveringHom.moduleTotalDimension
      (cokernel (S.finiteProjectiveStableImageInclusion j g)))
    j g s inferInstance inferInstance gstable hRzero hJ hmEssential hmWaist
      htopEssential rfl


/-- Every nonterminal simple essential layer lies in a larger essential cyclic
layer whose quotient by it is simple.  This is the existence half of the
ascending socle successor; the two-arm argument must still prove uniqueness
of the simple layer in the ambient quotient. -/
theorem exists_nextCyclicEssentialExtension_of_nonzero_cokernel
    {L G : CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategoryᵒᵖ) k}
    [Simple L] (l : L ⟶ G) [Mono l] (hl : IsEssentialMono l)
    (hquotient : ¬ IsZero (cokernel l)) :
    ∃ (i : S.IndecCategory)
      (h : S.finiteRestrictedContravariantRepresentable (S.fgObj i) ⟶ G)
      (lH : L ⟶ S.finiteRepresentableImage i h),
      h ≠ 0 ∧ Mono lH ∧
        lH ≫ S.finiteRepresentableImageInclusion i h = l ∧
        Simple (cokernel lH) ∧
        IsEssentialMono lH ∧
        IsUniserialObject (S.finiteRepresentableImage i h) ∧
        IsEssentialMono (S.finiteRepresentableImageInclusion i h) := by
  obtain ⟨T, t, i, p, h, hT, ht, hp, hh, hcomp, hle⟩ :=
    S.exists_restrictedRepresentable_lift_of_nonzero_essentialSimpleCokernel
      l hl hquotient
  letI : Simple T := hT
  letI : Mono t := ht
  obtain ⟨lH, hlHmono, hlHcomp, hsimple⟩ :=
    S.restrictedRepresentableLift_cokernel_simple
      l t i p hp h hcomp hle
  letI : Mono lH := hlHmono
  let m := S.finiteRepresentableImageInclusion i h
  have hlHEssential : IsEssentialMono lH :=
    IsUniserialObject.essential_restrict_of_simple
      l hl lH m hlHcomp
  letI : Simple (cokernel lH) := hsimple
  have hHUniserial : IsUniserialObject (S.finiteRepresentableImage i h) :=
    IsUniserialObject.of_essential_simple_cokernel lH hlHEssential
      (IsUniserialObject.of_simple (cokernel lH))
  have hmEssential : IsEssentialMono m := by
    constructor
    · infer_instance
    · intro Z q hmq
      apply hl.2 q
      rw [← hlHcomp, Category.assoc]
      infer_instance
  exact ⟨i, h, lH, hh, hlHmono, hlHcomp, hsimple, hlHEssential,
    hHUniserial, hmEssential⟩

/-- Under the two-arm bound, removing the distinguished projective summand
from the right almost-split middle at the first stable-socle generator leaves
either zero or one indecomposable complement. -/
theorem irreducibleIntoProjective_leftExtensionComplement_zero_or_indecomposable
    (harity : ∀ (i : S.IndecCategory),
      ¬ Projective (S.fgObj i) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData i ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    IsZero
        (S.irreducibleIntoProjective_leftExtensionComplement
          u p g hg).complement ∨
      Indecomposable
        (S.irreducibleIntoProjective_leftExtensionComplement
          u p g hg).complement := by
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let E := (S.minimalLeftAlmostSplitAt u).middle
  let D := S.irreducibleIntoProjective_leftExtensionComplement u p g hg
  let b := S.irreducibleIntoProjective_selectedLeftCokernelMap u p g hg hp
  have hcNonprojective : ¬ Projective (S.fgObj c) := by
    intro hc
    have hcModule : Module.Projective Aᵐᵒᵖ (S.fgObj c) :=
      MagnitudeConjecture.moduleProjective_of_fgProjective (S.fgObj c) hc
    letI : Module.Projective Aᵐᵒᵖ (S.fgObj c) := hcModule
    have hcObj : Projective (S.fgObj c).obj := inferInstance
    apply S.irreducibleIntoProjective_selectedInitialStableNaturalMap_ne_zero
      u p g hg hp
    exact S.finiteRestrictedMap_comp_stableQuotient_eq_zero
      (S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp)
      hcObj
  letI : Module.Finite k D.complement :=
    RightModule.finite_over_field_of_finitelyGenerated k A D.complement
  letI : Module.Finite k E :=
    RightModule.finite_over_field_of_finitelyGenerated k A E
  obtain ⟨dD⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) D.complement
  obtain ⟨dE⟩ := finiteIndecomposableDecomposition_fgModule_exists
    (k := k) E
  let dP :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.singleton
      (S.fgObj p) (S.fgObj_indecomposable p)
  let dSplit := dD.biprod dP
  let eSplit : E ≅ D.complement ⊞ S.fgObj p :=
    D.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have hlocalE (r : Fin dE.n) : IsLocalRing (End (dE.summand r)) :=
    MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
      (k := k) (B := A) (dE.summand r) (dE.indecomposable r)
  have hcount : dE.n = dD.n + 1 :=
    dE.n_eq_of_iso dSplit hlocalE eSplit
  have harityEq :
      FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData c = dE.n :=
    FiniteTauMatrix.rightMiddleArity_eq_of_minimalRightAlmostSplitDecomposition
      S.finiteTauCategoryData.toFiniteRightTauCategoryData c dE
      (S.irreducibleIntoProjective_selectedLeftCokernelMap_isRightAlmostSplit
        u p g hg hp)
      (S.irreducibleIntoProjective_selectedLeftCokernelMap_isRightMinimal
        u p g hg hp)
  have hDle : dD.n ≤ 1 := by
    have hEle : dE.n ≤ 2 := by
      rw [← harityEq]
      exact harity c hcNonprojective
    omega
  by_cases hDzero : IsZero D.complement
  · exact Or.inl hDzero
  · exact Or.inr
      (finiteIndecomposableDecomposition_indecomposable_of_n_le_one
        (k := k) dD hDle hDzero)

/-- Under the two-arm bound, the kernel of the raw first-socle generator is
zero or indecomposable.  This is the kernel-language form of the preceding
split-complement count and is the exact object that must be identified with
the translated next socle generator in the first presentation of
Auslander--Reiten Theorem 3.7. -/
theorem irreducibleIntoProjective_initialStableMapRaw_kernel_zero_or_indecomposable
    (harity : ∀ (i : S.IndecCategory),
      ¬ Projective (S.fgObj i) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData i ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    IsZero
        (kernel
          (S.irreducibleIntoProjective_initialStableMapRaw u p g hg)) ∨
      Indecomposable
        (kernel
          (S.irreducibleIntoProjective_initialStableMapRaw u p g hg)) := by
  let D := S.irreducibleIntoProjective_leftExtensionComplement u p g hg
  let e : D.complement ≅
      kernel (S.irreducibleIntoProjective_initialStableMapRaw u p g hg) :=
    S.irreducibleIntoProjective_leftExtensionComplementIsoInitialStableMapRawKernel
      u p g hg hp
  obtain hzero | hindecomposable :=
    S.irreducibleIntoProjective_leftExtensionComplement_zero_or_indecomposable
      harity u p g hg hp
  · exact Or.inl (hzero.of_iso e.symm)
  · exact Or.inr
      ((MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).1
        hindecomposable)

/-- If the quotient above the distinguished first stable socle is nonzero,
the next essential cyclic layer may be generated by an actual stable module
morphism into `P/U`. -/
theorem irreducibleIntoProjective_exists_nextStableCyclicEssentialExtension
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (hquotient : ¬ IsZero
      (cokernel
        (S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp)))) :
    ∃ (i : S.IndecCategory)
      (h : S.fgObj i ⟶
        S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
      (lH : S.finiteProjectiveStableImage
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp) ⟶
        S.finiteProjectiveStableImage i h),
      S.finiteRestrictedToProjectiveStableMap i h ≠ 0 ∧ Mono lH ∧
        lH ≫ S.finiteProjectiveStableImageInclusion i h =
          S.finiteProjectiveStableImageInclusion
            (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
            (S.irreducibleIntoProjective_selectedInitialStableMap
              u p g hg hp) ∧
        Simple (cokernel lH) ∧
        IsEssentialMono lH ∧
        IsUniserialObject (S.finiteProjectiveStableImage i h) ∧
        IsEssentialMono (S.finiteProjectiveStableImageInclusion i h) := by
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let q := S.irreducibleIntoProjective_cokernelLabel p g hg hp
  let h₀ := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  let L := S.finiteProjectiveStableImage c h₀
  let l := S.finiteProjectiveStableImageInclusion c h₀
  letI : Simple L :=
    S.irreducibleIntoProjective_selectedInitialStableImage_simple
      u p g hg hp
  obtain ⟨i, hNat, lH, hhNat, hlHmono, hlHcomp, hlHsimple,
      hlHessential, hHUniserial, hHessential⟩ :=
    S.exists_nextCyclicEssentialExtension_of_nonzero_cokernel
      l
      (S.irreducibleIntoProjective_selectedInitialStableImageInclusion_isEssential
        u p g hg hp)
      hquotient
  obtain ⟨h, hh⟩ :=
    S.exists_eq_finiteRestrictedToProjectiveStableMap i (S.fgObj q) hNat
  subst hNat
  exact ⟨i, h, lH, hhNat, hlHmono, hlHcomp, hlHsimple, hlHessential,
    hHUniserial, hHessential⟩

/-- For a next cyclic layer above the distinguished first stable socle, the
representable covering that first socle splits from the right almost-split
middle at the next generator. -/
theorem irreducibleIntoProjective_firstSocleCover_split_from_nextRightAlmostSplitMiddle
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (lH : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h)
    [Mono lH] (hlH : IsEssentialMono lH) [Simple (cokernel lH)] :
    ∃ a : S.finiteRestrictedContravariantRepresentable
          (S.minimalRightAlmostSplitAt i).middle ⟶
      S.finiteRestrictedContravariantRepresentable
          (S.fgObj
            (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)),
      IsSplitEpi a ∧
        a ≫ S.finiteProjectiveStableImagePresentation
              (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
              (S.irreducibleIntoProjective_selectedInitialStableMap
                u p g hg hp) ≫ lH =
          S.finiteRestrictedContravariantRepresentableMap
              (S.minimalRightAlmostSplitAt i).map ≫
            S.finiteProjectiveStableImagePresentation i h := by
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let h₀ := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  let L := S.finiteProjectiveStableImage c h₀
  letI : Simple L :=
    S.irreducibleIntoProjective_selectedInitialStableImage_simple
      u p g hg hp
  let P := S.finiteProjectiveStableImageMinimalProjectivePresentation c h₀
    (S.irreducibleIntoProjective_selectedInitialStableNaturalMap_ne_zero
      u p g hg hp)
  obtain ⟨a, ha, hcompat⟩ :=
    S.finiteProjectiveStableImage_projectiveCover_split_from_rightAlmostSplitMiddle
      i h hstable lH hlH P
        (S.minimalRightAlmostSplitAt i).map
        (S.minimalRightAlmostSplitAt i).rightAlmostSplit
  exact ⟨a, ha, hcompat⟩

/-- The representable splitting above reflects to modules: the chosen module
covering the distinguished first stable socle is a direct summand of the
right almost-split middle at the next generator, and its restricted Yoneda
map retains the projective-presentation compatibility. -/
theorem irreducibleIntoProjective_firstSocleModule_split_from_nextRightAlmostSplitMiddle
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (lH : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h)
    [Mono lH] (hlH : IsEssentialMono lH) [Simple (cokernel lH)] :
    ∃ r : (S.minimalRightAlmostSplitAt i).middle ⟶
        S.fgObj
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp),
      IsSplitEpi r ∧
        IsIrreducibleMorphism
            (S.rightKernelMap
                ⟨i,
                  S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
                    i h hstable⟩ ≫ r) ∧
        S.finiteRestrictedContravariantRepresentableMap r ≫
              S.finiteProjectiveStableImagePresentation
                (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
                (S.irreducibleIntoProjective_selectedInitialStableMap
                  u p g hg hp) ≫ lH =
          S.finiteRestrictedContravariantRepresentableMap
              (S.minimalRightAlmostSplitAt i).map ≫
            S.finiteProjectiveStableImagePresentation i h := by
  obtain ⟨a, ha, hcompat⟩ :=
    S.irreducibleIntoProjective_firstSocleCover_split_from_nextRightAlmostSplitMiddle
      u p g hg hp i h hstable lH hlH
  obtain ⟨r, hr, hrmap⟩ :=
    S.exists_splitEpi_with_map_eq_of_finiteRestrictedContravariantRepresentable_splitEpi
      (S.minimalRightAlmostSplitAt i).middle
      (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp) a ha
  refine ⟨r, hr,
    S.rightKernelMap_comp_splitEpi_isIrreducible i
      (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
      (S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
        i h hstable) r hr, ?_⟩
  rw [hrmap]
  exact hcompat

set_option backward.isDefEq.respectTransparency.types true in
/-- The retained first-socle presentation compatibility remains an equality
after inclusion into the ambient stable representable.  In module terms, the
two resulting composites into `P/U` therefore differ by a map through the
distinguished projective `P`. -/
theorem irreducibleIntoProjective_firstSocleStableComposites_eq
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (lH : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h)
    [Mono lH] (hlH : IsEssentialMono lH) [Simple (cokernel lH)]
    (hlHcomp :
      lH ≫ S.finiteProjectiveStableImageInclusion i h =
        S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp)) :
    ∃ r : (S.minimalRightAlmostSplitAt i).middle ⟶
        S.fgObj
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp),
      IsSplitEpi r ∧
        IsIrreducibleMorphism
          (S.rightKernelMap
              ⟨i,
                S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
                  i h hstable⟩ ≫ r) ∧
        S.finiteRestrictedContravariantRepresentableMap
              (r ≫ S.irreducibleIntoProjective_selectedInitialStableMap
                u p g hg hp) ≫
            S.finiteProjectiveStableQuotient
              (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)) =
          S.finiteRestrictedContravariantRepresentableMap
              ((S.minimalRightAlmostSplitAt i).map ≫ h) ≫
            S.finiteProjectiveStableQuotient
              (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)) := by
  obtain ⟨r, hr, hirred, hcompat⟩ :=
    S.irreducibleIntoProjective_firstSocleModule_split_from_nextRightAlmostSplitMiddle
      u p g hg hp i h hstable lH hlH
  refine ⟨r, hr, hirred, ?_⟩
  have hcompat' := congrArg
    (fun z ↦ z ≫ S.finiteProjectiveStableImageInclusion i h) hcompat
  simp only [Category.assoc] at hcompat'
  rw [hlHcomp,
    S.finiteProjectiveStableImagePresentation_comp_inclusion] at hcompat'
  have hright :
      S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫
          S.finiteProjectiveStableImagePresentation i h ≫
            S.finiteProjectiveStableImageInclusion i h =
        S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫
          S.finiteRestrictedToProjectiveStableMap i h := by
    exact congrArg
      (fun z ↦
        S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫ z)
      (S.finiteProjectiveStableImagePresentation_comp_inclusion i h)
  have hstableEq := hcompat'.trans hright
  dsimp only [finiteRestrictedToProjectiveStableMap] at hstableEq
  simp only [← Category.assoc] at hstableEq
  calc
    _ = (S.finiteRestrictedContravariantRepresentableMap r ≫
          S.finiteRestrictedContravariantRepresentableMap
            (S.irreducibleIntoProjective_selectedInitialStableMap
              u p g hg hp)) ≫
        S.finiteProjectiveStableQuotient
          (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)) :=
      congrArg
        (fun z ↦ z ≫ S.finiteProjectiveStableQuotient
          (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)))
        (S.finiteRestrictedContravariantRepresentableMap_comp r
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp))
    _ = (S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫
          S.finiteRestrictedContravariantRepresentableMap h) ≫
        S.finiteProjectiveStableQuotient
          (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)) :=
      hstableEq
    _ = _ :=
      congrArg
        (fun z ↦ z ≫ S.finiteProjectiveStableQuotient
          (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)))
        (S.finiteRestrictedContravariantRepresentableMap_comp
          (S.minimalRightAlmostSplitAt i).map h).symm

/-- The equality of stable composites can be lifted through the distinguished
projective quotient.  The resulting correction `s` is retained as an actual
module morphism, rather than merely as a morphism in the functor category. -/
theorem irreducibleIntoProjective_exists_firstSocleProjectiveCorrection
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (lH : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h)
    [Mono lH] (hlH : IsEssentialMono lH) [Simple (cokernel lH)]
    (hlHcomp :
      lH ≫ S.finiteProjectiveStableImageInclusion i h =
        S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp)) :
    ∃ (r : (S.minimalRightAlmostSplitAt i).middle ⟶
          S.fgObj
            (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp))
      (s : (S.minimalRightAlmostSplitAt i).middle ⟶ S.fgObj p),
      IsSplitEpi r ∧
        IsIrreducibleMorphism
          (S.rightKernelMap
              ⟨i,
                S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
                  i h hstable⟩ ≫ r) ∧
        S.finiteRestrictedContravariantRepresentableMap
              (s ≫ S.irreducibleIntoProjective_quotientMap p g hg hp) =
          S.finiteRestrictedContravariantRepresentableMap
              (r ≫ S.irreducibleIntoProjective_selectedInitialStableMap
                u p g hg hp) -
            S.finiteRestrictedContravariantRepresentableMap
              ((S.minimalRightAlmostSplitAt i).map ≫ h) := by
  obtain ⟨r, hr, hirred, hstableEq⟩ :=
    S.irreducibleIntoProjective_firstSocleStableComposites_eq
      u p g hg hp i h hstable lH hlH hlHcomp
  obtain ⟨s, hs⟩ :=
    S.exists_projectiveFactor_of_finiteRestrictedStableComposites_eq p
      (S.irreducibleIntoProjective_quotientMap p g hg hp) hp
      (r ≫ S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp)
      ((S.minimalRightAlmostSplitAt i).map ≫ h) hstableEq
  exact ⟨r, s, hr, hirred, hs⟩

/-- A candidate next essential layer supplies, after Auslander--Reiten
translation, an incoming occurrence at the distinguished first-socle
generator. -/
theorem irreducibleIntoProjective_nextLayer_translatedArrowMultiplicity_pos
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (lH : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h)
    [Mono lH] (hlH : IsEssentialMono lH) [Simple (cokernel lH)] :
    let hi :=
      S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
        i h hstable
    0 < FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (S.rightTranslationLabel ⟨i, hi⟩)
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp) := by
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let hi :=
    S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
      i h hstable
  obtain ⟨r, hr, -, -⟩ :=
    S.irreducibleIntoProjective_firstSocleModule_split_from_nextRightAlmostSplitMiddle
      u p g hg hp i h hstable lH hlH
  have hci : 0 < FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData c i :=
    S.arrowMultiplicity_pos_of_splitEpi_minimalRightAlmostSplitMiddle
      i c hi r hr
  have htranslate := S.arrowMultiplicity_eq_inverseTranslation
    (S.rightTranslationEquiv ⟨i, hi⟩) c
  have hval : (S.rightTranslationEquiv ⟨i, hi⟩).1 =
      S.rightTranslationLabel ⟨i, hi⟩ := by
    exact congrArg Subtype.val
      (Equiv.ofBijective_apply S.rightTranslation
        ⟨S.rightTranslation_injective, S.rightTranslation_surjective⟩ ⟨i, hi⟩)
  have htranslate' : FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData
        (S.rightTranslationLabel ⟨i, hi⟩) c =
    FiniteTauMatrix.arrowMultiplicity
      S.finiteTauCategoryData.toFiniteRightTauCategoryData c i := by
    rw [← hval]
    simpa only [Equiv.symm_apply_apply] using htranslate
  change 0 < FiniteTauMatrix.arrowMultiplicity
    S.finiteTauCategoryData.toFiniteRightTauCategoryData
      (S.rightTranslationLabel ⟨i, hi⟩) c
  rw [htranslate']
  exact hci

set_option backward.isDefEq.respectTransparency.types false in
/-- The translated generator of a next essential layer is exactly the kernel
of the raw first-socle map.  The projective correction retained from the
functor-category comparison rules out the otherwise ambiguous collision with
the distinguished projective arm.  This is the multiplicity-sensitive core
of Auslander--Reiten Proposition 2.6. -/
theorem
irreducibleIntoProjective_nextLayer_translationIsoInitialStableMapRawKernel
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (lH : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h)
    [Mono lH] (hlH : IsEssentialMono lH) [Simple (cokernel lH)]
    (hlHcomp :
      lH ≫ S.finiteProjectiveStableImageInclusion i h =
        S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp)) :
    Nonempty
      (S.fgObj
          (S.rightTranslationLabel
            ⟨i,
              S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
                i h hstable⟩) ≅
        kernel
          (S.irreducibleIntoProjective_initialStableMapRaw u p g hg)) := by
  let hi :=
    S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
      i h hstable
  let z : {j : Fin S.n // ¬ Projective (S.fgObj j)} := ⟨i, hi⟩
  let x := (S.rightTranslation z).1
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let E := (S.minimalLeftAlmostSplitAt u).middle
  let t := S.irreducibleIntoProjective_leftExtensionFactor u p g hg
  let D := S.irreducibleIntoProjective_leftExtensionComplement u p g hg
  let b := S.irreducibleIntoProjective_selectedLeftCokernelMap u p g hg hp
  let h₀ := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  let q := S.irreducibleIntoProjective_quotientMap p g hg hp
  let κ := S.rightKernelMap z
  obtain ⟨r, s, hr, hf, hs⟩ :=
    S.irreducibleIntoProjective_exists_firstSocleProjectiveCorrection
      u p g hg hp i h hstable lH hlH hlHcomp
  let f : S.fgObj x ⟶ S.fgObj c := S.rightKernelMap z ≫ r
  have hf' : IsIrreducibleMorphism f := hf
  obtain ⟨a, ha⟩ :=
    (S.irreducibleIntoProjective_selectedLeftCokernelMap_isRightAlmostSplit
      u p g hg hp).factors f hf'.not_isSplitEpi
  have haSplit : IsSplitMono a :=
    (hf'.factorization a b ha).resolve_right
      (S.irreducibleIntoProjective_selectedLeftCokernelMap_isRightAlmostSplit
        u p g hg hp).not_isSplitEpi
  letI : IsSplitMono a := haSplit
  have hκB : κ ≫ (S.minimalRightAlmostSplitAt i).map = 0 := by
    change S.rightKernelMap z ≫ (S.minimalRightAlmostSplitAt z.1).map = 0
    dsimp only [κ, rightKernelMap]
    simp only [Category.assoc, kernel.condition, comp_zero]
  have hκBh : κ ≫ ((S.minimalRightAlmostSplitAt i).map ≫ h) = 0 := by
    rw [← Category.assoc, hκB, zero_comp]
  have hnat :
      S.finiteRestrictedContravariantRepresentableMap (κ ≫ (s ≫ q)) =
        S.finiteRestrictedContravariantRepresentableMap (κ ≫ (r ≫ h₀)) := by
    calc
      S.finiteRestrictedContravariantRepresentableMap (κ ≫ (s ≫ q)) =
          S.finiteRestrictedContravariantRepresentableMap κ ≫
            S.finiteRestrictedContravariantRepresentableMap (s ≫ q) :=
        S.finiteRestrictedContravariantRepresentableMap_comp κ (s ≫ q)
      _ = S.finiteRestrictedContravariantRepresentableMap κ ≫
          (S.finiteRestrictedContravariantRepresentableMap (r ≫ h₀) -
            S.finiteRestrictedContravariantRepresentableMap
              ((S.minimalRightAlmostSplitAt i).map ≫ h)) :=
        congrArg
          (fun z ↦ S.finiteRestrictedContravariantRepresentableMap κ ≫ z) hs
      _ = S.finiteRestrictedContravariantRepresentableMap κ ≫
            S.finiteRestrictedContravariantRepresentableMap (r ≫ h₀) -
          S.finiteRestrictedContravariantRepresentableMap κ ≫
            S.finiteRestrictedContravariantRepresentableMap
              ((S.minimalRightAlmostSplitAt i).map ≫ h) :=
        Preadditive.comp_sub _ _ _
      _ = S.finiteRestrictedContravariantRepresentableMap (κ ≫ (r ≫ h₀)) -
          S.finiteRestrictedContravariantRepresentableMap
            (κ ≫ ((S.minimalRightAlmostSplitAt i).map ≫ h)) := by
        exact congrArg₂ (fun z w ↦ z - w)
          (S.finiteRestrictedContravariantRepresentableMap_comp
            κ (r ≫ h₀)).symm
          (S.finiteRestrictedContravariantRepresentableMap_comp
            κ ((S.minimalRightAlmostSplitAt i).map ≫ h)).symm
      _ = S.finiteRestrictedContravariantRepresentableMap (κ ≫ (r ≫ h₀)) -
          S.finiteRestrictedContravariantRepresentableMap 0 := by
        rw [hκBh]
      _ = S.finiteRestrictedContravariantRepresentableMap (κ ≫ (r ≫ h₀)) := by
        rw [S.finiteRestrictedContravariantRepresentableMap_zero, sub_zero]
  have hmoduleQ : κ ≫ (s ≫ q) = κ ≫ (r ≫ h₀) :=
    S.finiteRestrictedContravariantRepresentableMap_injective_from_fgObj x
      (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)) hnat
  have hbq : b ≫ h₀ = t ≫ q :=
    S.irreducibleIntoProjective_selectedLeftCokernelMap_comp_selectedInitialStableMap
      u p g hg hp
  have hcoordinateQ : (a ≫ t) ≫ q = (κ ≫ s) ≫ q := by
    calc
      (a ≫ t) ≫ q = a ≫ (t ≫ q) := Category.assoc _ _ _
      _ = a ≫ (b ≫ h₀) := congrArg (fun z ↦ a ≫ z) hbq.symm
      _ = (a ≫ b) ≫ h₀ := (Category.assoc _ _ _).symm
      _ = (κ ≫ r) ≫ h₀ := by
        change a ≫ b = κ ≫ r at ha
        exact congrArg (fun z ↦ z ≫ h₀) ha
      _ = κ ≫ (r ≫ h₀) := Category.assoc _ _ _
      _ = κ ≫ (s ≫ q) := hmoduleQ.symm
      _ = (κ ≫ s) ≫ q := (Category.assoc _ _ _).symm
  let eSplit : E ≅ D.complement ⊞ S.fgObj p :=
    D.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  have heSplitSnd : eSplit.hom ≫ biprod.snd = t := by
    exact D.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso_hom_comp
      (BinaryBiproduct.isLimit _ _) (Discrete.mk WalkingPair.right)
  let aSplit : S.fgObj x ⟶ D.complement ⊞ S.fgObj p :=
    a ≫ eSplit.hom
  have haSplitSndQ : (aSplit ≫ biprod.snd) ≫ q = (κ ≫ s) ≫ q := by
    dsimp only [aSplit]
    calc
      ((a ≫ eSplit.hom) ≫ biprod.snd) ≫ q =
          (a ≫ (eSplit.hom ≫ biprod.snd)) ≫ q :=
        congrArg (fun z ↦ z ≫ q) (Category.assoc _ _ _)
      _ = (a ≫ t) ≫ q :=
        congrArg (fun z ↦ (a ≫ z) ≫ q) heSplitSnd
      _ = (κ ≫ s) ≫ q := hcoordinateQ
  letI : IsSplitMono aSplit := by
    dsimp only [aSplit]
    infer_instance
  letI : IsLocalRing (End (S.fgObj x)) :=
    MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
      (k := k) (B := A) (S.fgObj x) (S.fgObj_indecomposable x)
  let eKernel : D.complement ≅
      kernel (S.irreducibleIntoProjective_initialStableMapRaw u p g hg) :=
    S.irreducibleIntoProjective_leftExtensionComplementIsoInitialStableMapRawKernel
      u p g hg hp
  rcases
      MagnitudeConjecture.CategoryTheory.splitMono_fst_or_snd_of_splitMono_to_biprod
        aSplit with hleft | hright
  · let left : S.fgObj x ⟶ D.complement := aSplit ≫ biprod.fst
    letI : IsSplitMono left := hleft
    obtain hDzero | hDindecomposable :=
      S.irreducibleIntoProjective_leftExtensionComplement_zero_or_indecomposable
        harity u p g hg hp
    · have hxzero : IsZero (S.fgObj x) := by
        rw [IsZero.iff_id_eq_zero]
        have hleftzero : left = 0 := hDzero.eq_of_tgt _ _
        calc
          𝟙 (S.fgObj x) = left ≫ retraction left :=
            (IsSplitMono.id left).symm
          _ = 0 ≫ retraction left :=
            congrArg (fun q ↦ q ≫ retraction left) hleftzero
          _ = 0 := zero_comp
      exact (S.fgObj_indecomposable x).1 hxzero |>.elim
    · let hleftIso : IsIso left :=
        MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
          hDindecomposable left (S.fgObj_indecomposable x).1
      exact ⟨(@asIso _ _ _ _ left hleftIso) ≪≫ eKernel⟩
  · let right : S.fgObj x ⟶ S.fgObj p := aSplit ≫ biprod.snd
    letI : IsSplitMono right := hright
    let hrightIso : IsIso right :=
      MagnitudeConjecture.CategoryTheory.isIso_of_isSplitMono_to_indecomposable
        (S.fgObj_indecomposable p) right (S.fgObj_indecomposable x).1
    letI : IsIso right := hrightIso
    by_cases hxp : x = p
    · let ep : S.fgObj x ≅ S.fgObj p := eqToIso (congrArg S.fgObj hxp)
      letI : Mono g := irreducibleIntoProjective_mono g hg hp
      have hkillQ : (right - κ ≫ s) ≫ q = 0 := by
        rw [Preadditive.sub_comp, haSplitSndQ, sub_self]
      let eQ := S.irreducibleIntoProjective_cokernelIso p g hg hp
      have hkill : (right - κ ≫ s) ≫ cokernel.π g = 0 := by
        apply (cancel_mono eQ.hom).1
        dsimp only [q, irreducibleIntoProjective_quotientMap] at hkillQ
        simpa only [Category.assoc, zero_comp] using hkillQ
      let K : KernelFork (cokernel.π g) :=
        KernelFork.ofι (right - κ ≫ s) hkill
      let hkernel : IsLimit
          (KernelFork.ofι g (cokernel.condition g)) :=
        Abelian.monoIsKernelOfCokernel
          (CokernelCofork.ofπ (cokernel.π g) (cokernel.condition g))
          (cokernelIsCokernel g)
      let d : S.fgObj x ⟶ S.fgObj u := hkernel.lift K
      have hd : d ≫ g = right - κ ≫ s :=
        hkernel.fac K WalkingParallelPair.zero
      let rightEnd : S.fgObj p ⟶ S.fgObj p := ep.inv ≫ right
      let κsEnd : S.fgObj p ⟶ S.fgObj p := ep.inv ≫ κ ≫ s
      let dgEnd : S.fgObj p ⟶ S.fgObj p := ep.inv ≫ d ≫ g
      letI : IsLocalRing (End (S.fgObj p)) :=
        MagnitudeConjecture.fgEnd_isLocalRing_of_indecomposable
          (k := k) (B := A) (S.fgObj p) (S.fgObj_indecomposable p)
      have hκsNonunit : ¬ IsUnit (End.of κsEnd : End (S.fgObj p)) := by
        intro hunit
        haveI : IsIso κsEnd := (isUnit_iff_isIso κsEnd).1 hunit
        have hκSplit : IsSplitMono κ := by
          apply IsSplitMono.mk'
          refine
            { retraction := s ≫ inv κsEnd ≫ ep.inv
              id := ?_ }
          calc
            κ ≫ (s ≫ inv κsEnd ≫ ep.inv) =
                ep.hom ≫ (ep.inv ≫ κ ≫ s) ≫ inv κsEnd ≫ ep.inv := by
              simp only [Category.assoc, Iso.hom_inv_id_assoc]
            _ = ep.hom ≫ κsEnd ≫ inv κsEnd ≫ ep.inv := rfl
            _ = ep.hom ≫ ep.inv := by
              exact congrArg (fun z ↦ ep.hom ≫ z)
                (IsIso.hom_inv_id_assoc κsEnd ep.inv)
            _ = 𝟙 (S.fgObj x) := ep.hom_inv_id
        exact (S.rightKernelMap_leftAlmostSplit z).not_isSplitMono hκSplit
      have hdgNonunit : ¬ IsUnit (End.of dgEnd : End (S.fgObj p)) := by
        intro hunit
        haveI : IsIso dgEnd := (isUnit_iff_isIso dgEnd).1 hunit
        have hgSplit : IsSplitEpi g := by
          apply IsSplitEpi.mk'
          refine
            { section_ := inv dgEnd ≫ ep.inv ≫ d
              id := ?_ }
          calc
            (inv dgEnd ≫ ep.inv ≫ d) ≫ g = inv dgEnd ≫ dgEnd := by
              dsimp only [dgEnd]
              simp only [Category.assoc]
            _ = 𝟙 (S.fgObj p) := by
              simpa only [Category.comp_id] using
                (IsIso.inv_hom_id_assoc dgEnd (𝟙 (S.fgObj p)))
        exact hg.not_isSplitEpi hgSplit
      have hsum :
          (End.of dgEnd : End (S.fgObj p)) + End.of κsEnd =
            End.of rightEnd := by
        apply End.ext
        change dgEnd + κsEnd = rightEnd
        dsimp only [dgEnd, κsEnd, rightEnd]
        calc
          ep.inv ≫ d ≫ g + ep.inv ≫ κ ≫ s =
              ep.inv ≫ (d ≫ g + κ ≫ s) := by
            simp only [Preadditive.comp_add, Category.assoc]
          _ = ep.inv ≫ ((right - κ ≫ s) + κ ≫ s) := by rw [hd]
          _ = ep.inv ≫ right := by rw [sub_add_cancel]
      have hsumUnit : IsUnit
          ((End.of dgEnd : End (S.fgObj p)) + End.of κsEnd) := by
        rw [hsum]
        exact (isUnit_iff_isIso rightEnd).2 (by
          dsimp only [rightEnd]
          infer_instance)
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsumUnit with
        hdgUnit | hκsUnit
      · exact (hdgNonunit hdgUnit).elim
      · exact (hκsNonunit hκsUnit).elim
    · have hlabel : x = p :=
        S.fgObj_skeletal ⟨@asIso _ _ _ _ right hrightIso⟩
      exact (hxp hlabel).elim

set_option backward.isDefEq.respectTransparency.types false in
/-- Two candidate next layers above the distinguished first stable socle have
the same indecomposable generator.  Both translated generators identify with
the same raw kernel, and injectivity of Auslander--Reiten translation then
recovers equality of the original labels. -/
theorem irreducibleIntoProjective_nextLayer_label_eq
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i i' : S.IndecCategory)
    (h : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (h' : S.fgObj i' ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (hstable' : S.finiteRestrictedToProjectiveStableMap i' h' ≠ 0)
    (lH : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h)
    (lH' : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i' h')
    [Mono lH] (hlH : IsEssentialMono lH) [Simple (cokernel lH)]
    [Mono lH'] (hlH' : IsEssentialMono lH') [Simple (cokernel lH')]
    (hlHcomp :
      lH ≫ S.finiteProjectiveStableImageInclusion i h =
        S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp))
    (hlHcomp' :
      lH' ≫ S.finiteProjectiveStableImageInclusion i' h' =
        S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp)) :
    i' = i := by
  let hi :=
    S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
      i h hstable
  let hi' :=
    S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
      i' h' hstable'
  obtain ⟨e⟩ :=
    S.irreducibleIntoProjective_nextLayer_translationIsoInitialStableMapRawKernel
      harity u p g hg hp i h hstable lH hlH hlHcomp
  obtain ⟨e'⟩ :=
    S.irreducibleIntoProjective_nextLayer_translationIsoInitialStableMapRawKernel
      harity u p g hg hp i' h' hstable' lH' hlH' hlHcomp'
  have htranslationLabel :
      S.rightTranslationLabel ⟨i', hi'⟩ =
        S.rightTranslationLabel ⟨i, hi⟩ :=
    S.fgObj_skeletal ⟨e' ≪≫ e.symm⟩
  have htranslation :
      S.rightTranslation ⟨i', hi'⟩ =
        S.rightTranslation ⟨i, hi⟩ :=
    Subtype.ext htranslationLabel
  have hsource : (⟨i', hi'⟩ :
      {j : S.IndecCategory // ¬ Projective (S.fgObj j)}) =
      ⟨i, hi⟩ :=
    S.rightTranslation_injective htranslation
  exact congrArg Subtype.val hsource

set_option backward.isDefEq.respectTransparency.types false in
/-- Once two next-layer candidates have the same generator label, their maps
to the quotient by the distinguished first socle are scalar-proportional. -/
theorem irreducibleIntoProjective_nextLayer_quotientMaps_proportional
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h h' : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (hstable' : S.finiteRestrictedToProjectiveStableMap i h' ≠ 0)
    (lH : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h)
    (lH' : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h')
    [Mono lH] (hlH : IsEssentialMono lH) [Simple (cokernel lH)]
    [Mono lH'] (hlH' : IsEssentialMono lH') [Simple (cokernel lH')]
    (hlHcomp :
      lH ≫ S.finiteProjectiveStableImageInclusion i h =
        S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp))
    (hlHcomp' :
      lH' ≫ S.finiteProjectiveStableImageInclusion i h' =
        S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp)) :
    ∃ α : k,
      S.finiteRestrictedToProjectiveStableMap i h' ≫
          cokernel.π
            (S.finiteProjectiveStableImageInclusion
              (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
              (S.irreducibleIntoProjective_selectedInitialStableMap
                u p g hg hp)) =
        (α • S.finiteRestrictedToProjectiveStableMap i h) ≫
          cokernel.π
            (S.finiteProjectiveStableImageInclusion
              (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
              (S.irreducibleIntoProjective_selectedInitialStableMap
                u p g hg hp)) := by
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let h₀ := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  let L := S.finiteProjectiveStableImage c h₀
  let l := S.finiteProjectiveStableImageInclusion c h₀
  let pL := S.finiteProjectiveStableImagePresentation c h₀
  let H := S.finiteRestrictedToProjectiveStableMap i h
  let H' := S.finiteRestrictedToProjectiveStableMap i h'
  let hi :=
    S.not_projective_of_finiteRestrictedToProjectiveStableMap_ne_zero
      i h hstable
  letI : Simple L :=
    S.irreducibleIntoProjective_selectedInitialStableImage_simple
      u p g hg hp
  obtain ⟨r, hr, -, hboundary⟩ :=
    S.irreducibleIntoProjective_firstSocleModule_split_from_nextRightAlmostSplitMiddle
      u p g hg hp i h hstable lH hlH
  obtain ⟨r', hr', -, hboundary'⟩ :=
    S.irreducibleIntoProjective_firstSocleModule_split_from_nextRightAlmostSplitMiddle
      u p g hg hp i h' hstable' lH' hlH'
  have hpL : pL ≠ 0 :=
    S.finiteProjectiveStableImagePresentation_ne_zero c h₀
      (S.irreducibleIntoProjective_selectedInitialStableNaturalMap_ne_zero
        u p g hg hp)
  obtain ⟨α, hproportional⟩ :=
    S.minimalRightAlmostSplit_splitEpi_simpleCover_proportional
      i c hi pL hpL r r' hr hr'
  have hboundaryAmbient :
      (S.finiteRestrictedContravariantRepresentableMap r ≫ pL) ≫ l =
        S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫ H := by
    have hcompat := congrArg
      (fun z ↦ z ≫ S.finiteProjectiveStableImageInclusion i h) hboundary
    simp only [Category.assoc] at hcompat
    rw [hlHcomp] at hcompat
    calc
      _ = S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫
          (S.finiteProjectiveStableImagePresentation i h ≫
            S.finiteProjectiveStableImageInclusion i h) := by
        simpa only [pL, l, Category.assoc] using hcompat
      _ = _ := congrArg
        (fun z ↦ S.finiteRestrictedContravariantRepresentableMap
          (S.minimalRightAlmostSplitAt i).map ≫ z)
        (S.finiteProjectiveStableImagePresentation_comp_inclusion i h)
  have hboundaryAmbient' :
      (S.finiteRestrictedContravariantRepresentableMap r' ≫ pL) ≫ l =
        S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫ H' := by
    have hcompat := congrArg
      (fun z ↦ z ≫ S.finiteProjectiveStableImageInclusion i h') hboundary'
    simp only [Category.assoc] at hcompat
    rw [hlHcomp'] at hcompat
    calc
      _ = S.finiteRestrictedContravariantRepresentableMap
            (S.minimalRightAlmostSplitAt i).map ≫
          (S.finiteProjectiveStableImagePresentation i h' ≫
            S.finiteProjectiveStableImageInclusion i h') := by
        simpa only [pL, l, Category.assoc] using hcompat
      _ = _ := congrArg
        (fun z ↦ S.finiteRestrictedContravariantRepresentableMap
          (S.minimalRightAlmostSplitAt i).map ≫ z)
        (S.finiteProjectiveStableImagePresentation_comp_inclusion i h')
  refine ⟨α, ?_⟩
  exact S.minimalRightAlmostSplit_quotientMaps_proportional_of_boundary
    i l
    (S.irreducibleIntoProjective_selectedInitialStableImageInclusion_isEssential
      u p g hg hp)
    H H'
    (S.finiteRestrictedContravariantRepresentableMap r ≫ pL)
    (S.finiteRestrictedContravariantRepresentableMap r' ≫ pL)
    hboundaryAmbient hboundaryAmbient' α hproportional

set_option backward.isDefEq.respectTransparency.types false in
/-- A chosen next cyclic layer determines an essential simple subobject of the
quotient by the distinguished first stable socle.  Every simple subobject of
that quotient lifts to another next-layer candidate; translation injectivity
and square-free boundary proportionality force it to factor through the
chosen one. -/
theorem irreducibleIntoProjective_nextLayer_cokernelMap_essential
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (lH : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h)
    [Mono lH] (hlH : IsEssentialMono lH) [Simple (cokernel lH)]
    (hlHcomp :
      lH ≫ S.finiteProjectiveStableImageInclusion i h =
        S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp)) :
    ∃ t₀ : cokernel lH ⟶
        cokernel
          (S.finiteProjectiveStableImageInclusion
            (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
            (S.irreducibleIntoProjective_selectedInitialStableMap
              u p g hg hp)),
      Mono t₀ ∧ IsEssentialMono t₀ ∧
        cokernel.π lH ≫ t₀ =
          S.finiteProjectiveStableImageInclusion i h ≫
            cokernel.π
              (S.finiteProjectiveStableImageInclusion
                (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
                (S.irreducibleIntoProjective_selectedInitialStableMap
                  u p g hg hp)) := by
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let h₀ := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  let L := S.finiteProjectiveStableImage c h₀
  let l := S.finiteProjectiveStableImageInclusion c h₀
  let H := S.finiteRestrictedToProjectiveStableMap i h
  let m := S.finiteProjectiveStableImageInclusion i h
  letI : Simple L :=
    S.irreducibleIntoProjective_selectedInitialStableImage_simple
      u p g hg hp
  have sq : IsPullback lH (𝟙 L) m l :=
    IsPullback.of_vert_isIso_mono ⟨by
      simpa only [hlHcomp, Category.id_comp]⟩
  let t₀ : cokernel lH ⟶ cokernel l :=
    cokernel.map lH l (𝟙 L) m sq.w
  letI : Mono t₀ := Abelian.mono_cokernel_map_of_isPullback sq
  have ht₀ : cokernel.π lH ≫ t₀ = m ≫ cokernel.π l :=
    cokernel.π_desc _ _ _
  have ht₀essential : IsEssentialMono t₀ := by
    apply S.finiteDimensionalModule_isEssentialMono_of_simple_restrictedRepresentable_factors
      t₀
    intro T hT t ht i' p' hp'
    letI : Simple T := hT
    letI : Mono t := ht
    let HNat' : S.finiteRestrictedContravariantRepresentable (S.fgObj i') ⟶
        S.finiteProjectiveStableContravariantRepresentable
          (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)) :=
      Projective.factorThru (p' ≫ t) (cokernel.π l)
    have hHNat'comp : HNat' ≫ cokernel.π l = p' ≫ t :=
      Projective.factorThru_comp (p' ≫ t) (cokernel.π l)
    have hp't : p' ≫ t ≠ 0 := by
      intro hzero
      apply hp'
      apply (cancel_mono t).1
      simpa only [zero_comp] using hzero
    have hHNat' : HNat' ≠ 0 := by
      intro hzero
      apply hp't
      rw [← hHNat'comp, hzero, zero_comp]
    have himage : imageSubobject HNat' ≠ ⊥ := by
      intro himage
      apply hHNat'
      have harrow : (imageSubobject HNat').arrow = 0 := by
        rw [← Subobject.mk_eq_bot_iff_zero]
        simpa only [Subobject.mk_arrow] using himage
      rw [← imageSubobject_arrow_comp HNat', harrow, comp_zero]
    have hle : Subobject.mk l ≤ imageSubobject HNat' :=
      IsUniserialObject.simple_le_nonzero_subobject_of_essential
        l
        (S.irreducibleIntoProjective_selectedInitialStableImageInclusion_isEssential
          u p g hg hp)
        (imageSubobject HNat') himage
    obtain ⟨h', hh'⟩ :=
      S.exists_eq_finiteRestrictedToProjectiveStableMap i'
        (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp)) HNat'
    have hstable' : S.finiteRestrictedToProjectiveStableMap i' h' ≠ 0 := by
      rw [hh']
      exact hHNat'
    have hstableComp' :
        S.finiteRestrictedToProjectiveStableMap i' h' ≫ cokernel.π l =
          p' ≫ t := by
      rw [hh']
      exact hHNat'comp
    have hstableLe' : Subobject.mk l ≤ imageSubobject
        (S.finiteRestrictedToProjectiveStableMap i' h') := by
      rw [hh']
      exact hle
    obtain ⟨lH', hlH'mono, hlH'comp, hlH'simple⟩ :=
      S.restrictedRepresentableLift_cokernel_simple
        l t i' p' hp' (S.finiteRestrictedToProjectiveStableMap i' h')
          hstableComp' hstableLe'
    let lHstable : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp) ⟶
        S.finiteProjectiveStableImage i' h' := lH'
    have hlHstableMono : Mono lHstable := by
      dsimp only [lHstable]
      exact hlH'mono
    letI : Mono lHstable := hlHstableMono
    have hlHstableSimple : Simple (cokernel lHstable) := by
      dsimp only [lHstable]
      exact hlH'simple
    letI : Simple (cokernel lHstable) := hlHstableSimple
    have hlHstableComp :
        lHstable ≫ S.finiteProjectiveStableImageInclusion i' h' = l := by
      dsimp only [lHstable]
      change lH' ≫ S.finiteProjectiveStableImageInclusion i' h' = l
      change lH' ≫ S.finiteProjectiveStableImageInclusion i' h' = l at hlH'comp
      exact hlH'comp
    have hlHstableEssential : IsEssentialMono lHstable :=
      IsUniserialObject.essential_restrict_of_simple
        l
        (S.irreducibleIntoProjective_selectedInitialStableImageInclusion_isEssential
          u p g hg hp)
        lHstable (S.finiteProjectiveStableImageInclusion i' h')
        hlHstableComp
    have hii : i' = i :=
      S.irreducibleIntoProjective_nextLayer_label_eq
        harity u p g hg hp i i' h h' hstable hstable' lH lHstable
        hlH hlHstableEssential hlHcomp hlHstableComp
    subst i'
    letI : Mono lHstable := hlHstableMono
    letI : Simple (cokernel lHstable) := hlHstableSimple
    obtain ⟨α, hproportional⟩ :=
      S.irreducibleIntoProjective_nextLayer_quotientMaps_proportional
        u p g hg hp i h h' hstable hstable' lH lHstable
        hlH hlHstableEssential hlHcomp hlHstableComp
    let p₀ := S.finiteProjectiveStableImagePresentation i h ≫ cokernel.π lH
    have hfixed : H ≫ cokernel.π l = p₀ ≫ t₀ := by
      calc
        H ≫ cokernel.π l =
            (S.finiteProjectiveStableImagePresentation i h ≫ m) ≫
              cokernel.π l := by
          rw [S.finiteProjectiveStableImagePresentation_comp_inclusion]
        _ = S.finiteProjectiveStableImagePresentation i h ≫
              (m ≫ cokernel.π l) := Category.assoc _ _ _
        _ = S.finiteProjectiveStableImagePresentation i h ≫
              (cokernel.π lH ≫ t₀) := by rw [ht₀]
        _ = p₀ ≫ t₀ := (Category.assoc _ _ _).symm
    refine ⟨α • p₀, ?_⟩
    calc
      (α • p₀) ≫ t₀ = α • (p₀ ≫ t₀) := by rw [Linear.smul_comp]
      _ = α • (H ≫ cokernel.π l) := by rw [hfixed]
      _ = (α • H) ≫ cokernel.π l := by rw [Linear.smul_comp]
      _ = S.finiteRestrictedToProjectiveStableMap i h' ≫
          cokernel.π l := hproportional.symm
      _ = p' ≫ t := hstableComp'
  exact ⟨t₀, inferInstance, ht₀essential, ht₀⟩

/-- Canonical-map form of first-successor essentiality. -/
theorem irreducibleIntoProjective_nextLayer_top_essential
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (i : S.IndecCategory)
    (h : S.fgObj i ⟶
      S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))
    (hstable : S.finiteRestrictedToProjectiveStableMap i h ≠ 0)
    (lH : S.finiteProjectiveStableImage
        (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
        (S.irreducibleIntoProjective_selectedInitialStableMap
          u p g hg hp) ⟶
      S.finiteProjectiveStableImage i h)
    [Mono lH] (hlH : IsEssentialMono lH) [Simple (cokernel lH)]
    (hlHcomp :
      lH ≫ S.finiteProjectiveStableImageInclusion i h =
        S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp)) :
    IsEssentialMono
      (cokernelInclusionOfComp lH
        (S.finiteProjectiveStableImageInclusion i h)) := by
  obtain ⟨t₀, ht₀mono, ht₀essential, ht₀⟩ :=
    S.irreducibleIntoProjective_nextLayer_cokernelMap_essential
      harity u p g hg hp i h hstable lH hlH hlHcomp
  letI : Mono t₀ := ht₀mono
  let n := S.finiteProjectiveStableImageInclusion i h
  let t := cokernelInclusionOfComp lH n
  let e := eqToIso (congrArg
    (fun q : _ ⟶ _ ↦ cokernel q) hlHcomp)
  have ht : t ≫ e.hom = t₀ := by
    apply (cancel_epi (cokernel.π lH)).1
    calc
      cokernel.π lH ≫ (t ≫ e.hom) =
          (n ≫ cokernel.π (lH ≫ n)) ≫ e.hom := by
        rw [← Category.assoc]
        dsimp only [t]
        rw [cokernel_π_comp_cokernelInclusionOfComp]
      _ = n ≫ cokernel.π
          (S.finiteProjectiveStableImageInclusion
            (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
            (S.irreducibleIntoProjective_selectedInitialStableMap
              u p g hg hp)) := by
        dsimp only [e, n]
        rw [Category.assoc, cokernel_π_comp_eqToIso_of_eq hlHcomp]
      _ = cokernel.π lH ≫ t₀ := ht₀.symm
  apply IsUniserialObject.isEssentialMono_of_comp_iso t e
  rw [ht]
  exact ht₀essential

/-- The distinguished first stable-socle generator carries the projective
irreducible arm killed in the stable quotient. -/
theorem irreducibleIntoProjective_selectedInitialStableMap_isStableChainGenerator
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    S.IsStableChainGenerator
      (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
      (S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp) := by
  refine ⟨p, S.irreducibleIntoProjective_initialProjectiveArm
    u p g hg hp,
    S.irreducibleIntoProjective_initialProjectiveArm_isIrreducible
      u p g hg hp, ?_⟩
  dsimp only [irreducibleIntoProjective_initialProjectiveArm]
  rw [S.finiteRestrictedContravariantRepresentableMap_comp,
    Category.assoc,
    S.irreducibleIntoProjective_selectedLeftCokernelMap_comp_selectedInitialStableNaturalMap_eq_zero,
    comp_zero]

/-- Once the quotient above the distinguished essential stable socle is
uniserial, the entire selected stable representable is uniserial.  This is
the categorical ascending-socle induction step specialized to the
Auslander--Reiten initialization. -/
theorem irreducibleIntoProjective_stableRepresentable_isUniserial_of_socleCokernel
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p))
    (hquotient : IsUniserialObject
      (cokernel
        (S.finiteProjectiveStableImageInclusion
          (S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp)
          (S.irreducibleIntoProjective_selectedInitialStableMap
            u p g hg hp)))) :
    IsUniserialObject
      (S.finiteProjectiveStableContravariantRepresentable
        (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))) := by
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let h₀ := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  let l := S.finiteProjectiveStableImageInclusion c h₀
  letI : Simple (S.finiteProjectiveStableImage c h₀) :=
    S.irreducibleIntoProjective_selectedInitialStableImage_simple
      u p g hg hp
  exact IsUniserialObject.of_essential_simple_cokernel l
    (S.irreducibleIntoProjective_selectedInitialStableImageInclusion_isEssential
      u p g hg hp)
    hquotient

/-- Under the two-arm bound, the stable representable attached to an
irreducible submodule of an indecomposable projective is uniserial. -/
theorem irreducibleIntoProjective_stableRepresentable_isUniserial
    (harity : ∀ (j : S.IndecCategory),
      ¬ Projective (S.fgObj j) →
        FiniteTauMatrix.rightMiddleArity
          S.finiteTauCategoryData.toFiniteRightTauCategoryData j ≤ 2)
    (u p : Fin S.n) (g : S.fgObj u ⟶ S.fgObj p)
    (hg : IsIrreducibleMorphism g) (hp : Projective (S.fgObj p)) :
    IsUniserialObject
      (S.finiteProjectiveStableContravariantRepresentable
        (S.fgObj (S.irreducibleIntoProjective_cokernelLabel p g hg hp))) := by
  let c := S.irreducibleIntoProjective_leftCokernelLabel u p g hg hp
  let h₀ := S.irreducibleIntoProjective_selectedInitialStableMap u p g hg hp
  let L := S.finiteProjectiveStableImage c h₀
  let l := S.finiteProjectiveStableImageInclusion c h₀
  letI : Simple L :=
    S.irreducibleIntoProjective_selectedInitialStableImage_simple
      u p g hg hp
  have hlEssential : IsEssentialMono l :=
    S.irreducibleIntoProjective_selectedInitialStableImageInclusion_isEssential
      u p g hg hp
  have hlWaist : IsUniserialObject.IsWaistSubobject (Subobject.mk l) :=
    IsUniserialObject.isWaistSubobject_of_simple_essential l hlEssential
  by_cases hquotient : IsZero (cokernel l)
  · have hπ : cokernel.π l = 0 := hquotient.eq_of_tgt _ _
    letI : Epi l := Abelian.epi_of_cokernel_π_eq_zero l hπ
    letI : IsIso l := isIso_of_mono_of_epi l
    exact (IsUniserialObject.of_simple L).congr (asIso l)
  · obtain ⟨i, h, lH, hstable, hlHmono, hlHcomp, hlHsimple,
        hlHEssential, hH, hnEssential⟩ :=
      S.irreducibleIntoProjective_exists_nextStableCyclicEssentialExtension
        u p g hg hp hquotient
    letI : Mono lH := hlHmono
    letI : Simple (cokernel lH) := hlHsimple
    let n := S.finiteProjectiveStableImageInclusion i h
    have htopEssential : IsEssentialMono
        (cokernelInclusionOfComp lH n) :=
      S.irreducibleIntoProjective_nextLayer_top_essential
        harity u p g hg hp i h hstable lH hlHEssential hlHcomp
    have hnWaist : IsUniserialObject.IsWaistSubobject
        (Subobject.mk n) := by
      apply IsUniserialObject.isWaistSubobject_of_essentialSimpleTop lH n
      · simpa only [n, hlHcomp] using hlWaist
      · exact htopEssential
    let Rad := imageSubobject
      (S.finiteRestrictedContravariantRepresentableRadicalInclusion i ≫
        S.finiteProjectiveStableImagePresentation i h)
    have hRadEq : Rad = Subobject.mk lH := by
      dsimp only [Rad]
      exact S.finiteProjectiveStableImageRadical_eq_of_uniserialSimpleCokernel
        i h hstable hH lH
    let eRad : (Rad : CoveringHom.FiniteDimensionalModuleCategory
        (C := S.IndecCategoryᵒᵖ) k) ≅ L :=
      eqToIso (congrArg
        (fun Q : Subobject (S.finiteProjectiveStableImage i h) ↦
          (Q : CoveringHom.FiniteDimensionalModuleCategory
            (C := S.IndecCategoryᵒᵖ) k)) hRadEq) ≪≫
        Subobject.underlyingIso lH
    have hRadNonzero : ¬ IsZero
        (Rad : CoveringHom.FiniteDimensionalModuleCategory
          (C := S.IndecCategoryᵒᵖ) k) := by
      intro hzeroRad
      exact Simple.not_isZero L (hzeroRad.of_iso eRad.symm)
    exact S.finiteProjectiveStableRepresentable_isUniserial_of_cyclicWaistStage
      harity i h hstable (by simpa only [Rad] using hRadNonzero)
      lH hH hnEssential hnWaist htopEssential

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
