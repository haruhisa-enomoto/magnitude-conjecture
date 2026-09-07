import MagnitudeConjecture.Algebra.RightModuleIdealQuotientCategory
import MagnitudeConjecture.CategoryTheory.AlmostSplitLocalFunctor
import MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitCofinite
import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# The maximal submodule annihilated by a two-sided ideal

For a two-sided ideal `I` and a finitely generated right `A`-module `M`, this
file constructs the largest submodule of `M` annihilated by `I`.  Bundled in
the annihilated full subcategory, this is the right adjoint needed to restrict
ambient right almost-split maps to `mod (A/I)`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- A finite biproduct of modules annihilated by `I` is again annihilated
by `I`. -/
theorem isAnnihilatedBy_biproduct (I : TwoSidedIdeal A)
    {J : Type} [Fintype J]
    (F : J → FinitelyGeneratedCategory A)
    (hF : ∀ j, IsAnnihilatedBy I (F j)) :
    IsAnnihilatedBy I (⨁ F) := by
  classical
  intro x a ha
  have htotal :
      (∑ j : J, (biproduct.π F j ≫ biproduct.ι F j).hom.hom x) = x := by
    have hsum :
        (∑ j : J, biproduct.π F j ≫ biproduct.ι F j).hom.hom =
          ∑ j : J, (biproduct.π F j ≫ biproduct.ι F j).hom.hom := by
      have h :
          (∑ j : J, biproduct.π F j ≫ biproduct.ι F j).hom =
            ∑ j : J, (biproduct.π F j ≫ biproduct.ι F j).hom :=
        map_sum
          (InducedCategory.homAddEquiv :
            ((⨁ F) ⟶ (⨁ F)) ≃+ ((⨁ F).obj ⟶ (⨁ F).obj))
          (fun j : J ↦ biproduct.π F j ≫ biproduct.ι F j)
          Finset.univ
      rw [h, ModuleCat.hom_sum]
    have h := congrArg
      (fun f : (⨁ F) ⟶ (⨁ F) ↦ f.hom.hom x)
      (biproduct.total :
        ∑ j : J, biproduct.π F j ≫ biproduct.ι F j = 𝟙 (⨁ F))
    rw [hsum] at h
    simpa only [LinearMap.sum_apply, FGModuleCat.hom_hom_comp,
      LinearMap.comp_apply, FGModuleCat.hom_hom_id,
      LinearMap.id_apply] using h
  rw [← htotal, Finset.smul_sum]
  apply Finset.sum_eq_zero
  intro j _hj
  change (MulOpposite.op a) •
      (biproduct.ι F j) ((biproduct.π F j) x) = 0
  rw [← map_smul, hF j ((biproduct.π F j) x) a ha, map_zero]

/-- The largest submodule of `M` annihilated by the two-sided ideal `I`. -/
def idealTorsionSubmodule (I : TwoSidedIdeal A)
    (M : FinitelyGeneratedCategory A) : Submodule Aᵐᵒᵖ M where
  carrier := {x | ∀ a : A, a ∈ I → (MulOpposite.op a) • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy a ha
    rw [smul_add, hx a ha, hy a ha, add_zero]
  smul_mem' := by
    intro r x hx a ha
    rw [← mul_smul]
    simpa using hx (r.unop * a) (I.mul_mem_left r.unop a ha)

/-- The maximal annihilated submodule as a finitely generated ambient right
module. -/
def idealTorsionFGObj (I : TwoSidedIdeal A)
    (M : FinitelyGeneratedCategory A) : FinitelyGeneratedCategory A :=
  FGModuleCat.of Aᵐᵒᵖ (idealTorsionSubmodule I M)

/-- The canonical inclusion of the maximal annihilated submodule. -/
def idealTorsionInclusion (I : TwoSidedIdeal A)
    (M : FinitelyGeneratedCategory A) :
    idealTorsionFGObj I M ⟶ M :=
  FGModuleCat.ofHom (idealTorsionSubmodule I M).subtype

instance idealTorsionInclusion_mono (I : TwoSidedIdeal A)
    (M : FinitelyGeneratedCategory A) :
    Mono (idealTorsionInclusion I M) := by
  apply (IndecomposableSkeleton.fg_mono_iff_injective _).2
  exact (idealTorsionSubmodule I M).subtype_injective

/-- The maximal torsion object is annihilated by `I`. -/
theorem idealTorsionFGObj_isAnnihilatedBy (I : TwoSidedIdeal A)
    (M : FinitelyGeneratedCategory A) :
    IsAnnihilatedBy I (idealTorsionFGObj I M) := by
  intro x a ha
  apply Subtype.ext
  exact x.property a ha

/-- The maximal torsion object bundled in the annihilated full
subcategory. -/
def idealTorsionSubcategoryObj (I : TwoSidedIdeal A)
    (M : FinitelyGeneratedCategory A) : IdealQuotientSubcategory I :=
  ⟨idealTorsionFGObj I M, idealTorsionFGObj_isAnnihilatedBy I M⟩

/-- An ambient morphism restricts to the maximal annihilated submodules. -/
def idealTorsionMap (I : TwoSidedIdeal A)
    {M N : FinitelyGeneratedCategory A} (f : M ⟶ N) :
    idealTorsionFGObj I M ⟶ idealTorsionFGObj I N :=
  FGModuleCat.ofHom {
    toFun := fun x ↦ ⟨f x, by
      intro a ha
      calc
        (MulOpposite.op a) • f x.1 =
            f ((MulOpposite.op a) • x.1) :=
          (f.hom.hom.map_smul (MulOpposite.op a) x.1).symm
        _ = f 0 := congrArg f.hom.hom (x.property a ha)
        _ = 0 := f.hom.hom.map_zero⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      exact f.hom.hom.map_add x y
    map_smul' := by
      intro a x
      apply Subtype.ext
      exact f.hom.hom.map_smul a x }

@[simp]
theorem idealTorsionMap_apply (I : TwoSidedIdeal A)
    {M N : FinitelyGeneratedCategory A} (f : M ⟶ N)
    (x : idealTorsionFGObj I M) :
    (idealTorsionMap I f x).1 = f x.1 := rfl

/-- Restriction commutes with the canonical inclusions. -/
theorem idealTorsionMap_comp_inclusion (I : TwoSidedIdeal A)
    {M N : FinitelyGeneratedCategory A} (f : M ⟶ N) :
    idealTorsionMap I f ≫ idealTorsionInclusion I N =
      idealTorsionInclusion I M ≫ f := by
  apply FGModuleCat.hom_ext
  ext x
  rfl

/-- The maximal-annihilated-submodule construction is functorial. -/
def idealTorsionFunctor (I : TwoSidedIdeal A) :
    FinitelyGeneratedCategory A ⥤ FinitelyGeneratedCategory A where
  obj M := idealTorsionFGObj I M
  map f := idealTorsionMap I f
  map_id M := by
    apply FGModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply FGModuleCat.hom_ext
    ext x
    rfl

instance idealTorsionFunctor_additive (I : TwoSidedIdeal A) :
    (idealTorsionFunctor I).Additive where
  map_add := by
    intro M N f g
    apply FGModuleCat.hom_ext
    ext x
    rfl

/-- Every map from an `I`-annihilated module factors canonically through the
maximal annihilated submodule of its target. -/
def idealTorsionLift (I : TwoSidedIdeal A)
    {X M : FinitelyGeneratedCategory A}
    (hX : IsAnnihilatedBy I X) (f : X ⟶ M) :
    X ⟶ idealTorsionFGObj I M :=
  FGModuleCat.ofHom {
    toFun := fun x ↦ ⟨f x, by
      intro a ha
      calc
        (MulOpposite.op a) • f x =
            f ((MulOpposite.op a) • x) :=
          (f.hom.hom.map_smul (MulOpposite.op a) x).symm
        _ = f 0 := congrArg f.hom.hom (hX x a ha)
        _ = 0 := f.hom.hom.map_zero⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      exact f.hom.hom.map_add x y
    map_smul' := by
      intro a x
      apply Subtype.ext
      exact f.hom.hom.map_smul a x }

@[simp]
theorem idealTorsionLift_comp_inclusion (I : TwoSidedIdeal A)
    {X M : FinitelyGeneratedCategory A}
    (hX : IsAnnihilatedBy I X) (f : X ⟶ M) :
    idealTorsionLift I hX f ≫ idealTorsionInclusion I M = f := by
  apply FGModuleCat.hom_ext
  ext x
  rfl

/-- On an annihilated module, the maximal torsion inclusion is an
isomorphism. -/
def idealTorsionIsoOfIsAnnihilated (I : TwoSidedIdeal A)
    (M : FinitelyGeneratedCategory A) (hM : IsAnnihilatedBy I M) :
    idealTorsionFGObj I M ≅ M where
  hom := idealTorsionInclusion I M
  inv := idealTorsionLift I hM (𝟙 M)
  hom_inv_id := by
    apply FGModuleCat.hom_ext
    ext x
    rfl
  inv_hom_id := idealTorsionLift_comp_inclusion I hM (𝟙 M)

/-- Restrict an ambient map to the maximal annihilated submodule of its
source when the target is annihilated by `I`. -/
def idealTorsionTargetMap (I : TwoSidedIdeal A)
    {E N : FinitelyGeneratedCategory A}
    (hN : IsAnnihilatedBy I N) (q : E ⟶ N) :
    idealTorsionSubcategoryObj I E ⟶ ⟨N, hN⟩ :=
  ObjectProperty.homMk (idealTorsionInclusion I E ≫ q)

/-- If the ambient kernel of a map to an annihilated target is itself
annihilated, then it is also the kernel after restricting the source to its
maximal annihilated submodule. -/
def idealTorsionTargetKernelIso (I : TwoSidedIdeal A)
    {E N : FinitelyGeneratedCategory A}
    (hN : IsAnnihilatedBy I N) (q : E ⟶ N)
    (hK : IsAnnihilatedBy I (kernel q)) :
    kernel (idealTorsionTargetMap I hN q) ≅
      (⟨kernel q, hK⟩ : IdealQuotientSubcategory I) := by
  let r := idealTorsionTargetMap I hN q
  let U := (IdealQuotientProperty I).ι
  let tι := idealTorsionInclusion I E
  let kι : kernel q ⟶ idealTorsionFGObj I E :=
    idealTorsionLift I hK (kernel.ι q)
  have hkι_tι : kι ≫ tι = kernel.ι q :=
    idealTorsionLift_comp_inclusion I hK (kernel.ι q)
  have hkι : kι ≫ U.map r = 0 := by
    change kι ≫ (tι ≫ q) = 0
    rw [← Category.assoc, idealTorsionLift_comp_inclusion,
      kernel.condition]
  haveI : Mono (kι ≫ tι) := by
    rw [hkι_tι]
    infer_instance
  letI : Mono kι := mono_of_mono kι tι
  let s : KernelFork (U.map r) :=
    KernelFork.ofι kι hkι
  let hs : IsLimit s := KernelFork.IsLimit.ofι' kι hkι fun a ha ↦ by
    have haq : (a ≫ tι) ≫ q = 0 := by
      change a ≫ (tι ≫ q) = 0 at ha
      simpa only [Category.assoc] using ha
    refine ⟨kernel.lift q (a ≫ tι) haq, ?_⟩
    apply (cancel_mono tι).1
    calc
      (kernel.lift q (a ≫ tι) haq ≫ kι) ≫ tι =
          kernel.lift q (a ≫ tι) haq ≫ kernel.ι q := by
            rw [Category.assoc, hkι_tι]
      _ = a ≫ tι := kernel.lift_ι _ _ _
  letI : PreservesLimit (parallelPair r 0) U :=
    (IdealQuotientProperty I).preservesKernels_ι r
  let ePreserved := PreservesKernel.iso U r
  let eAmbient : kernel (U.map r) ≅ kernel q :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel (U.map r)) hs
  exact ObjectProperty.isoMk _ (ePreserved.trans eAmbient)

/-- The right adjoint to the annihilated full-subcategory inclusion carries
an ambient right almost-split map to a right almost-split map. -/
theorem idealTorsionTargetMap_isRightAlmostSplit (I : TwoSidedIdeal A)
    {E N : FinitelyGeneratedCategory A}
    (hN : IsAnnihilatedBy I N) (q : E ⟶ N)
    (hq : IsRightAlmostSplit q) :
    IsRightAlmostSplit (idealTorsionTargetMap I hN q) := by
  constructor
  · intro hs
    apply hq.not_isSplitEpi
    obtain ⟨s⟩ := hs.exists_splitEpi
    exact IsSplitEpi.mk' {
      section_ := s.section_.hom ≫ idealTorsionInclusion I E
      id := by
        have hsId := congrArg (fun f ↦ f.hom) s.id
        change s.section_.hom ≫
          (idealTorsionInclusion I E ≫ q) = 𝟙 N at hsId
        simpa only [Category.assoc] using hsId }
  · intro X g hg
    have hgAmbient : ¬ IsSplitEpi g.hom := by
      intro hs
      apply hg
      obtain ⟨s⟩ := hs.exists_splitEpi
      exact IsSplitEpi.mk' {
        section_ := ObjectProperty.homMk s.section_
        id := by
          apply ObjectProperty.hom_ext
          exact s.id }
    obtain ⟨h, hh⟩ := hq.factors g.hom hgAmbient
    refine ⟨ObjectProperty.homMk (idealTorsionLift I X.property h), ?_⟩
    apply ObjectProperty.hom_ext
    change idealTorsionLift I X.property h ≫
      (idealTorsionInclusion I E ≫ q) = g.hom
    rw [← Category.assoc, idealTorsionLift_comp_inclusion]
    exact hh

/-- If the ambient source is already annihilated, restricting an ambient
right-minimal map preserves right minimality. -/
theorem idealTorsionTargetMap_isRightMinimal_of_source_isAnnihilatedBy
    (I : TwoSidedIdeal A) {E N : FinitelyGeneratedCategory A}
    (hE : IsAnnihilatedBy I E) (hN : IsAnnihilatedBy I N)
    (q : E ⟶ N) (hq : IsRightMinimal q) :
    IsRightMinimal (idealTorsionTargetMap I hN q) := by
  let U := (IdealQuotientProperty I).ι
  apply MagnitudeConjecture.rightMinimal_of_map_full_faithful U
  change IsRightMinimal (idealTorsionInclusion I E ≫ q)
  let e := idealTorsionIsoOfIsAnnihilated I E hE
  letI : IsIso (idealTorsionInclusion I E) := e.isIso_hom
  exact hq.precomp_splitMono _

include k in
/-- A displayed decomposition of a maximal annihilated source transports to
the corresponding object over the literal quotient algebra. -/
def idealTorsionSourceDecomposition
    (I : TwoSidedIdeal A)
    [IsNoetherianRing (idealQuotientAlgebra I)ᵐᵒᵖ]
    (E : FinitelyGeneratedCategory A)
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      (idealTorsionFGObj I E))
    (hsummand : ∀ i, IsAnnihilatedBy I (d.summand i)) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      ((idealQuotientEquivalence (k := k) I).functor.obj
        (idealTorsionSubcategoryObj I E)) := by
  let C := IdealQuotientSubcategory I
  let Eq := idealQuotientEquivalence (k := k) I
  let U := (IdealQuotientProperty I).ι
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      Eq.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence Eq.functor
  let summandSub : Fin d.n → C := fun i ↦
    ⟨d.summand i, hsummand i⟩
  let decompositionSub :
      idealTorsionSubcategoryObj I E ≅ ⨁ summandSub :=
    ObjectProperty.isoMk _
      (d.isoBiproduct.trans (U.mapBiproduct summandSub).symm)
  have hsub (i : Fin d.n) : Indecomposable (summandSub i) :=
    MagnitudeConjecture.CategoryTheory.indecomposable_of_fully_faithful_additive
      U (summandSub i) (d.indecomposable i)
  exact {
    n := d.n
    summand := fun i ↦ Eq.functor.obj (summandSub i)
    indecomposable := fun i ↦
      (MagnitudeConjecture.CategoryTheory.indecomposable_map_iff_of_equivalence
        Eq.functor (summandSub i)).2 (hsub i)
    isoBiproduct :=
      Eq.functor.mapIso decompositionSub ≪≫
        Eq.functor.mapBiproduct summandSub }

include k in
/-- An explicit ambient decomposition whose summands are annihilated by
`I` transports to a decomposition of the right-adjoint sink source over
the literal quotient algebra, with the same number of summands. -/
def idealTorsionTargetSourceDecomposition
    (I : TwoSidedIdeal A)
    [IsNoetherianRing (idealQuotientAlgebra I)ᵐᵒᵖ]
    (E : FinitelyGeneratedCategory A)
    (hE : IsAnnihilatedBy I E)
    (d : MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition E)
    (hsummand : ∀ i, IsAnnihilatedBy I (d.summand i)) :
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition
      ((idealQuotientEquivalence (k := k) I).functor.obj
        (idealTorsionSubcategoryObj I E)) := by
  let dT :=
    MagnitudeConjecture.CategoryTheory.FiniteIndecomposableDecomposition.ofIso
      (idealTorsionIsoOfIsAnnihilated I E hE) d
  exact idealTorsionSourceDecomposition (k := k) I E dT hsummand

include k in
/-- The full subcategory annihilated by an arbitrary ideal has enough
projectives, transported from finitely generated modules over the literal
quotient algebra. -/
theorem idealQuotientSubcategory_enoughProjectives (I : TwoSidedIdeal A) :
    EnoughProjectives (IdealQuotientSubcategory I) := by
  exact (idealQuotientEquivalence (k := k) I).enoughProjectives_iff.mpr
    (MagnitudeConjecture.fgModuleCat_enoughProjectives
      (idealQuotientAlgebra I)ᵐᵒᵖ)

/-- A projective ambient module which is annihilated by `I` remains
projective in the full annihilated subcategory. -/
theorem idealQuotientSubcategory_projective_of_ambient
    (I : TwoSidedIdeal A) (M : IdealQuotientSubcategory I)
    (hM : Projective M.1) : Projective M := by
  letI : Projective M.1 := hM
  constructor
  intro E X f e _
  letI : Epi e.hom := idealQuotientSubcategory_epi_ambient I e
  obtain ⟨g, hg⟩ := Projective.factors f.hom e.hom
  refine ⟨ObjectProperty.homMk g, ?_⟩
  apply ObjectProperty.hom_ext
  exact hg

include k in
/-- Transporting an annihilated ambient projective through the literal
ideal-quotient equivalence produces a projective quotient module. -/
theorem idealQuotientFGObj_projective_of_ambient
    (I : TwoSidedIdeal A) [IsNoetherianRing (idealQuotientAlgebra I)ᵐᵒᵖ]
    (M : FinitelyGeneratedCategory A) (hAnn : IsAnnihilatedBy I M)
    (hM : Projective M) :
    Projective ((idealQuotientEquivalence (k := k) I).functor.obj
      (⟨M, hAnn⟩ : IdealQuotientSubcategory I)) :=
  (idealQuotientEquivalence (k := k) I).map_projective_iff
    (⟨M, hAnn⟩ : IdealQuotientSubcategory I) |>.2
      (idealQuotientSubcategory_projective_of_ambient I ⟨M, hAnn⟩ hM)

/-- An injective ambient module which is annihilated by `I` remains
injective in the full annihilated subcategory. -/
theorem idealQuotientSubcategory_injective_of_ambient
    (I : TwoSidedIdeal A) (M : IdealQuotientSubcategory I)
    (hM : Injective M.1) : Injective M := by
  let Q := IdealQuotientProperty I
  let U := Q.ι
  letI : Q.Nonempty := ObjectProperty.nonempty_of_prop M.property
  letI : U.PreservesMonomorphisms :=
    Q.preservesMonomorphisms_ι_of_isNormalEpiCategory
  letI : Injective M.1 := hM
  constructor
  intro X Y g f _
  letI : Mono (U.map f) := U.map_mono f
  letI : Mono f.hom := by
    change Mono (U.map f)
    infer_instance
  obtain ⟨h, hh⟩ := Injective.factors g.hom f.hom
  refine ⟨ObjectProperty.homMk h, ?_⟩
  apply ObjectProperty.hom_ext
  exact hh

include k in
/-- Transporting an annihilated ambient injective through the literal
ideal-quotient equivalence produces an injective quotient module. -/
theorem idealQuotientFGObj_injective_of_ambient
    (I : TwoSidedIdeal A) [IsNoetherianRing (idealQuotientAlgebra I)ᵐᵒᵖ]
    (M : FinitelyGeneratedCategory A) (hAnn : IsAnnihilatedBy I M)
    (hM : Injective M) :
    Injective ((idealQuotientEquivalence (k := k) I).functor.obj
      (⟨M, hAnn⟩ : IdealQuotientSubcategory I)) :=
  (idealQuotientEquivalence (k := k) I).map_injective_iff
    (⟨M, hAnn⟩ : IdealQuotientSubcategory I) |>.2
      (idealQuotientSubcategory_injective_of_ambient I ⟨M, hAnn⟩ hM)

/-- If the ambient source is already annihilated, the restricted sink map
is monic exactly when the ambient sink map is monic. -/
theorem idealTorsionTargetMap_mono_iff_of_source_isAnnihilatedBy
    (I : TwoSidedIdeal A) {E N : FinitelyGeneratedCategory A}
    (hE : IsAnnihilatedBy I E) (hN : IsAnnihilatedBy I N)
    (q : E ⟶ N) :
    Mono (idealTorsionTargetMap I hN q) ↔ Mono q := by
  let Q := IdealQuotientProperty I
  let U := Q.ι
  let e := idealTorsionIsoOfIsAnnihilated I E hE
  letI : IsIso (idealTorsionInclusion I E) := e.isIso_hom
  letI : Q.Nonempty :=
    ObjectProperty.nonempty_of_prop hE
  letI : U.PreservesMonomorphisms :=
    Q.preservesMonomorphisms_ι_of_isNormalEpiCategory
  constructor
  · intro hrestricted
    letI : Mono (idealTorsionTargetMap I hN q) := hrestricted
    have hambient : Mono (U.map (idealTorsionTargetMap I hN q)) :=
      U.map_mono _
    change Mono (idealTorsionInclusion I E ≫ q) at hambient
    exact (mono_comp_iff_of_isIso (idealTorsionInclusion I E) q).mp
      hambient
  · intro hambient
    letI : Mono q := hambient
    apply U.mono_of_mono_map
    change Mono (idealTorsionInclusion I E ≫ q)
    infer_instance

include k in
/-- When a minimal ambient sink has annihilated source and target, passing
to the ideal quotient preserves and reflects projectivity of its target. -/
theorem idealQuotient_projective_iff_of_minimal_sink_source_isAnnihilatedBy
    (I : TwoSidedIdeal A) {E N : FinitelyGeneratedCategory A}
    (hE : IsAnnihilatedBy I E) (hN : IsAnnihilatedBy I N)
    (q : E ⟶ N) (hq : IsRightAlmostSplit q)
    (hqmin : IsRightMinimal q) :
    Projective (⟨N, hN⟩ : IdealQuotientSubcategory I) ↔ Projective N := by
  let C := IdealQuotientSubcategory I
  let Eq := idealQuotientEquivalence (k := k) I
  letI : IsNoetherianRing (idealQuotientAlgebra I)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      Eq.functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence Eq.functor
  let restricted := idealTorsionTargetMap I hN q
  have hrestricted : IsRightAlmostSplit restricted :=
    idealTorsionTargetMap_isRightAlmostSplit I hN q hq
  have hrestrictedMin : IsRightMinimal restricted :=
    idealTorsionTargetMap_isRightMinimal_of_source_isAnnihilatedBy
      I hE hN q hqmin
  have hmono : Mono restricted ↔ Mono q :=
    idealTorsionTargetMap_mono_iff_of_source_isAnnihilatedBy
      I hE hN q
  letI : EnoughProjectives (FinitelyGeneratedCategory A) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : EnoughProjectives C :=
    idealQuotientSubcategory_enoughProjectives (k := k) I
  constructor
  · intro hprojective
    letI : Projective (⟨N, hN⟩ : C) := hprojective
    have hrestrictedMono : Mono restricted :=
      MagnitudeConjecture.CategoryTheory.rightAlmostSplit_mono_of_projective_target
        restricted hrestricted hrestrictedMin
    letI : Mono q := hmono.mp hrestrictedMono
    exact MagnitudeConjecture.CategoryTheory.projective_of_mono_rightAlmostSplit
      q hq
  · intro hprojective
    letI : Projective N := hprojective
    have hqMono : Mono q :=
      MagnitudeConjecture.CategoryTheory.rightAlmostSplit_mono_of_projective_target
        q hq hqmin
    letI : Mono restricted := hmono.mpr hqMono
    exact MagnitudeConjecture.CategoryTheory.projective_of_mono_rightAlmostSplit
      restricted hrestricted

end MagnitudeConjecture.RightModule
