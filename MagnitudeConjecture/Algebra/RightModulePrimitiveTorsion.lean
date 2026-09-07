import MagnitudeConjecture.Algebra.IdempotentSaturation
import MagnitudeConjecture.Algebra.RightModuleLeftAlmostSplit
import MagnitudeConjecture.Algebra.RightModulePrimitiveQuotientCategory
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitCofinite

/-!
# The primitive torsion radical

For a primitive idempotent `e`, the Hoshino torsion radical sends a right
`A`-module `M` to its largest submodule annihilated by `AeA`.  In the
right-module convention this is the idempotent-torsion submodule for
`MulOpposite.op e` in the left `Aᵐᵒᵖ`-module `M`.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- The largest ambient submodule annihilated by the primitive quotient
ideal `AeA`. -/
abbrev primitiveTorsionSubmodule (e : A)
    (M : FinitelyGeneratedCategory A) : Submodule Aᵐᵒᵖ M :=
  IdempotentSaturation.torsionSubmodule (MulOpposite.op e)

/-- The primitive torsion radical as a finitely generated ambient right
module. -/
def primitiveTorsionFGObj (e : A) (M : FinitelyGeneratedCategory A) :
    FinitelyGeneratedCategory A :=
  FGModuleCat.of Aᵐᵒᵖ (primitiveTorsionSubmodule e M)

/-- The canonical inclusion of the primitive torsion radical. -/
def primitiveTorsionInclusion (e : A) (M : FinitelyGeneratedCategory A) :
    primitiveTorsionFGObj e M ⟶ M :=
  FGModuleCat.ofHom (primitiveTorsionSubmodule e M).subtype

/-- The quotient of a module by its maximal `AeA`-annihilated submodule. -/
def primitiveTorsionQuotientFGObj (e : A)
    (M : FinitelyGeneratedCategory A) : FinitelyGeneratedCategory A :=
  FGModuleCat.of Aᵐᵒᵖ (M ⧸ primitiveTorsionSubmodule e M)

/-- The canonical projection onto the primitive torsion-free quotient. -/
def primitiveTorsionQuotientMk (e : A)
    (M : FinitelyGeneratedCategory A) :
    M ⟶ primitiveTorsionQuotientFGObj e M :=
  FGModuleCat.ofHom (primitiveTorsionSubmodule e M).mkQ

theorem primitiveTorsionInclusion_comp_quotientMk (e : A)
    (M : FinitelyGeneratedCategory A) :
    primitiveTorsionInclusion e M ≫ primitiveTorsionQuotientMk e M = 0 := by
  apply FGModuleCat.hom_ext
  ext x
  change Submodule.Quotient.mk x.1 = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact x.2

/-- The torsion radical, ambient module, and torsion-free quotient form the
canonical short exact sequence. -/
theorem primitiveTorsionQuotient_shortExact (e : A)
    (M : FinitelyGeneratedCategory A) :
    (ShortComplex.mk (primitiveTorsionInclusion e M).hom
      (primitiveTorsionQuotientMk e M).hom
      (congrArg (fun f ↦ f.hom)
        (primitiveTorsionInclusion_comp_quotientMk e M))).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · rw [LinearMap.exact_iff]
    change LinearMap.ker (primitiveTorsionSubmodule e M).mkQ =
      LinearMap.range (primitiveTorsionSubmodule e M).subtype
    rw [Submodule.ker_mkQ, Submodule.range_subtype]
  · intro x y hxy
    exact Subtype.ext hxy
  · exact (primitiveTorsionSubmodule e M).mkQ_surjective

/-- The same canonical torsion sequence, retained inside the finitely
generated module category. -/
theorem primitiveTorsionQuotient_fg_shortExact (e : A)
    (M : FinitelyGeneratedCategory A) :
    (ShortComplex.mk (primitiveTorsionInclusion e M)
      (primitiveTorsionQuotientMk e M)
      (primitiveTorsionInclusion_comp_quotientMk e M)).ShortExact := by
  apply ShortExact.reflects_shortExact_of_faithful
    (forget₂ (FinitelyGeneratedCategory A) (RightModule.Category A))
  convert primitiveTorsionQuotient_shortExact e M using 1
  all_goals rfl

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- Quotienting by the primitive torsion radical leaves no nonzero primitive
torsion. -/
theorem primitiveTorsionQuotient_torsionSubmodule_eq_bot
    {e : A} (he : IsIdempotentElem e)
    (M : FinitelyGeneratedCategory A) :
    primitiveTorsionSubmodule e (primitiveTorsionQuotientFGObj e M) = ⊥ := by
  have heop : IsIdempotentElem (MulOpposite.op e) := by
    apply MulOpposite.unop_injective
    exact he.eq
  have hsat : IdempotentSaturation.saturation (MulOpposite.op e)
      (⊥ : Submodule Aᵐᵒᵖ M) = primitiveTorsionSubmodule e M := by
    ext x
    rw [IdempotentSaturation.mem_saturation_iff,
      IdempotentSaturation.mem_torsionSubmodule_iff]
    constructor
    · intro hx r
      have hr : (⊥ : Submodule Aᵐᵒᵖ M).mkQ
          ((MulOpposite.op e * r) • x) = 0 := by
        simpa only [map_smul] using hx r
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_bot] at hr
      exact hr
    · intro hx r
      change (⊥ : Submodule Aᵐᵒᵖ M).mkQ
        ((MulOpposite.op e * r) • x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_bot]
      exact hx r
  change IdempotentSaturation.torsionSubmodule
    (M := M ⧸ primitiveTorsionSubmodule e M) (MulOpposite.op e) = ⊥
  rw [← hsat]
  exact IdempotentSaturation.torsionSubmodule_quotient_saturation_eq_bot
    (M := M) heop (⊥ : Submodule Aᵐᵒᵖ M)

/-- The torsion radical is annihilated by `AeA`, hence is an object of the
primitive quotient subcategory. -/
theorem primitiveTorsionFGObj_isAnnihilatedBy (e : A)
    (M : FinitelyGeneratedCategory A) :
    IsAnnihilatedBy (primitiveIdeal e) (primitiveTorsionFGObj e M) := by
  rw [isAnnihilatedBy_primitiveIdeal_iff]
  intro x
  apply Subtype.ext
  exact IdempotentSaturation.smul_eq_zero_of_mem_torsionSubmodule
    (MulOpposite.op e) x.property

/-- The torsion radical bundled in the full primitive-quotient
subcategory. -/
def primitiveTorsionSubcategoryObj (e : A)
    (M : FinitelyGeneratedCategory A) : PrimitiveQuotientSubcategory e :=
  ⟨primitiveTorsionFGObj e M,
    primitiveTorsionFGObj_isAnnihilatedBy e M⟩

/-- A morphism of ambient modules restricts to their primitive torsion
radicals. -/
def primitiveTorsionMap (e : A) {M N : FinitelyGeneratedCategory A}
    (f : M ⟶ N) : primitiveTorsionFGObj e M ⟶ primitiveTorsionFGObj e N :=
  FGModuleCat.ofHom {
    toFun := fun x ↦ ⟨f x, by
      intro r
      calc
        (MulOpposite.op e * r) • f x.1 =
            f ((MulOpposite.op e * r) • x.1) :=
          (f.hom.hom.map_smul (MulOpposite.op e * r) x.1).symm
        _ = f 0 := congrArg f.hom.hom (x.property r)
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
theorem primitiveTorsionMap_apply (e : A)
    {M N : FinitelyGeneratedCategory A} (f : M ⟶ N)
    (x : primitiveTorsionFGObj e M) :
    (primitiveTorsionMap e f x).1 = f x.1 := rfl

/-- Restriction to the primitive torsion radical commutes with the canonical
inclusions into the ambient modules. -/
theorem primitiveTorsionMap_comp_inclusion (e : A)
    {M N : FinitelyGeneratedCategory A} (f : M ⟶ N) :
    primitiveTorsionMap e f ≫ primitiveTorsionInclusion e N =
      primitiveTorsionInclusion e M ≫ f := by
  apply FGModuleCat.hom_ext
  ext x
  rfl

/-- The primitive torsion radical is functorial on finitely generated
ambient modules. -/
def primitiveTorsionFunctor (e : A) :
    FinitelyGeneratedCategory A ⥤ FinitelyGeneratedCategory A where
  obj M := primitiveTorsionFGObj e M
  map f := primitiveTorsionMap e f
  map_id M := by
    apply FGModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply FGModuleCat.hom_ext
    ext x
    rfl

/-- The primitive torsion radical is additive on morphisms. -/
instance primitiveTorsionFunctor_additive (e : A) :
    (primitiveTorsionFunctor e).Additive where
  map_add := by
    intro M N f g
    apply FGModuleCat.hom_ext
    ext x
    rfl

instance primitiveTorsionFunctor_preservesBinaryBiproducts (e : A) :
    Limits.PreservesBinaryBiproducts (primitiveTorsionFunctor e) :=
  Limits.preservesBinaryBiproducts_of_preservesBiproducts
    (primitiveTorsionFunctor e)

/-- Primitive torsion carries a binary biproduct to the biproduct of the
primitive torsion radicals. -/
abbrev primitiveTorsionBiprodIso (e : A)
    (M N : FinitelyGeneratedCategory A) :=
  (primitiveTorsionFunctor e).mapBiprod M N

/-- The torsion inclusions form a natural transformation to the identity
functor. -/
def primitiveTorsionInclusionNatTrans (e : A) :
    primitiveTorsionFunctor e ⟶ 𝟭 (FinitelyGeneratedCategory A) where
  app M := primitiveTorsionInclusion e M
  naturality := by
    intro M N f
    apply FGModuleCat.hom_ext
    ext x
    rfl

/-- Any map from an `AeA`-annihilated module factors canonically through
the primitive torsion radical. -/
def primitiveTorsionLift (e : A)
    {X M : FinitelyGeneratedCategory A}
    (hX : IsAnnihilatedBy (primitiveIdeal e) X) (f : X ⟶ M) :
    X ⟶ primitiveTorsionFGObj e M := by
  have he : ∀ x : X, (MulOpposite.op e) • x = 0 :=
    (isAnnihilatedBy_primitiveIdeal_iff e X).1 hX
  exact FGModuleCat.ofHom {
    toFun := fun x ↦ ⟨f x, by
      intro r
      calc
        (MulOpposite.op e * r) • f x =
            f ((MulOpposite.op e * r) • x) :=
          (f.hom.hom.map_smul (MulOpposite.op e * r) x).symm
        _ = f (MulOpposite.op e • r • x) := by rw [mul_smul]
        _ = f 0 := congrArg f.hom.hom (he (r • x))
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
theorem primitiveTorsionLift_comp_inclusion (e : A)
    {X M : FinitelyGeneratedCategory A}
    (hX : IsAnnihilatedBy (primitiveIdeal e) X) (f : X ⟶ M) :
    primitiveTorsionLift e hX f ≫ primitiveTorsionInclusion e M = f := by
  apply FGModuleCat.hom_ext
  ext x
  rfl

/-- Every morphism from an `AeA`-annihilated module to the torsion-free
quotient is zero. -/
theorem hom_to_primitiveTorsionQuotient_eq_zero
    {e : A} (he : IsIdempotentElem e)
    {X M : FinitelyGeneratedCategory A}
    (hX : IsAnnihilatedBy (primitiveIdeal e) X)
    (f : X ⟶ primitiveTorsionQuotientFGObj e M) :
    f = 0 := by
  apply FGModuleCat.hom_ext
  ext x
  have hx : f x ∈ primitiveTorsionSubmodule e
      (primitiveTorsionQuotientFGObj e M) :=
    (primitiveTorsionLift e hX f x).property
  rw [primitiveTorsionQuotient_torsionSubmodule_eq_bot he M,
    Submodule.mem_bot] at hx
  exact hx

/-- On an `AeA`-annihilated module the torsion inclusion is an
isomorphism. -/
def primitiveTorsionIsoOfIsAnnihilated (e : A)
    (M : FinitelyGeneratedCategory A)
    (hM : IsAnnihilatedBy (primitiveIdeal e) M) :
    primitiveTorsionFGObj e M ≅ M where
  hom := primitiveTorsionInclusion e M
  inv := primitiveTorsionLift e hM (𝟙 M)
  hom_inv_id := by
    apply FGModuleCat.hom_ext
    ext x
    rfl
  inv_hom_id := primitiveTorsionLift_comp_inclusion e hM (𝟙 M)

/-- Restrict an ambient map to the primitive torsion radical of its source,
when its target is already annihilated by `AeA`. -/
def primitiveTorsionTargetMap (e : A)
    {E N : FinitelyGeneratedCategory A}
    (hN : IsAnnihilatedBy (primitiveIdeal e) N) (q : E ⟶ N) :
    primitiveTorsionSubcategoryObj e E ⟶
      ⟨N, hN⟩ :=
  ObjectProperty.homMk (primitiveTorsionInclusion e E ≫ q)

/-- Hoshino's factorization step: applying the primitive torsion radical to
an ambient right almost-split map gives a right almost-split map in the full
primitive-quotient subcategory. -/
theorem primitiveTorsionTargetMap_isRightAlmostSplit (e : A)
    {E N : FinitelyGeneratedCategory A}
    (hN : IsAnnihilatedBy (primitiveIdeal e) N) (q : E ⟶ N)
    (hq : IsRightAlmostSplit q) :
    IsRightAlmostSplit (primitiveTorsionTargetMap e hN q) := by
  constructor
  · intro hs
    apply hq.not_isSplitEpi
    obtain ⟨s⟩ := hs.exists_splitEpi
    exact IsSplitEpi.mk' {
      section_ := s.section_.hom ≫ primitiveTorsionInclusion e E
      id := by
        have hsId := congrArg (fun f ↦ f.hom) s.id
        change s.section_.hom ≫
          (primitiveTorsionInclusion e E ≫ q) = 𝟙 N at hsId
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
    refine ⟨ObjectProperty.homMk
      (primitiveTorsionLift e X.property h), ?_⟩
    apply ObjectProperty.hom_ext
    change primitiveTorsionLift e X.property h ≫
      (primitiveTorsionInclusion e E ≫ q) = g.hom
    rw [← Category.assoc, primitiveTorsionLift_comp_inclusion]
    exact hh

include k in
/-- The primitive-quotient full subcategory has enough projectives, by
transport from the literal module category of `A/AeA`. -/
theorem primitiveQuotientSubcategory_enoughProjectives (e : A) :
    EnoughProjectives (PrimitiveQuotientSubcategory e) := by
  apply (primitiveQuotientEquivalence (k := k) e).enoughProjectives_iff.mpr
  exact fgModuleCat_enoughProjectives
    (primitiveQuotientAlgebra e)ᵐᵒᵖ

include k in
/-- The restricted right almost-split map is epic when its target is
nonprojective in the primitive-quotient category. -/
theorem primitiveTorsionTargetMap_epi_of_not_projective (e : A)
    {E N : FinitelyGeneratedCategory A}
    (hN : IsAnnihilatedBy (primitiveIdeal e) N) (q : E ⟶ N)
    (hq : IsRightAlmostSplit q)
    (hNprojective :
      ¬ Projective (⟨N, hN⟩ : PrimitiveQuotientSubcategory e)) :
    Epi (primitiveTorsionTargetMap e hN q) := by
  letI : EnoughProjectives (PrimitiveQuotientSubcategory e) :=
    primitiveQuotientSubcategory_enoughProjectives (k := k) e
  let P := (EnoughProjectives.presentation
    (⟨N, hN⟩ : PrimitiveQuotientSubcategory e)).some
  have hPnot : ¬ IsSplitEpi P.f := by
    intro hsplit
    obtain ⟨s⟩ := hsplit.exists_splitEpi
    apply hNprojective
    letI : Projective P.p := P.projective
    exact (show Retract (⟨N, hN⟩ : PrimitiveQuotientSubcategory e) P.p from
      { i := s.section_
        r := P.f
        retract := s.id }).projective
  exact (primitiveTorsionTargetMap_isRightAlmostSplit e hN q hq).epi_of_nonsplit_epi
    P.f hPnot

/-- The underlying ambient map of `primitiveTorsionTargetMap`. -/
abbrev primitiveTorsionAmbientTargetMap (e : A)
    {E N : FinitelyGeneratedCategory A} (q : E ⟶ N) :
    primitiveTorsionFGObj e E ⟶ N :=
  primitiveTorsionInclusion e E ≫ q

include k in
/-- Quotient nonprojectivity makes the restricted target map surjective on
the underlying ambient modules. -/
theorem primitiveTorsionAmbientTargetMap_surjective_of_not_projective
    (e : A) {E N : FinitelyGeneratedCategory A}
    (hN : IsAnnihilatedBy (primitiveIdeal e) N) (q : E ⟶ N)
    (hq : IsRightAlmostSplit q)
    (hNprojective :
      ¬ Projective (⟨N, hN⟩ : PrimitiveQuotientSubcategory e)) :
    Function.Surjective (primitiveTorsionAmbientTargetMap e q) := by
  letI : Epi (primitiveTorsionTargetMap e hN q) :=
    primitiveTorsionTargetMap_epi_of_not_projective (k := k)
      e hN q hq hNprojective
  letI : Epi (primitiveTorsionTargetMap e hN q).hom :=
    primitiveQuotientSubcategory_epi_ambient e
      (primitiveTorsionTargetMap e hN q)
  exact
    (QuotientSubmoduleEquidistribution.IndecomposableSkeleton.fg_epi_iff_surjective
      (primitiveTorsionTargetMap e hN q).hom).1 inferInstance

/-- The primitive torsion radical is left exact on an ambient exact pair.
This is the kernel part of Hoshino's comparison and uses only the maximal
annihilated-submodule construction. -/
theorem primitiveTorsion_functionExact (e : A)
    {Q E N : FinitelyGeneratedCategory A}
    (i : Q ⟶ E) (q : E ⟶ N)
    (hi : Function.Injective i)
    (hexact : Function.Exact i q) :
    Function.Exact (primitiveTorsionMap e i)
      (primitiveTorsionAmbientTargetMap e q) := by
  rw [LinearMap.exact_iff] at hexact ⊢
  apply le_antisymm
  · intro x hx
    let xT : primitiveTorsionSubmodule e E := x
    have hxKer : xT.1 ∈ LinearMap.ker q.hom.hom := by
      exact hx
    have hxRange : xT.1 ∈ LinearMap.range i.hom.hom :=
      hexact ▸ hxKer
    obtain ⟨y, hy⟩ := hxRange
    let yT : primitiveTorsionFGObj e Q := ⟨y, by
      intro r
      apply hi
      calc
        i ((MulOpposite.op e * r) • y) =
            (MulOpposite.op e * r) • i y :=
          i.hom.hom.map_smul (MulOpposite.op e * r) y
        _ = (MulOpposite.op e * r) • xT.1 :=
          congrArg (fun z ↦ (MulOpposite.op e * r) • z) hy
        _ = 0 := xT.property r
        _ = i 0 := (i.hom.hom.map_zero).symm⟩
    refine ⟨yT, ?_⟩
    apply Subtype.ext
    exact hy
  · rintro x ⟨y, hy⟩
    rw [LinearMap.mem_ker]
    have hyRange : i y.1 ∈ LinearMap.range i.hom.hom :=
      ⟨y.1, rfl⟩
    have hyKer : i y.1 ∈ LinearMap.ker q.hom.hom :=
      hexact.symm ▸ hyRange
    calc
      q x.1 = q (i y.1) := by
        rw [← hy]
        rfl
      _ = 0 := hyKer

include k in
/-- In Hoshino's situation the torsion part of the ambient kernel is
nonzero.  Once quotient nonprojectivity makes the restricted right
almost-split map epic, a zero torsion kernel would make that map an
isomorphism, contradicting right almost-splitness. -/
theorem primitiveTorsionFGObj_nontrivial_of_not_projective (e : A)
    {Q E N : FinitelyGeneratedCategory A}
    (hN : IsAnnihilatedBy (primitiveIdeal e) N)
    (i : Q ⟶ E) (q : E ⟶ N)
    (hi : Function.Injective i)
    (hexact : Function.Exact i q)
    (hq : IsRightAlmostSplit q)
    (hNprojective :
      ¬ Projective (⟨N, hN⟩ : PrimitiveQuotientSubcategory e)) :
    Nontrivial (primitiveTorsionFGObj e Q) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  have hsurj : Function.Surjective
      (primitiveTorsionAmbientTargetMap e q) :=
    primitiveTorsionAmbientTargetMap_surjective_of_not_projective
      (k := k) e hN q hq hNprojective
  have hrestrictedExact := primitiveTorsion_functionExact e i q hi hexact
  rw [LinearMap.exact_iff] at hrestrictedExact
  have hinj : Function.Injective
      (primitiveTorsionAmbientTargetMap e q) := by
    intro x y hxy
    have hker : x - y ∈ LinearMap.ker
        (primitiveTorsionAmbientTargetMap e q).hom.hom := by
      rw [LinearMap.mem_ker]
      rw [map_sub, sub_eq_zero]
      exact hxy
    have hrange : x - y ∈ LinearMap.range
        (primitiveTorsionMap e i).hom.hom :=
      hrestrictedExact ▸ hker
    obtain ⟨z, hz⟩ := hrange
    have hz0 : z = 0 := Subsingleton.elim z 0
    apply sub_eq_zero.mp
    calc
      x - y = (primitiveTorsionMap e i) z := hz.symm
      _ = (primitiveTorsionMap e i) 0 := by rw [hz0]
      _ = 0 := (primitiveTorsionMap e i).hom.hom.map_zero
  let f := primitiveTorsionAmbientTargetMap e q
  let U := forget₂ (FinitelyGeneratedCategory A) (RightModule.Category A)
  haveI : IsIso (U.map f) := by
    change IsIso f.hom
    exact (ConcreteCategory.isIso_iff_bijective f.hom).2 ⟨hinj, hsurj⟩
  haveI : IsIso f := isIso_of_reflects_iso f U
  haveI : IsIso (primitiveTorsionTargetMap e hN q).hom := by
    change IsIso f
    infer_instance
  haveI : IsIso (primitiveTorsionTargetMap e hN q) :=
    (ObjectProperty.isIso_hom_iff
      (primitiveTorsionTargetMap e hN q)).mp inferInstance
  exact (primitiveTorsionTargetMap_isRightAlmostSplit e hN q hq).not_isSplitEpi
    inferInstance

theorem primitiveTorsion_comp_eq_zero (e : A)
    {Q E N : FinitelyGeneratedCategory A}
    (i : Q ⟶ E) (q : E ⟶ N)
    (hi : Function.Injective i)
    (hexact : Function.Exact i q) :
    primitiveTorsionMap e i ≫ primitiveTorsionAmbientTargetMap e q = 0 := by
  apply FGModuleCat.hom_ext
  ext x
  exact Function.Exact.apply_apply_eq_zero
    (primitiveTorsion_functionExact e i q hi hexact) x

theorem primitiveTorsion_comp_eq_zero_hom (e : A)
    {Q E N : FinitelyGeneratedCategory A}
    (i : Q ⟶ E) (q : E ⟶ N)
    (hi : Function.Injective i)
    (hexact : Function.Exact i q) :
    (primitiveTorsionMap e i).hom ≫
      (primitiveTorsionAmbientTargetMap e q).hom = 0 := by
  exact congrArg (fun f ↦ f.hom)
    (primitiveTorsion_comp_eq_zero e i q hi hexact)

/-- If the torsion-restricted target map is surjective, the left-exact
torsion pair is a short exact sequence of ambient modules. -/
theorem primitiveTorsion_shortExact (e : A)
    {Q E N : FinitelyGeneratedCategory A}
    (i : Q ⟶ E) (q : E ⟶ N)
    (hi : Function.Injective i)
    (hexact : Function.Exact i q)
    (hsurj : Function.Surjective (primitiveTorsionAmbientTargetMap e q)) :
    (ShortComplex.mk (primitiveTorsionMap e i).hom
      (primitiveTorsionAmbientTargetMap e q).hom
      (primitiveTorsion_comp_eq_zero_hom e i q hi hexact)).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact primitiveTorsion_functionExact e i q hi hexact
  · intro x y hxy
    apply Subtype.ext
    apply hi
    exact congrArg Subtype.val hxy
  · exact hsurj

include k in
/-- Hoshino's restricted sequence is short exact whenever the quotient
target is nonprojective. -/
theorem primitiveTorsion_shortExact_of_not_projective (e : A)
    {Q E N : FinitelyGeneratedCategory A}
    (hN : IsAnnihilatedBy (primitiveIdeal e) N)
    (i : Q ⟶ E) (q : E ⟶ N)
    (hi : Function.Injective i)
    (hexact : Function.Exact i q)
    (hq : IsRightAlmostSplit q)
    (hNprojective :
      ¬ Projective (⟨N, hN⟩ : PrimitiveQuotientSubcategory e)) :
    (ShortComplex.mk (primitiveTorsionMap e i).hom
      (primitiveTorsionAmbientTargetMap e q).hom
      (primitiveTorsion_comp_eq_zero_hom e i q hi hexact)).ShortExact :=
  primitiveTorsion_shortExact e i q hi hexact
    (primitiveTorsionAmbientTargetMap_surjective_of_not_projective
      (k := k) e hN q hq hNprojective)

include k in
/-- Hoshino's restricted short exact sequence retained in the finitely
generated ambient module category. -/
theorem primitiveTorsion_fg_shortExact_of_not_projective (e : A)
    {Q E N : FinitelyGeneratedCategory A}
    (hN : IsAnnihilatedBy (primitiveIdeal e) N)
    (i : Q ⟶ E) (q : E ⟶ N)
    (hi : Function.Injective i)
    (hexact : Function.Exact i q)
    (hq : IsRightAlmostSplit q)
    (hNprojective :
      ¬ Projective (⟨N, hN⟩ : PrimitiveQuotientSubcategory e)) :
    (ShortComplex.mk (primitiveTorsionMap e i)
      (primitiveTorsionAmbientTargetMap e q)
      (primitiveTorsion_comp_eq_zero e i q hi hexact)).ShortExact := by
  apply ShortExact.reflects_shortExact_of_faithful
    (forget₂ (FinitelyGeneratedCategory A) (RightModule.Category A))
  convert primitiveTorsion_shortExact_of_not_projective
    (k := k) e hN i q hi hexact hq hNprojective using 1
  all_goals rfl

end MagnitudeConjecture.RightModule
