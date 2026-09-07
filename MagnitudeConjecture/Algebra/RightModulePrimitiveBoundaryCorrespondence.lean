import MagnitudeConjecture.Algebra.RightModulePrimitiveDeletion
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitUniqueness
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.Algebra.Category.FGModuleCat.Abelian

/-!
# Boundary markers of a primitive new mesh

For a new right mesh `M → U → N` in the primitive quotient, this file
constructs the inverse ambient marker `p_M = τ_A⁻¹M`.  It proves that `p_M`
survives the quotient by `mod (A/AeA)` and is tau-projective there.  Thus it is
the projective boundary marker paired with the already constructed
tau-injective marker `q_N = τ_A N`.

The survival proof is categorical.  If `p_M` were an `A/AeA`-module,
extension closure would put the ambient AR sequence ending at `p_M` inside the
literal quotient subcategory.  Its first map and Hoshino's relative first map
would then be minimal left almost split with the same source.  Uniqueness and
short exactness identify their endpoints, contradicting survival of `q_N`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open MagnitudeConjecture

set_option autoImplicit false

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

namespace QuotientSubmoduleEquidistribution

universe v

variable {C : Type u} [Category.{v} C]

/-- An ambient left almost-split morphism remains left almost split after
restricting both endpoints to a full subcategory. -/
theorem IsLeftAlmostSplit.fullSubcategory
    (P : ObjectProperty C) {X Y : P.FullSubcategory}
    (f : X ⟶ Y) (hf : IsLeftAlmostSplit f.hom) :
    IsLeftAlmostSplit f := by
  constructor
  · intro hsplit
    apply hf.not_isSplitMono
    obtain ⟨r⟩ := hsplit.exists_splitMono
    exact IsSplitMono.mk' {
      retraction := r.retraction.hom
      id := congrArg (fun q ↦ q.hom) r.id }
  · intro Z g hg
    have hgAmbient : ¬ IsSplitMono g.hom := by
      intro hsplit
      apply hg
      obtain ⟨r⟩ := hsplit.exists_splitMono
      exact IsSplitMono.mk' {
        retraction := ObjectProperty.homMk r.retraction
        id := by
          apply ObjectProperty.hom_ext
          exact r.id }
    obtain ⟨h, hh⟩ := hf.factors g.hom hgAmbient
    refine ⟨ObjectProperty.homMk h, ?_⟩
    apply ObjectProperty.hom_ext
    exact hh

/-- Ambient left minimality remains left minimal after restricting both
endpoints to a full subcategory. -/
theorem IsLeftMinimal.fullSubcategory
    (P : ObjectProperty C) {X Y : P.FullSubcategory}
    (f : X ⟶ Y) (hf : IsLeftMinimal f.hom) :
    IsLeftMinimal f := by
  intro a ha
  have haAmbient : f.hom ≫ a.hom = f.hom := by
    exact congrArg (fun q ↦ q.hom) ha
  haveI : IsIso a.hom := hf a.hom haAmbient
  exact (ObjectProperty.isIso_hom_iff a).mp inferInstance

/-- A left almost-split kernel inclusion is left minimal when every split
epimorphic endomorphism of the right endpoint is invertible. -/
theorem IsRightAlmostSplit.kernel_ι_isLeftMinimal_of_splitEpi_end_isIso
    {D : Type u} [Category.{v} D] [Abelian D]
    {E Z : D} (f : E ⟶ Z) [Epi f]
    (hf : IsRightAlmostSplit f)
    (hk : IsLeftAlmostSplit (kernel.ι f))
    (hiso : ∀ d : Z ⟶ Z, IsSplitEpi d → IsIso d) :
    IsLeftMinimal (kernel.ι f) := by
  intro e he
  let hcok := Abelian.epiIsCokernelOfKernel
    (KernelFork.ofι (kernel.ι f) (kernel.condition f))
    (kernelIsKernel f)
  have hezero : kernel.ι f ≫ (e ≫ f) = 0 := by
    rw [← Category.assoc, he, kernel.condition]
  obtain ⟨d, hd⟩ :=
    CokernelCofork.IsColimit.desc' hcok (e ≫ f) hezero
  change Z ⟶ Z at d
  change f ≫ d = e ≫ f at hd
  have hdsplit : IsSplitEpi d := by
    by_contra hdnot
    obtain ⟨h, hh⟩ := hf.factors d hdnot
    let a : E ⟶ E := e - f ≫ h
    have haf : a ≫ f = 0 := by
      dsimp only [a]
      rw [Preadditive.sub_comp, Category.assoc, hh, hd]
      simp
    let t : E ⟶ kernel f := kernel.lift f a haf
    have ht : t ≫ kernel.ι f = a := kernel.lift_ι f a haf
    apply hk.not_isSplitMono
    exact IsSplitMono.mk' {
      retraction := t
      id := by
        apply (cancel_mono (kernel.ι f)).1
        rw [Category.assoc, ht]
        dsimp only [a]
        rw [Preadditive.comp_sub, he, ← Category.assoc,
          kernel.condition, zero_comp, sub_zero, Category.id_comp] }
  letI : IsIso d := hiso d hdsplit
  let T : ShortComplex D :=
    ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel T (kernelIsKernel f) }
  let φ : T ⟶ T := {
    τ₁ := 𝟙 _
    τ₂ := e
    τ₃ := d
    comm₁₂ := by simpa only [Category.id_comp] using he.symm
    comm₂₃ := hd.symm }
  change IsIso φ.τ₂
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hT hT

end QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

open QuotientSubmoduleEquidistribution

variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {e : A} {D : RightModule.PrimitiveIdempotentData e}

/-- The inverse marker `p_M = τ_A⁻¹M` of the source of a new quotient
mesh survives the factor by `mod (A/AeA)`. -/
theorem PrimitiveNewRightMeshEndpoint.leftMarkerAmbientLabel_not_mem
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.leftMarkerAmbientLabel H he ∉ S.primitiveKilledLabels D := by
  intro hpKilled
  let y := N.sourceNoninjectiveLabel H he
  let z := (S.rightTranslationEquiv).symm y
  have hzSource : S.rightTranslationLabel z =
      N.sourceAmbientLabel H he := by
    exact congrArg Subtype.val
      (S.rightTranslationEquiv.apply_symm_apply y)
  have hsourceKilled : IsAnnihilatedBy (primitiveIdeal e)
      (S.fgObj (S.rightTranslationLabel z)) := by
    rw [hzSource]
    exact (S.mem_primitiveKilledLabels_iff_isAnnihilatedBy D _).mp
      (N.sourceAmbientLabel_mem H he)
  have hpLabel : z.1 = N.leftMarkerAmbientLabel H he := rfl
  have hpAnnihilated : IsAnnihilatedBy (primitiveIdeal e)
      (S.fgObj z.1) := by
    rw [hpLabel]
    exact (S.mem_primitiveKilledLabels_iff_isAnnihilatedBy D _).mp
      hpKilled
  let Bp := S.minimalRightAlmostSplitAt z.1
  have hmiddleAnnihilated : IsAnnihilatedBy (primitiveIdeal e) Bp.middle :=
    isAnnihilatedBy_primitiveIdeal_middle_of_exact he
      (S.rightKernelMap z) Bp.map (S.rightKernelMap_functionExact z)
      hsourceKilled hpAnnihilated
  have hRelativeAmbient := N.fgShortComplex_shortExact
  let C := PrimitiveQuotientSubcategory e
  letI : IsNoetherianRing (primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      (primitiveQuotientEquivalence (k := k) e).functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence
    (primitiveQuotientEquivalence (k := k) e).functor
  letI : HasZeroMorphisms C :=
    CategoryTheory.Abelian.nonPreadditiveAbelian.toHasZeroMorphisms
  letI : HasZeroMorphisms (FinitelyGeneratedCategory A) :=
    (ModuleCat.isFG Aᵐᵒᵖ).instHasZeroMorphismsFullSubcategory
  let X₁ : C := primitiveTorsionSubcategoryObj e
    (S.fgObj N.rightMarker.1)
  let X₂ : C := primitiveTorsionSubcategoryObj e
    (S.minimalRightAlmostSplitAt N.label.1).middle
  let X₃ : C := ⟨S.fgObj N.label.1,
    (S.mem_primitiveKilledLabels_iff_isAnnihilatedBy D N.label.1).mp
      N.label.2⟩
  let f : X₁ ⟶ X₂ := ObjectProperty.homMk
    (primitiveTorsionMap e (S.rightKernelMap N.ambientLabel))
  let g : X₂ ⟶ X₃ := primitiveTorsionTargetMap e X₃.property
    (S.minimalRightAlmostSplitAt N.label.1).map
  have hfg : f ≫ g = 0 := by
    apply ObjectProperty.hom_ext
    exact primitiveTorsion_comp_eq_zero e
      (S.rightKernelMap N.ambientLabel)
      (S.minimalRightAlmostSplitAt N.label.1).map
      N.rightKernelMap_injective
      (S.rightKernelMap_functionExact N.ambientLabel)
  letI : Mono N.fgShortComplex.f := hRelativeAmbient.mono_f
  have hfKernel : IsLimit (KernelFork.ofι f hfg) := by
    refine Fork.IsLimit.mk _ (fun s ↦ ObjectProperty.homMk
      (hRelativeAmbient.exact.lift s.ι.hom ?_)) ?_ ?_
    · apply FGModuleCat.hom_ext
      ext x
      have hs := congrArg (fun q ↦ q.hom.hom x)
        (congrArg (fun q ↦ q.hom) s.condition)
      exact hs
    · intro s
      apply ObjectProperty.hom_ext
      exact hRelativeAmbient.exact.lift_f s.ι.hom _
    · intro s m hm
      apply ObjectProperty.hom_ext
      have hmAmbient := congrArg (fun q ↦ q.hom) hm
      change m.hom ≫ f.hom = s.ι.hom at hmAmbient
      have hfOld : f.hom = N.fgShortComplex.f := rfl
      rw [hfOld] at hmAmbient
      have hmOld : m.hom ≫ N.fgShortComplex.f = s.ι.hom := by
        exact hmAmbient
      have hliftOld := hRelativeAmbient.exact.lift_f s.ι.hom
        (by
          apply FGModuleCat.hom_ext
          ext x
          have hs := congrArg (fun q ↦ q.hom.hom x)
            (congrArg (fun q ↦ q.hom) s.condition)
          exact hs)
      apply (cancel_mono N.fgShortComplex.f).1
      exact hmOld.trans hliftOld.symm
  have hgSurjective : Function.Surjective g.hom :=
    primitiveTorsionAmbientTargetMap_surjective_of_not_projective
      (k := k) e X₃.property
      (S.minimalRightAlmostSplitAt N.label.1).map
      (S.minimalRightAlmostSplitAt N.label.1).rightAlmostSplit
      N.quotient_nonprojective
  haveI : Epi g.hom :=
    (IndecomposableSkeleton.fg_epi_iff_surjective g.hom).2 hgSurjective
  letI : Epi g := by
    constructor
    intro Z a b hab
    apply ObjectProperty.hom_ext
    apply (cancel_epi g.hom).1
    exact congrArg (fun q ↦ q.hom) hab
  have hgASMin : IsRightAlmostSplit g ∧ IsRightMinimal g := by
    simpa only [g, X₃, PrimitiveNewRightMeshEndpoint.ambientLabel] using
      S.primitiveTorsionTargetMap_minimalRightAlmostSplit
        H he N.ambientLabel X₃.property N.quotient_nonprojective
  have hkAS : IsLeftAlmostSplit (kernel.ι g) :=
    hgASMin.1.kernel_ι_isLeftAlmostSplit g hgASMin.2
  have hkMin : IsLeftMinimal (kernel.ι g) := by
    apply hgASMin.1.kernel_ι_isLeftMinimal_of_splitEpi_end_isIso g hkAS
    intro d hd
    obtain ⟨r⟩ := hd.exists_splitEpi
    let dA : S.fgObj N.label.1 ⟶ S.fgObj N.label.1 := d.hom
    let hdAEpi : IsSplitEpi dA := IsSplitEpi.mk' {
      section_ := r.section_.hom
      id := congrArg (fun q ↦ q.hom) r.id }
    let hmono : IsSplitMono dA :=
      @IndecomposableSkeleton.isSplitMono_of_isSplitEpi_between_obj
        (MulOpposite A) _ _ (Fin S.n) S.almostSplitSkeleton
          N.label.1 N.label.1 dA hdAEpi
    letI : IsSplitEpi dA := hdAEpi
    letI : IsSplitMono dA := hmono
    letI : IsIso dA := isIso_of_epi_of_isSplitMono dA
    apply (ObjectProperty.isIso_hom_iff d).mp
    change IsIso dA
    infer_instance
  let eK : X₁ ≅ kernel g :=
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel g) hfKernel).symm
  have heK : eK.hom ≫ kernel.ι g = f := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp hfKernel
      (kernelIsKernel g) WalkingParallelPair.zero
  have hfAS : IsLeftAlmostSplit f := by
    rw [← heK]
    exact hkAS.precomp_iso eK
  have hfMin : IsLeftMinimal f := by
    rw [← heK]
    exact hkMin.precomp_iso eK
  let P₂ : C := ⟨Bp.middle, hmiddleAnnihilated⟩
  let eSourceAmbient : N.sourceModule ≅
      S.fgObj (S.rightTranslationLabel z) :=
    (N.sourceIso H he).trans
      (eqToIso (congrArg S.fgObj hzSource.symm))
  let fp : X₁ ⟶ P₂ := ObjectProperty.homMk
    (eSourceAmbient.hom ≫ S.rightKernelMap z)
  let P₁ : C := ⟨S.fgObj (S.rightTranslationLabel z), hsourceKilled⟩
  let fp₀ : P₁ ⟶ P₂ := ObjectProperty.homMk (S.rightKernelMap z)
  let eSource : X₁ ≅ P₁ := ObjectProperty.isoMk _ eSourceAmbient
  have hfp₀AS : IsLeftAlmostSplit fp₀ :=
    (S.rightKernelMap_leftAlmostSplit z).fullSubcategory
      (PrimitiveQuotientProperty e) fp₀
  have hfp₀Min : IsLeftMinimal fp₀ :=
    (S.rightKernelMap_leftMinimal z).fullSubcategory
      (PrimitiveQuotientProperty e) fp₀
  have hfpEq : eSource.hom ≫ fp₀ = fp := rfl
  have hfpAS : IsLeftAlmostSplit fp := by
    rw [← hfpEq]
    exact hfp₀AS.precomp_iso eSource
  have hfpMin : IsLeftMinimal fp := by
    rw [← hfpEq]
    exact hfp₀Min.precomp_iso eSource
  obtain ⟨eMiddle, heMiddle⟩ :=
    exists_leftAlmostSplit_middleIso hfAS hfMin hfpAS hfpMin
  have hBpSurjective : Function.Surjective Bp.map := by
    letI : Epi Bp.map :=
      IndecomposableSkeleton.IsRightAlmostSplit.epi_of_not_projective_obj
        S.almostSplitSkeleton Bp.map Bp.rightAlmostSplit z.2
    exact (IndecomposableSkeleton.fg_epi_iff_surjective Bp.map).1
      inferInstance
  have hrightKernelInjective : Function.Injective (S.rightKernelMap z) := by
    haveI : Mono (S.rightKernelMap z) := by
      change Mono
        ((S.rightTranslationKernelIso z).inv ≫ kernel.ι Bp.map)
      infer_instance
    exact (IndecomposableSkeleton.fg_mono_iff_injective
      (S.rightKernelMap z)).1 inferInstance
  have hzeroBase : S.rightKernelMap z ≫ Bp.map = 0 := by
    change ((S.rightTranslationKernelIso z).inv ≫
      kernel.ι Bp.map) ≫ Bp.map = 0
    simp
  let Base := ShortComplex.mk (S.rightKernelMap z) Bp.map hzeroBase
  have hBase : Base.ShortExact := by
    apply ShortExact.reflects_shortExact_of_faithful
      (forget₂ (FinitelyGeneratedCategory A) (RightModule.Category A))
    apply ModuleCat.shortComplex_shortExact
    · exact S.rightKernelMap_functionExact z
    · exact hrightKernelInjective
    · exact hBpSurjective
  let pFirst : N.fgShortComplex.X₁ ⟶ Bp.middle :=
    eSourceAmbient.hom ≫ S.rightKernelMap z
  have hzeroP : pFirst ≫ Bp.map = 0 := by
    change (eSourceAmbient.hom ≫
      ((S.rightTranslationKernelIso z).inv ≫ kernel.ι Bp.map)) ≫
        Bp.map = 0
    simp
  let P := ShortComplex.mk pFirst Bp.map hzeroP
  let ePB : P ≅ Base := ShortComplex.isoMk eSourceAmbient
    (Iso.refl _) (Iso.refl _)
  have hP : P.ShortExact :=
    ShortComplex.shortExact_of_iso ePB.symm hBase
  let eMiddleAmbient : N.fgShortComplex.X₂ ≅ P.X₂ := by
    change X₂.obj ≅ P₂.obj
    exact (PrimitiveQuotientProperty e).ι.mapIso eMiddle
  have heMiddleAmbient : N.fgShortComplex.f ≫ eMiddleAmbient.hom =
      P.f := by
    exact congrArg (fun q ↦ q.hom) heMiddle
  let eSourceId : N.fgShortComplex.X₁ ≅ P.X₁ := Iso.refl _
  let eC : cokernel N.fgShortComplex.f ≅ cokernel P.f :=
    cokernel.mapIso N.fgShortComplex.f P.f eSourceId eMiddleAmbient
      (by simpa only [eSourceId, Iso.refl_hom, Category.id_comp] using
        heMiddleAmbient)
  let eT : cokernel N.fgShortComplex.f ≅ N.fgShortComplex.X₃ :=
    colimit.isoColimitCocone {
      cocone := CokernelCofork.ofπ N.fgShortComplex.g
        N.fgShortComplex.zero
      isColimit := hRelativeAmbient.gIsCokernel }
  let eP : cokernel P.f ≅ P.X₃ :=
    colimit.isoColimitCocone {
      cocone := CokernelCofork.ofπ P.g P.zero
      isColimit := hP.gIsCokernel }
  let eEnd : N.fgShortComplex.X₃ ≅ P.X₃ :=
    eT.symm.trans (eC.trans eP)
  have hlabels : N.label.1 = z.1 :=
    S.fgObj_skeletal ⟨eEnd⟩
  have hambientLabel : N.ambientLabel = z := Subtype.ext hlabels
  have hzTranslationMem : S.rightTranslationLabel z ∈
      S.primitiveKilledLabels D := by
    rw [hzSource]
    exact N.sourceAmbientLabel_mem H he
  have htranslation : S.rightTranslationLabel N.ambientLabel =
      S.rightTranslationLabel z := congrArg _ hambientLabel
  exact N.translation_not_mem (htranslation.symm ▸ hzTranslationMem)

/-- The surviving left marker bundled as an object label of the primitive
factor. -/
def PrimitiveNewRightMeshEndpoint.leftMarker
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.SurvivingLabel (S.primitiveKilledLabels D) :=
  ⟨N.leftMarkerAmbientLabel H he,
    N.leftMarkerAmbientLabel_not_mem H he⟩

/-- The inverse ambient translate defining `p_M` is not projective in
`mod A`.  Its projectivity is created only after passing to the factor. -/
theorem PrimitiveNewRightMeshEndpoint.leftMarker_ambient_not_projective
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    ¬ Projective (S.fgObj (N.leftMarker H he).1) := by
  change ¬ Projective
    (S.fgObj
      ((S.rightTranslationEquiv).symm
        (N.sourceNoninjectiveLabel H he)).1)
  exact ((S.rightTranslationEquiv).symm
    (N.sourceNoninjectiveLabel H he)).2

/-- The inverse marker `p_M` is tau-projective in the primitive factor: its
ambient translate is the killed quotient source `M`. -/
theorem PrimitiveNewRightMeshEndpoint.leftMarker_isProjective
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    (S.factorFiniteTauCategoryData (S.primitiveKilledLabels D)).IsProjective
      (N.leftMarker H he) := by
  let K := S.primitiveKilledLabels D
  let y := N.sourceNoninjectiveLabel H he
  let z := (S.rightTranslationEquiv).symm y
  have hzSource : S.rightTranslationLabel z =
      N.sourceAmbientLabel H he := by
    exact congrArg Subtype.val
      (S.rightTranslationEquiv.apply_symm_apply y)
  have hnotProjective : ¬ Projective
      (S.fgObj (N.leftMarker H he).1) := by
    exact N.leftMarker_ambient_not_projective H he
  let z' : {x : Fin S.n // ¬ Projective (S.fgObj x)} :=
    ⟨(N.leftMarker H he).1, hnotProjective⟩
  have hzz : z' = z := Subtype.ext (by rfl)
  have hz'Source : S.rightTranslationLabel z' =
      N.sourceAmbientLabel H he := by
    rw [hzz]
    exact hzSource
  let T := S.labelRightMesh (N.leftMarker H he).1
  let eT₀ : T.X₁ ≅ S.fgObj (S.rightTranslationLabel z') := by
    simpa [T, labelRightMesh, hnotProjective, nonprojectiveRightMesh,
      z'] using S.rightTranslationKernelIso z'
  let eT : T.X₁ ≅ S.fgObj (N.sourceAmbientLabel H he) :=
    eT₀.trans (eqToIso (congrArg S.fgObj hz'Source))
  let eQ :
      (S.factorRawRightMesh K (N.leftMarker H he).1).X₁ ≅
        (S.factorModuleFunctor K).obj
          (S.fgObj (N.sourceAmbientLabel H he)) :=
    (S.factorModuleFunctor K).mapIso eT
  have hsource : IsZero
      ((S.factorModuleFunctor K).obj
        (S.fgObj (N.sourceAmbientLabel H he))) :=
    (S.factorObject_isZero_of_mem K (N.sourceAmbientLabel_mem H he)).of_iso
      (S.factorAmbientPointIsoFactorModule K
        (N.sourceAmbientLabel H he))
  have hraw : IsZero
      (S.factorRawRightMesh K (N.leftMarker H he).1).X₁ :=
    hsource.of_iso eQ
  change IsZero
    (S.canonicalFactorRightMesh K
      (S.factorObject K (N.leftMarker H he))).X₁
  rw [S.canonicalFactorRightMesh_at_label K (N.leftMarker H he)]
  rw [factorLabelRightMesh]
  simp only [dif_pos (Or.inl hraw), factorZeroLeftRightMesh]
  exact S.factorZeroObject_isZero K

/-- The factor-projective boundary label supplied by a new mesh endpoint. -/
def PrimitiveNewRightMeshEndpoint.leftMarkerProjectiveLabel
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.FactorProjectiveLabel (S.primitiveKilledLabels D) :=
  ⟨N.leftMarker H he, N.leftMarker_isProjective H he⟩

/-- The boundary coordinate theorem gives the marker multiplicity
`[p_M : S_e] = 1`. -/
theorem PrimitiveNewRightMeshEndpoint.leftMarker_primitiveMultiplicity_eq_one
    [IsAlgClosed k]
    (B : S.PrimitiveDirectedBoundaryData
      (S.primitiveMultiplicityInput D))
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    S.primitiveMultiplicity D (N.leftMarker H he).1 = 1 :=
  B.projective_multiplicity_eq_one
    (N.leftMarkerProjectiveLabel H he)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
