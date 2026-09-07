import MagnitudeConjecture.Algebra.CornerQuotient
import MagnitudeConjecture.Algebra.RightModuleNakayamaARIdentification
import MagnitudeConjecture.Algebra.RightModulePrimitiveTorsion
import MagnitudeConjecture.CategoryTheory.AlmostSplitShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Hoshino's primitive-torsion argument

This file formalizes the homological step in Hoshino's reduction.  Stable
Auslander--Reiten duality kills the relevant `Ext¹` group, so every
endomorphism of the primitive torsion radical extends to the ambient
Auslander--Reiten source.  The resulting surjection of endomorphism rings
transports locality, and hence indecomposability, to the torsion radical.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture

universe u v

namespace CategoryTheory

variable {C : Type u} [Category C] [Abelian C] [HasExt.{v} C]

/-- In the contravariant long exact sequence of a short exact sequence,
vanishing of the following `Ext¹` group makes restriction along the kernel
surjective on morphisms. -/
theorem ShortComplex.ShortExact.precomp_surjective_of_ext_subsingleton
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    [Subsingleton (Ext.{v} S.X₃ Y 1)] :
    Function.Surjective (fun f : S.X₂ ⟶ Y ↦ S.f ≫ f) := by
  intro f
  have hzero :
      hS.extClass.comp (Ext.mk₀ f) (rfl : 1 + 0 = 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x₂, hx₂⟩ :=
    Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ f)
      (rfl : 1 + 0 = 1) hzero
  refine ⟨Ext.addEquiv₀ x₂, ?_⟩
  apply (Ext.mk₀_bijective S.X₁ Y).1
  rw [← Ext.mk₀_comp_mk₀]
  simpa using hx₂

end CategoryTheory

namespace RightModule

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

/-- Restriction of ambient endomorphisms to the primitive torsion radical,
as a homomorphism of (possibly noncommutative) rings. -/
def primitiveTorsionEndRestriction (e : A)
    (M : FinitelyGeneratedCategory A) :
    End M →+* End (primitiveTorsionFGObj e M) where
  toFun := primitiveTorsionMap e
  map_one' := by
    apply FGModuleCat.hom_ext
    ext x
    rfl
  map_mul' f g := by
    apply FGModuleCat.hom_ext
    ext x
    rfl
  map_zero' := by
    apply FGModuleCat.hom_ext
    ext x
    rfl
  map_add' f g := by
    apply FGModuleCat.hom_ext
    ext x
    rfl

/-- If the torsion-free quotient has no degree-one extensions into the
ambient module, every endomorphism of the torsion radical extends to an
ambient endomorphism. -/
theorem primitiveTorsionEndRestriction_surjective_of_ext_subsingleton
    [HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ)]
    (e : A) (M : FinitelyGeneratedCategory A)
    [Subsingleton
      (Ext.{u} (primitiveTorsionQuotientFGObj e M) M 1)] :
    Function.Surjective (primitiveTorsionEndRestriction e M) := by
  let S : ShortComplex (FinitelyGeneratedCategory A) :=
    ShortComplex.mk (primitiveTorsionInclusion e M)
      (primitiveTorsionQuotientMk e M)
      (primitiveTorsionInclusion_comp_quotientMk e M)
  have hS : S.ShortExact := primitiveTorsionQuotient_fg_shortExact e M
  letI : Mono (primitiveTorsionInclusion e M) :=
    (IndecomposableSkeleton.fg_mono_iff_injective
      (primitiveTorsionInclusion e M)).2
      (primitiveTorsionSubmodule e M).subtype_injective
  intro a
  obtain ⟨b, hb⟩ :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.precomp_surjective_of_ext_subsingleton
      hS M
      (a ≫ primitiveTorsionInclusion e M)
  refine ⟨b, ?_⟩
  change primitiveTorsionMap e b = a
  apply (cancel_mono (primitiveTorsionInclusion e M)).1
  rw [primitiveTorsionMap_comp_inclusion]
  exact hb

namespace FiniteIndecomposableSkeleton

variable {S : RightModule.FiniteIndecomposableSkeleton k A}

/-- The transported kernel inclusion of the chosen right AR map is exact on
underlying module elements. -/
theorem rightKernelMap_functionExact
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    Function.Exact (S.rightKernelMap z)
      (S.minimalRightAlmostSplitAt z.1).map := by
  let B := S.minimalRightAlmostSplitAt z.1
  let e := S.rightTranslationKernelIso z
  have hzero : S.rightKernelMap z ≫ B.map = 0 := by
    change ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map) ≫
      B.map = 0
    simp
  have hKernel : IsLimit
      (KernelFork.ofι (S.rightKernelMap z) hzero) :=
    IsLimit.ofIsoLimit (kernelIsKernel B.map)
      (Fork.ext e (by
        change e.hom ≫ ((S.rightTranslationKernelIso z).inv ≫
          kernel.ι B.map) = kernel.ι B.map
        simp [e]))
  let T : ShortComplex (FinitelyGeneratedCategory A) :=
    ShortComplex.mk (S.rightKernelMap z) B.map hzero
  have hT : T.Exact := T.exact_of_f_is_kernel hKernel
  let U := forget₂ (FinitelyGeneratedCategory A) (RightModule.Category A)
  have hTU : (T.map U).Exact := hT.map U
  have hfun : Function.Exact (T.map U).f (T.map U).g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hTU
  change Function.Exact (S.rightKernelMap z).hom.hom B.map.hom.hom at hfun
  exact hfun

/-- Under the manuscript's quotient-nonprojectivity hypothesis, the primitive
torsion radical of the ambient AR translate is nonzero. -/
theorem primitiveTorsionFGObj_rightTranslation_nontrivial
    {e : A}
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hN : IsAnnihilatedBy (primitiveIdeal e) (S.fgObj z.1))
    (hNprojective :
      ¬ Projective
        (⟨S.fgObj z.1, hN⟩ : PrimitiveQuotientSubcategory e)) :
    Nontrivial
      (primitiveTorsionFGObj e
        (S.fgObj (S.rightTranslationLabel z))) := by
  let B := S.minimalRightAlmostSplitAt z.1
  haveI : Mono (S.rightKernelMap z) := by
    change Mono
      ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map)
    infer_instance
  exact primitiveTorsionFGObj_nontrivial_of_not_projective
    (k := k) e hN (S.rightKernelMap z) B.map
      ((IndecomposableSkeleton.fg_mono_iff_injective
        (S.rightKernelMap z)).1 inferInstance)
      (S.rightKernelMap_functionExact z)
      B.rightAlmostSplit hNprojective

/-- Hoshino's AR-duality vanishing: for a quotient-module endpoint `N`, the
torsion-free quotient of its ambient AR translate has vanishing `Ext¹` into
that translate. -/
theorem primitiveTorsionQuotient_extOne_rightTranslation_subsingleton
    [IsAlgClosed k]
    [HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ)]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (he : IsIdempotentElem e)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hN : IsAnnihilatedBy (primitiveIdeal e) (S.fgObj z.1)) :
    Subsingleton
      (Ext.{u}
        (primitiveTorsionQuotientFGObj e
          (S.fgObj (S.rightTranslationLabel z)))
        (S.fgObj (S.rightTranslationLabel z)) 1) := by
  obtain ⟨P⟩ := twoStepMinimalProjectivePresentation_nonempty k
    (S.fgObj z.1)
  obtain ⟨eNak⟩ := S.rightTranslationIso_nakayamaKernel H z P
  have hzero : ∀ xi : Ext.{u}
      (primitiveTorsionQuotientFGObj e
        (S.fgObj (S.rightTranslationLabel z)))
      (S.fgObj (S.rightTranslationLabel z)) 1, xi = 0 := by
    intro xi
    let xi' : Ext.{u}
        (primitiveTorsionQuotientFGObj e
          (S.fgObj (S.rightTranslationLabel z)))
        (P.nakayamaKernel (k := k)) 1 :=
      xi.comp (Ext.mk₀ eNak.hom) (add_zero 1)
    have hstable : ∀ a : RightModule.projectiveStableHom
        (k := k) (S.fgObj z.1)
        (primitiveTorsionQuotientFGObj e
          (S.fgObj (S.rightTranslationLabel z))), a = 0 := by
      intro a
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      have hf : f = 0 :=
        hom_to_primitiveTorsionQuotient_eq_zero he hN f
      rw [hf]
      simp
    have hxi' : xi' = 0 := by
      apply (P.stableHomExtLinearEquiv (k := k)
        (primitiveTorsionQuotientFGObj e
          (S.fgObj (S.rightTranslationLabel z)))).injective
      apply LinearMap.ext
      intro a
      rw [hstable a]
      simp
    have hrecover := congrArg
      (fun eta : Ext.{u}
          (primitiveTorsionQuotientFGObj e
            (S.fgObj (S.rightTranslationLabel z)))
          (P.nakayamaKernel (k := k)) 1 ↦
        eta.comp (Ext.mk₀ eNak.inv) (add_zero 1)) hxi'
    simpa [xi', Ext.comp_assoc_of_second_deg_zero] using hrecover
  exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩

/-- The restriction from the endomorphism ring of an ambient AR translate to
the endomorphism ring of its primitive torsion radical is surjective. -/
theorem primitiveTorsionEndRestriction_rightTranslation_surjective
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (he : IsIdempotentElem e)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hN : IsAnnihilatedBy (primitiveIdeal e) (S.fgObj z.1)) :
    Function.Surjective
      (primitiveTorsionEndRestriction e
        (S.fgObj (S.rightTranslationLabel z))) := by
  letI : EnoughProjectives (FGModuleCat.{u} Aᵐᵒᵖ) :=
    fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  letI : Subsingleton
      (Ext.{u}
        (primitiveTorsionQuotientFGObj e
          (S.fgObj (S.rightTranslationLabel z)))
        (S.fgObj (S.rightTranslationLabel z)) 1) :=
    S.primitiveTorsionQuotient_extOne_rightTranslation_subsingleton
      H he z hN
  exact primitiveTorsionEndRestriction_surjective_of_ext_subsingleton
    e (S.fgObj (S.rightTranslationLabel z))

/-- A nonzero primitive torsion radical of an ambient AR translate inherits
a local endomorphism ring. -/
theorem primitiveTorsionFGObj_rightTranslation_end_isLocalRing
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (he : IsIdempotentElem e)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hN : IsAnnihilatedBy (primitiveIdeal e) (S.fgObj z.1))
    (hNprojective :
      ¬ Projective
        (⟨S.fgObj z.1, hN⟩ : PrimitiveQuotientSubcategory e)) :
    IsLocalRing
      (End (primitiveTorsionFGObj e
        (S.fgObj (S.rightTranslationLabel z)))) := by
  let R := primitiveTorsionFGObj e
    (S.fgObj (S.rightTranslationLabel z))
  letI : Nontrivial R :=
    S.primitiveTorsionFGObj_rightTranslation_nontrivial
      z hN hNprojective
  letI : IsLocalRing (End (S.fgObj (S.rightTranslationLabel z))) :=
    S.fgObj_end_isLocalRing (S.rightTranslationLabel z)
  letI : Nontrivial (End R) :=
    (fgEndModuleEndRingEquiv (A := A) R).symm.injective.nontrivial
  exact MagnitudeConjecture.isLocalRing_of_surjective
    (primitiveTorsionEndRestriction e
      (S.fgObj (S.rightTranslationLabel z)))
    (S.primitiveTorsionEndRestriction_rightTranslation_surjective
      H he z hN)

/-- The primitive torsion radical of the ambient AR translate is an
indecomposable module under exactly Hoshino's nonprojectivity hypothesis. -/
theorem primitiveTorsionFGObj_rightTranslation_isIndecomposableModule
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (he : IsIdempotentElem e)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hN : IsAnnihilatedBy (primitiveIdeal e) (S.fgObj z.1))
    (hNprojective :
      ¬ Projective
        (⟨S.fgObj z.1, hN⟩ : PrimitiveQuotientSubcategory e)) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Aᵐᵒᵖ
      (primitiveTorsionFGObj e
        (S.fgObj (S.rightTranslationLabel z))) := by
  let R := primitiveTorsionFGObj e
    (S.fgObj (S.rightTranslationLabel z))
  letI : Nontrivial R :=
    S.primitiveTorsionFGObj_rightTranslation_nontrivial
      z hN hNprojective
  letI : IsLocalRing (End R) :=
    S.primitiveTorsionFGObj_rightTranslation_end_isLocalRing
      H he z hN hNprojective
  letI : IsLocalRing (Module.End Aᵐᵒᵖ R) :=
    RingEquiv.isLocalRing_noncomm
      (fgEndModuleEndRingEquiv (A := A) R)
  exact
    QuotientSubmoduleEquidistribution.Foundation.isIndecomposableModule_of_isLocalRing_end

/-- The torsion-restricted ambient AR epimorphism is right minimal. -/
theorem primitiveTorsionAmbientTargetMap_rightMinimal
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (he : IsIdempotentElem e)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hN : IsAnnihilatedBy (primitiveIdeal e) (S.fgObj z.1))
    (hNprojective :
      ¬ Projective
        (⟨S.fgObj z.1, hN⟩ : PrimitiveQuotientSubcategory e)) :
    IsRightMinimal
      (primitiveTorsionAmbientTargetMap e
        (S.minimalRightAlmostSplitAt z.1).map) := by
  let B := S.minimalRightAlmostSplitAt z.1
  haveI : Mono (S.rightKernelMap z) := by
    change Mono
      ((S.rightTranslationKernelIso z).inv ≫ kernel.ι B.map)
    infer_instance
  have hi : Function.Injective (S.rightKernelMap z) :=
    (IndecomposableSkeleton.fg_mono_iff_injective
      (S.rightKernelMap z)).1 inferInstance
  have hexact : Function.Exact (S.rightKernelMap z) B.map :=
    S.rightKernelMap_functionExact z
  let T : ShortComplex (FinitelyGeneratedCategory A) :=
    ShortComplex.mk (primitiveTorsionMap e (S.rightKernelMap z))
      (primitiveTorsionAmbientTargetMap e B.map)
      (primitiveTorsion_comp_eq_zero e
        (S.rightKernelMap z) B.map hi hexact)
  have hT : T.ShortExact :=
    primitiveTorsion_fg_shortExact_of_not_projective
      (k := k) e hN (S.rightKernelMap z) B.map hi hexact
        B.rightAlmostSplit hNprojective
  letI : IsLocalRing (End T.X₁) :=
    S.primitiveTorsionFGObj_rightTranslation_end_isLocalRing
      H he z hN hNprojective
  have hnot : ¬ IsSplitEpi T.g := by
    intro hsplit
    apply (primitiveTorsionTargetMap_isRightAlmostSplit
      e hN B.map B.rightAlmostSplit).not_isSplitEpi
    obtain ⟨s⟩ := hsplit.exists_splitEpi
    exact IsSplitEpi.mk' {
      section_ := ObjectProperty.homMk s.section_
      id := by
        apply ObjectProperty.hom_ext
        exact s.id }
  exact
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.isRightMinimal_g_of_local_end
      hT hnot

/-- Hoshino's restricted map is minimal right almost split in the literal
primitive-quotient subcategory. -/
theorem primitiveTorsionTargetMap_minimalRightAlmostSplit
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {e : A} (he : IsIdempotentElem e)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (hN : IsAnnihilatedBy (primitiveIdeal e) (S.fgObj z.1))
    (hNprojective :
      ¬ Projective
        (⟨S.fgObj z.1, hN⟩ : PrimitiveQuotientSubcategory e)) :
    IsRightAlmostSplit
        (primitiveTorsionTargetMap e hN
          (S.minimalRightAlmostSplitAt z.1).map) ∧
      IsRightMinimal
        (primitiveTorsionTargetMap e hN
          (S.minimalRightAlmostSplitAt z.1).map) := by
  let B := S.minimalRightAlmostSplitAt z.1
  constructor
  · exact primitiveTorsionTargetMap_isRightAlmostSplit
      e hN B.map B.rightAlmostSplit
  · intro a ha
    have haAmbient : a.hom ≫
        primitiveTorsionAmbientTargetMap e B.map =
        primitiveTorsionAmbientTargetMap e B.map := by
      have ha' := congrArg (fun f ↦ f.hom) ha
      exact ha'
    have haIso : IsIso a.hom :=
      S.primitiveTorsionAmbientTargetMap_rightMinimal
        H he z hN hNprojective a.hom haAmbient
    exact (ObjectProperty.isIso_hom_iff a).mp haIso

end FiniteIndecomposableSkeleton

end RightModule

end MagnitudeConjecture
