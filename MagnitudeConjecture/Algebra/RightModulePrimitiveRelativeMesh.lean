import MagnitudeConjecture.Algebra.RightModulePrimitiveDeletedSocle
import MagnitudeConjecture.Algebra.RightModulePrimitiveBoundaryCorrespondence

/-!
# Relative almost-split meshes under primitive deletion

This file realizes every Hoshino mesh in the literal primitive-quotient
subcategory, proves both maps are minimal almost split, and derives endpoint
and source uniqueness.  These are the mesh-theoretic inputs for the global
gaining-pair construction.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}
variable {e : A} {D : RightModule.PrimitiveIdempotentData e}

namespace PrimitiveNewRightMeshEndpoint

/-- The Hoshino relative mesh bundled in the literal primitive-quotient
subcategory.  Its underlying ambient short complex is `fgShortComplex`. -/
def quotientShortComplex
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    ShortComplex (RightModule.PrimitiveQuotientSubcategory e) := by
  let X₁ := RightModule.primitiveTorsionSubcategoryObj e
    (S.fgObj N.rightMarker.1)
  let X₂ := RightModule.primitiveTorsionSubcategoryObj e
    (S.minimalRightAlmostSplitAt N.label.1).middle
  let X₃ := S.primitiveQuotientLabelObj D N.label
  let f : X₁ ⟶ X₂ := ObjectProperty.homMk
    (RightModule.primitiveTorsionMap e
      (S.rightKernelMap N.ambientLabel))
  let g : X₂ ⟶ X₃ := RightModule.primitiveTorsionTargetMap e
    ((S.mem_primitiveKilledLabels_iff_isAnnihilatedBy
      D N.label.1).1 N.label.2)
    (S.minimalRightAlmostSplitAt N.label.1).map
  have hfg : f ≫ g = 0 := by
    apply ObjectProperty.hom_ext
    exact RightModule.primitiveTorsion_comp_eq_zero e
      (S.rightKernelMap N.ambientLabel)
      (S.minimalRightAlmostSplitAt N.label.1).map
      N.rightKernelMap_injective
      (S.rightKernelMap_functionExact N.ambientLabel)
  exact ShortComplex.mk f g hfg

/-- The bundled quotient mesh forgets to the previously constructed ambient
Hoshino complex. -/
theorem quotientShortComplex_forget
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.quotientShortComplex.map
        (RightModule.PrimitiveQuotientProperty e).ι =
      N.fgShortComplex := by
  change N.fgShortComplex = N.fgShortComplex
  rfl

/-- The bundled Hoshino mesh is short exact in the literal quotient
subcategory. -/
theorem quotientShortComplex_shortExact
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    N.quotientShortComplex.ShortExact := by
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let C := RightModule.PrimitiveQuotientSubcategory e
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      (RightModule.primitiveQuotientEquivalence (k := k) e).functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence
    (RightModule.primitiveQuotientEquivalence (k := k) e).functor
  apply ShortExact.reflects_shortExact_of_faithful
    (RightModule.PrimitiveQuotientProperty e).ι
  rw [N.quotientShortComplex_forget]
  exact N.fgShortComplex_shortExact

/-- The terminal map of the bundled quotient mesh is the Hoshino minimal
right almost-split morphism. -/
theorem quotientShortComplex_g_minimalRightAlmostSplit [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    IsRightAlmostSplit N.quotientShortComplex.g ∧
      IsRightMinimal N.quotientShortComplex.g := by
  change IsRightAlmostSplit
      (RightModule.primitiveTorsionTargetMap e
        ((S.mem_primitiveKilledLabels_iff_isAnnihilatedBy
          D N.label.1).1 N.label.2)
        (S.minimalRightAlmostSplitAt N.ambientLabel.1).map) ∧
    IsRightMinimal
      (RightModule.primitiveTorsionTargetMap e
        ((S.mem_primitiveKilledLabels_iff_isAnnihilatedBy
          D N.label.1).1 N.label.2)
        (S.minimalRightAlmostSplitAt N.ambientLabel.1).map)
  exact S.primitiveTorsionTargetMap_minimalRightAlmostSplit
    H he N.ambientLabel
    ((S.mem_primitiveKilledLabels_iff_isAnnihilatedBy
      D N.label.1).1 N.label.2)
    N.quotient_nonprojective

/-- The initial map of the bundled quotient mesh is minimal left almost
split.  This is the sourcewise uniqueness input for the negative half of the
new-mesh injection. -/
theorem quotientShortComplex_f_minimalLeftAlmostSplit [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e)
    (N : S.PrimitiveNewRightMeshEndpoint D) :
    IsLeftAlmostSplit N.quotientShortComplex.f ∧
      IsLeftMinimal N.quotientShortComplex.f := by
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let C := RightModule.PrimitiveQuotientSubcategory e
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      (RightModule.primitiveQuotientEquivalence (k := k) e).functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence
    (RightModule.primitiveQuotientEquivalence (k := k) e).functor
  let T := N.quotientShortComplex
  have hT : T.ShortExact := N.quotientShortComplex_shortExact
  letI : Epi T.g := hT.epi_g
  have hg := N.quotientShortComplex_g_minimalRightAlmostSplit H he
  have hkAS : IsLeftAlmostSplit (kernel.ι T.g) :=
    hg.1.kernel_ι_isLeftAlmostSplit T.g hg.2
  have hkMin : IsLeftMinimal (kernel.ι T.g) := by
    apply hg.1.kernel_ι_isLeftMinimal_of_splitEpi_end_isIso T.g hkAS
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
  let eK : T.X₁ ≅ kernel T.g :=
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel T.g)
      hT.fIsKernel).symm
  have heK : eK.hom ≫ kernel.ι T.g = T.f := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp hT.fIsKernel
      (kernelIsKernel T.g) WalkingParallelPair.zero
  constructor
  · rw [← heK]
    exact hkAS.precomp_iso eK
  · rw [← heK]
    exact hkMin.precomp_iso eK

/-- Distinct primitive new meshes have distinct quotient sources.  This is
the sourcewise counterpart of endpoint extensionality and follows from
uniqueness of minimal left almost-split maps in `mod(A/AeA)`. -/
theorem sourceLabel_injective [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (he : IsIdempotentElem e) :
    Function.Injective
      (sourceLabel (S := S) (D := D) H he) := by
  intro N N' hsource
  letI : IsNoetherianRing
      (RightModule.primitiveQuotientAlgebra e)ᵐᵒᵖ :=
    IsNoetherianRing.of_finite k _
  let C := RightModule.PrimitiveQuotientSubcategory e
  letI : HasFiniteProducts C :=
    ⟨fun _ ↦ CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
      (RightModule.primitiveQuotientEquivalence (k := k) e).functor⟩
  letI : Abelian C := CategoryTheory.abelianOfEquivalence
    (RightModule.primitiveQuotientEquivalence (k := k) e).functor
  let T := N.quotientShortComplex
  let T' := N'.quotientShortComplex
  have hsourceLabel : N.sourceAmbientLabel H he =
      N'.sourceAmbientLabel H he :=
    congrArg Subtype.val hsource
  let eSourceAmbient : N.sourceModule ≅ N'.sourceModule :=
    (N.sourceIso H he).trans
      ((eqToIso (congrArg S.fgObj hsourceLabel)).trans
        (N'.sourceIso H he).symm)
  let eSource : T.X₁ ≅ T'.X₁ :=
    ObjectProperty.isoMk _ eSourceAmbient
  have hf := N.quotientShortComplex_f_minimalLeftAlmostSplit H he
  have hf' := N'.quotientShortComplex_f_minimalLeftAlmostSplit H he
  have hf'AS : IsLeftAlmostSplit (eSource.hom ≫ T'.f) :=
    hf'.1.precomp_iso eSource
  have hf'Min : IsLeftMinimal (eSource.hom ≫ T'.f) :=
    hf'.2.precomp_iso eSource
  obtain ⟨eMiddle, heMiddle⟩ :=
    exists_leftAlmostSplit_middleIso hf.1 hf.2 hf'AS hf'Min
  let eC : cokernel T.f ≅ cokernel T'.f :=
    cokernel.mapIso T.f T'.f eSource eMiddle heMiddle
  have hT : T.ShortExact := N.quotientShortComplex_shortExact
  have hT' : T'.ShortExact := N'.quotientShortComplex_shortExact
  let eT : cokernel T.f ≅ T.X₃ :=
    colimit.isoColimitCocone {
      cocone := CokernelCofork.ofπ T.g T.zero
      isColimit := hT.gIsCokernel }
  let eT' : cokernel T'.f ≅ T'.X₃ :=
    colimit.isoColimitCocone {
      cocone := CokernelCofork.ofπ T'.g T'.zero
      isColimit := hT'.gIsCokernel }
  let eEndpoint : T.X₃ ≅ T'.X₃ := eT.symm.trans (eC.trans eT')
  have hlabel : N.label.1 = N'.label.1 :=
    S.fgObj_skeletal
      ⟨(RightModule.PrimitiveQuotientProperty e).ι.mapIso eEndpoint⟩
  cases N
  cases N'
  cases Subtype.ext hlabel
  rfl

/-- A primitive new-mesh endpoint is determined by its quotient label. -/
@[ext]
theorem ext {N N' : S.PrimitiveNewRightMeshEndpoint D}
    (h : N.label = N'.label) : N = N' := by
  cases N
  cases N'
  cases h
  rfl

/-- There are only finitely many primitive new-mesh endpoints. -/
noncomputable instance finite : Finite (S.PrimitiveNewRightMeshEndpoint D) :=
  Finite.of_injective PrimitiveNewRightMeshEndpoint.label fun _ _ h ↦ ext h

/-- A positive primitive new mesh, retaining the proof of its sign. -/
abbrev PositiveEndpoint :=
  {N : S.PrimitiveNewRightMeshEndpoint D // N.IsPositive}

end PrimitiveNewRightMeshEndpoint

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
