import MagnitudeConjecture.Algebra.RightModuleNakayama
import MagnitudeConjecture.Algebra.RightModuleNakayamaKernelIndecomposable

/-!
# The Nakayama kernel is the support Auslander--Reiten translate

At a literal middle-support endpoint, directedness makes the endomorphism
ring scalar.  The stable-socle realization of the Nakayama kernel is therefore
minimal right almost split, so uniqueness identifies its kernel with the
selected support almost-split kernel.  This discharges the `DTr` identification
used in Ringel's projective-dimension-one argument.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]
variable {S : RightModule.FiniteIndecomposableSkeleton k A}

/-- Auslander--Reiten translation points strictly backwards in the directed
order. -/
theorem rightTranslation_strictly_precedes
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)}) :
    (S.directedLinearOrder H).lt (S.rightTranslationLabel z) z.1 := by
  let O := S.directedLinearOrder H
  let B := S.minimalRightAlmostSplitAt z.1
  let L := S.rightSequenceLeftDecomposition z
  obtain ⟨p, f, hf⟩ := S.exists_projectiveLabel_hom_ne_zero z.1
  have hpMiddle : p ∈ S.projectiveSupport B.middle :=
    (S.rightSequence_endpointSupport_subset_middle z).2 ⟨f, hf⟩
  rw [S.mem_projectiveSupport_rightMiddle_iff z.1 p] at hpMiddle
  obtain ⟨t, _ht⟩ := hpMiddle
  have hleft := S.directedLinearOrder_lt_of_irreducible H
      ⟨L.component S.almostSplitSkeleton t,
        L.component_irreducible S.almostSplitSkeleton t⟩
  have hright := S.directedLinearOrder_lt_of_irreducible H
      ⟨B.component S.almostSplitSkeleton t,
        B.component_irreducible S.almostSplitSkeleton t⟩
  exact (O.lt_iff_le_not_ge _ _).2
    ⟨O.le_trans _ _ _ hleft.1 hright.1, fun hback ↦
      hleft.2 (O.le_trans _ _ _ hright.1 hback)⟩

/-- Directedness rules out every morphism from a nonprojective endpoint to
its Auslander--Reiten translate. -/
theorem hom_to_rightTranslation_eq_zero
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (f : S.fgObj z.1 ⟶ S.fgObj (S.rightTranslationLabel z)) :
    f = 0 := by
  by_contra hf
  have hforward := S.directedLinearOrder_le_of_hom_ne_zero H f hf
  exact ((S.directedLinearOrder H).lt_iff_le_not_ge _ _).1
    (S.rightTranslation_strictly_precedes H z) |>.2 hforward

/-- If the Nakayama kernel of a minimal presentation is indecomposable, it
is the chosen Auslander--Reiten translate of any selected skeleton endpoint
isomorphic to the presented module. -/
theorem rightTranslationIso_nakayamaKernel_of_targetIso
    [IsAlgClosed k]
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    {X : FGModuleCat.{u} Aᵐᵒᵖ}
    (e : X ≅ S.fgObj z.1)
    (Q : TwoStepMinimalProjectivePresentation X)
    (hTind :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Aᵐᵒᵖ (Q.nakayamaKernel (k := k))) :
    Nonempty (S.fgObj (S.rightTranslationLabel z) ≅
      Q.nakayamaKernel (k := k)) := by
  let B := S.minimalRightAlmostSplitAt z.1
  letI : EnoughProjectives (FGModuleCat.{u} Aᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  have hXind : Indecomposable X :=
    (MagnitudeConjecture.CategoryTheory.indecomposable_iff_of_iso e).2
      (S.fgObj_indecomposable z.1)
  have hXnot : ¬ Projective X := by
    intro hX
    exact z.2 (Projective.of_iso e hX)
  obtain ⟨E, i, q, zero, hshort, _hclass, hqAS⟩ :=
    Q.exists_stableSocleClass_realization_rightAlmostSplit
      (k := k) hXnot hXind
  let m : B.middle ⟶ X := B.map ≫ e.inv
  have hmAS : IsRightAlmostSplit m :=
    B.rightAlmostSplit.postcomp_iso e.symm
  have hmMin : IsRightMinimal m :=
    IsRightMinimal.postcomp_iso e.symm B.rightMinimal
  obtain ⟨eQ⟩ :=
    Q.nonempty_nakayamaKernelIso_kernel_of_minimalRightAlmostSplit
      (k := k) hTind i q zero hshort hqAS m hmAS hmMin
  let eKernel : kernel B.map ≅ kernel m :=
    kernel.mapIso B.map m (Iso.refl B.middle) e.symm (by simp [m])
  exact ⟨(S.rightTranslationKernelIso z).symm.trans
    (eKernel.trans eQ.symm)⟩

/-- If the Nakayama kernel of a minimal presentation is indecomposable, it
is the chosen Auslander--Reiten translate of the endpoint. -/
theorem rightTranslationIso_nakayamaKernel_of_isIndecomposableModule
    [IsAlgClosed k]
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (Q : TwoStepMinimalProjectivePresentation (S.fgObj z.1))
    (hTind :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Aᵐᵒᵖ (Q.nakayamaKernel (k := k))) :
    Nonempty (S.fgObj (S.rightTranslationLabel z) ≅
      Q.nakayamaKernel (k := k)) := by
  exact S.rightTranslationIso_nakayamaKernel_of_targetIso z
    (Iso.refl _) Q hTind

/-- For any nonprojective vertex of a directed finite module skeleton, the
Nakayama kernel of a minimal two-step presentation is its chosen
Auslander--Reiten translate. -/
theorem rightTranslationIso_nakayamaKernel
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (Q : TwoStepMinimalProjectivePresentation (S.fgObj z.1)) :
    Nonempty (S.fgObj (S.rightTranslationLabel z) ≅
      Q.nakayamaKernel (k := k)) := by
  letI : EnoughProjectives (FGModuleCat.{u} Aᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Aᵐᵒᵖ
  letI : HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  have hscalar : ∀ r : S.fgObj z.1 ⟶ S.fgObj z.1,
      ∃ c : k, c • 𝟙 _ = r :=
    H.endomorphism_eq_smul_id S z.1
  have hTind := Q.nakayamaKernel_isIndecomposableModule
    (k := k) z.2 (S.fgObj_indecomposable z.1) hscalar
  exact S.rightTranslationIso_nakayamaKernel_of_isIndecomposableModule
    z Q hTind

/-- A nonzero degree-one extension into a noninjective selected module gives
a nonzero ordinary morphism from its inverse Auslander--Reiten translate.
This is the nonvanishing direction of stable Auslander--Reiten duality used
by the source-marker sign test. -/
theorem exists_nonzero_hom_inverseTranslation_of_extOne_ne_zero
    [IsAlgClosed k]
    [HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ)]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (x : {x : Fin S.n // ¬ Injective (S.fgObj x)})
    (Y : FGModuleCat.{u} Aᵐᵒᵖ)
    (xi : Ext.{u} Y (S.fgObj x.1) 1)
    (hxi : xi ≠ 0) :
    ∃ f : S.fgObj ((S.rightTranslationEquiv).symm x).1 ⟶ Y,
      f ≠ 0 := by
  let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
    (S.rightTranslationEquiv).symm x
  obtain ⟨P⟩ := twoStepMinimalProjectivePresentation_nonempty k
    (S.fgObj z.1)
  obtain ⟨eNak⟩ := S.rightTranslationIso_nakayamaKernel H z P
  let eSource : S.fgObj x.1 ≅ S.fgObj (S.rightTranslationLabel z) :=
    S.noninjectiveLeftSourceIso x
  let e : S.fgObj x.1 ≅ P.nakayamaKernel (k := k) :=
    eSource.trans eNak
  let xi' : Ext.{u} Y (P.nakayamaKernel (k := k)) 1 :=
    xi.comp (Ext.mk₀ e.hom) (add_zero 1)
  have hxi' : xi' ≠ 0 := by
    intro hzero
    apply hxi
    have hrecover := congrArg
      (fun eta : Ext.{u} Y (P.nakayamaKernel (k := k)) 1 ↦
        eta.comp (Ext.mk₀ e.inv) (add_zero 1)) hzero
    simpa [xi', Ext.comp_assoc_of_second_deg_zero] using hrecover
  let lambda := P.stableHomExtLinearEquiv (k := k) Y xi'
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hxi'
    apply (P.stableHomExtLinearEquiv (k := k) Y).injective
    rw [map_zero]
    exact hzero
  have hexists : ∃ a : RightModule.projectiveStableHom
      (k := k) (S.fgObj z.1) Y, lambda a ≠ 0 := by
    by_contra hall
    apply hlambda
    apply LinearMap.ext
    intro a
    have ha : lambda a = 0 :=
      not_ne_iff.mp ((not_exists.mp hall) a)
    exact ha
  obtain ⟨a, ha⟩ := hexists
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  refine ⟨f, ?_⟩
  intro hf
  apply ha
  rw [hf]
  simp [lambda]

/-- Every selected indecomposable over a directed algebra has vanishing
degree-one self-Ext.  For a noninjective object, rotate to the corresponding
right Auslander--Reiten sequence and use stable Hom--Ext duality together
with the absence of maps from its endpoint back to its translate. -/
theorem extOne_self_eq_zero
    [IsAlgClosed k]
    [HasExt.{u} (FGModuleCat.{u} Aᵐᵒᵖ)]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (x : Fin S.n)
    (xi : Ext.{u} (S.fgObj x) (S.fgObj x) 1) :
    xi = 0 := by
  by_cases hx : Injective (S.fgObj x)
  · letI : Injective (S.fgObj x) := hx
    exact Ext.eq_zero_of_injective xi
  · let xni : {x : Fin S.n // ¬ Injective (S.fgObj x)} := ⟨x, hx⟩
    let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
      (S.rightTranslationEquiv).symm xni
    obtain ⟨Q⟩ := twoStepMinimalProjectivePresentation_nonempty k
      (S.fgObj z.1)
    obtain ⟨eNak⟩ := S.rightTranslationIso_nakayamaKernel H z Q
    let eSource : S.fgObj x ≅ S.fgObj (S.rightTranslationLabel z) :=
      S.noninjectiveLeftSourceIso xni
    let e : S.fgObj x ≅ Q.nakayamaKernel (k := k) :=
      eSource.trans eNak
    let xi' : Ext.{u} (S.fgObj x) (Q.nakayamaKernel (k := k)) 1 :=
      xi.comp (Ext.mk₀ e.hom) (add_zero 1)
    have hstable : ∀ a : RightModule.projectiveStableHom
        (k := k) (S.fgObj z.1) (S.fgObj x), a = 0 := by
      intro a
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      have hf : f = 0 := by
        apply (cancel_mono eSource.hom).1
        simpa [eSource] using S.hom_to_rightTranslation_eq_zero H z
          (f ≫ eSource.hom)
      rw [hf]
      simp
    have hxi' : xi' = 0 := by
      apply (Q.stableHomExtLinearEquiv (k := k) (S.fgObj x)).injective
      apply LinearMap.ext
      intro a
      rw [hstable a]
      simp
    have hrecover := congrArg
      (fun eta : Ext.{u} (S.fgObj x) (Q.nakayamaKernel (k := k)) 1 ↦
        eta.comp (Ext.mk₀ e.inv) (add_zero 1)) hxi'
    simpa [xi', Ext.comp_assoc_of_second_deg_zero] using hrecover

namespace PrimitiveProjectivePresentation

variable (P : S.PrimitiveProjectivePresentation)

/-- For a minimal two-step presentation of a literal middle-support endpoint,
its Nakayama kernel is the kernel selected by the transported almost-split
sequence. -/
theorem rightSequenceSupportKernelIso_nakayamaKernel
    [IsAlgClosed k]
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (Q : TwoStepMinimalProjectivePresentation
      (P.rightSequenceSupportEndpointFGObj hA z)) :
    Nonempty (P.rightSequenceSupportKernelFGObj hA z ≅
      Q.nakayamaKernel (k := k)) := by
  let X := (S.minimalRightAlmostSplitAt z.1).middle
  let T := P.supportAlgebraSkeleton hA X
  let B := P.rightSequenceSupportMinimalRightAlmostSplitDecomposition hA z
  letI : EnoughProjectives
      (FGModuleCat.{u} (P.SupportAlgebra X)ᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives
      ((P.SupportAlgebra X)ᵐᵒᵖ)
  letI : HasExt.{u}
      (FGModuleCat.{u} (P.SupportAlgebra X)ᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  have hendpoint : ¬ Projective
      (P.rightSequenceSupportEndpointFGObj hA z) :=
    P.rightSequenceSupportTarget_not_projective hA z
  have hscalar : ∀ r :
      P.rightSequenceSupportEndpointFGObj hA z ⟶
        P.rightSequenceSupportEndpointFGObj hA z,
      ∃ c : k, c • 𝟙 _ = r := by
    exact
      (P.supportAlgebraSkeleton_hasAcyclicNonzeroNonisomorphisms H hA X
        |>.endomorphism_eq_smul_id
          T (P.rightSequenceSupportTargetLabel hA z))
  have hXind : Indecomposable
      (P.rightSequenceSupportEndpointFGObj hA z) :=
    T.fgObj_indecomposable (P.rightSequenceSupportTargetLabel hA z)
  have hTind := Q.nakayamaKernel_isIndecomposableModule
    (k := k) hendpoint hXind hscalar
  obtain ⟨E, i, q, zero, hshort, _hclass, hqAS⟩ :=
    Q.exists_stableSocleClass_realization_rightAlmostSplit
      (k := k) hendpoint hXind
  obtain ⟨eQ⟩ :=
    Q.nonempty_nakayamaKernelIso_kernel_of_minimalRightAlmostSplit
      (k := k) hTind i q zero hshort hqAS B.map
        B.rightAlmostSplit B.rightMinimal
  exact ⟨(P.rightSequenceSupportKernelIso hA z).symm.trans eQ.symm⟩

/-- Ringel's endpoint projective-dimension bound in the literal support
quotient, with the Nakayama/AR identification discharged internally. -/
theorem rightSequenceSupportEndpoint_hasProjectiveDimensionLE_one
    [IsAlgClosed k]
    (hA : RightModule.IsRepresentationFinite k A)
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (z : {z : Fin S.n // ¬ Projective (S.fgObj z)})
    (Q : TwoStepMinimalProjectivePresentation
      (P.rightSequenceSupportEndpointFGObj hA z)) :
    HasProjectiveDimensionLE
      (P.rightSequenceSupportEndpointFGObj hA z) 1 := by
  obtain ⟨e⟩ :=
    P.rightSequenceSupportKernelIso_nakayamaKernel hA H z Q
  apply
    P.rightSequenceSupportEndpoint_hasProjectiveDimensionLE_one_of_nakayamaKernelIso
      hA H z Q
  exact e

end PrimitiveProjectivePresentation

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
