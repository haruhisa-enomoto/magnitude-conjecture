import MagnitudeConjecture.Algebra.RightModuleSimpleTop
import MagnitudeConjecture.CategoryTheory.FGExtRealization
import MagnitudeConjecture.CategoryTheory.ProjectiveDimensionBiproduct

/-!
# Minimal realizations for weak positivity

Every nonnegative projective-coordinate vector has a module realization.
Among all realizations choose one with least endomorphism dimension.  Ringel's
endomorphism-drop lemma then forces the degree-one extensions between all
indecomposable summands of a minimal realization to vanish.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped BigOperators ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture

universe u v w

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- A short exact sequence with nonzero extension class cannot split at its
left map. -/
theorem not_isSplitMono_of_extClass_ne_zero
    {Q : ShortComplex C} (hQ : Q.ShortExact)
    (hne : hQ.extClass ≠ 0) :
    ¬ IsSplitMono Q.f := by
  intro hsplit
  letI : IsSplitMono Q.f := hsplit
  apply hne
  have hzero := hQ.extClass_comp_assoc
    (Ext.mk₀ (retraction Q.f)) (n' := 1) (h := rfl)
  rw [Ext.mk₀_comp_mk₀, IsSplitMono.id Q.f,
    Ext.comp_mk₀_id] at hzero
  exact hzero

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [HasFiniteBiproducts C]

/-- Pairwise vanishing of degree-one extensions between all summands implies
vanishing of the degree-one self-extension group of their finite biproduct. -/
theorem extOne_biproduct_eq_zero_of_pairwise
    {J : Type*} [Fintype J] (F : J → C)
    (hpair : ∀ i j (xi : Ext.{w} (F i) (F j) 1), xi = 0)
    (xi : Ext.{w} (⨁ F) (⨁ F) 1) :
    xi = 0 := by
  apply (Ext.biproductAddEquiv (biproduct.isBilimit F) (⨁ F) 1).injective
  funext i
  apply (Ext.addEquivBiproduct (F i) (biproduct.isBilimit F) 1).injective
  funext j
  simpa only [map_zero, Pi.zero_apply] using hpair i j
    ((Ext.addEquivBiproduct (F i) (biproduct.isBilimit F) 1)
      ((Ext.biproductAddEquiv (biproduct.isBilimit F) (⨁ F) 1) xi i) j)

end CategoryTheory

namespace RightModule.FiniteIndecomposableSkeleton

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k B)

/-- The two map-detection consequences of sincerity used in Ringel's cycle
proof.  They say that the chosen indecomposable detects every nonzero map out
of the standard injective cogenerator, and every nonzero map into a finite
projective. -/
structure SincereDetectionData (w : Fin S.n) : Prop where
  precomp_injectiveCogenerator :
    ∀ {T : FGModuleCat.{u} Bᵐᵒᵖ}
      (q : RightModule.injectiveCogeneratorFGObj (k := k) (B := B) ⟶ T),
      q ≠ 0 → ∃ y : Fin S.n,
        (∃ f : S.fgObj w ⟶ S.fgObj y, f ≠ 0) ∧
          ∃ g : S.fgObj y ⟶ T, g ≠ 0
  postcomp_projective :
    ∀ (P : FGModuleCat.{u} Bᵐᵒᵖ) [Projective P]
      {T : FGModuleCat.{u} Bᵐᵒᵖ} (i : T ⟶ P),
      i ≠ 0 → ∃ y : Fin S.n,
        (∃ f : T ⟶ S.fgObj y, f ≠ 0) ∧
          ∃ g : S.fgObj y ⟶ S.fgObj w, g ≠ 0

omit [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] in
/-- Endomorphism dimension is invariant under isomorphism. -/
theorem finrank_end_eq_of_iso
    {M N : FGModuleCat.{u} Bᵐᵒᵖ} (e : M ≅ N) :
    Module.finrank k (M ⟶ M) = Module.finrank k (N ⟶ N) :=
  (CategoryTheory.Linear.homCongr k e e).finrank_eq

/-- Every nonnegative coordinate vector has a realization with the least
possible endomorphism dimension among all its realizations. -/
theorem exists_projectiveVectorRealization_minimal_end
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (v : S.ProjectiveLabel → ℕ) :
    ∃ M : FGModuleCat.{u} Bᵐᵒᵖ,
      S.projectiveHomVectorFGObj M = (fun p ↦ (v p : ℤ)) ∧
      ∀ N : FGModuleCat.{u} Bᵐᵒᵖ,
        S.projectiveHomVectorFGObj N = (fun p ↦ (v p : ℤ)) →
          Module.finrank k (M ⟶ M) ≤ Module.finrank k (N ⟶ N) := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ M : FGModuleCat.{u} Bᵐᵒᵖ,
      S.projectiveHomVectorFGObj M = (fun p ↦ (v p : ℤ)) ∧
        Module.finrank k (M ⟶ M) = n
  have hP : ∃ n, P n := by
    refine ⟨Module.finrank k
      (S.projectiveVectorRealization v ⟶ S.projectiveVectorRealization v),
      S.projectiveVectorRealization v,
      S.projectiveHomVectorFGObj_projectiveVectorRealization H v, rfl⟩
  obtain ⟨M, hMvector, hMend⟩ := Nat.find_spec hP
  refine ⟨M, hMvector, fun N hNvector ↦ ?_⟩
  rw [hMend]
  exact Nat.find_min' hP ⟨N, hNvector, rfl⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Ringel 2.4(7), in the selected-skeleton form needed below: the existence
of a sincere directing indecomposable forces every selected indecomposable
to have projective dimension at most two. -/
theorem hasProjectiveDimensionLE_two_of_sincereDetection
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (w : Fin S.n) (D : S.SincereDetectionData w)
    (x : Fin S.n) :
    HasProjectiveDimensionLE (S.fgObj x) 2 := by
  classical
  letI : EnoughProjectives (FGModuleCat.{u} Bᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Bᵐᵒᵖ
  letI : HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  obtain ⟨P⟩ := twoStepMinimalProjectivePresentation_nonempty k
    (S.fgObj x)
  let Omega : FGModuleCat.{u} Bᵐᵒᵖ := kernel P.augmentation.f
  obtain ⟨n, label, ⟨e⟩⟩ := S.fgObj_decomposition Omega
  let F : Fin n → FGModuleCat.{u} Bᵐᵒᵖ :=
    fun t ↦ S.fgObj (label t)
  have hcomponent (t : Fin n) :
      HasProjectiveDimensionLE (F t) 1 := by
    by_cases ht : Projective (F t)
    · letI : Projective (F t) := ht
      infer_instance
    · let z : {z : Fin S.n // ¬ Projective (S.fgObj z)} :=
        ⟨label t, ht⟩
      obtain ⟨Q⟩ := twoStepMinimalProjectivePresentation_nonempty k
        (S.fgObj z.1)
      obtain ⟨eNak⟩ := S.rightTranslationIso_nakayamaKernel H z Q
      apply Q.hasProjectiveDimensionLE_one_of_nakayamaKernelIso_of_hom_eq_zero
        (k := k) eNak
      intro q
      by_contra hq
      obtain ⟨y, ⟨f, hf⟩, g, hg⟩ :=
        D.precomp_injectiveCogenerator q hq
      let i : F t ⟶ P.augmentation.p :=
        biproduct.ι F t ≫ e.inv ≫ kernel.ι P.augmentation.f
      have hi : i ≠ 0 := by
        haveI : Mono i := inferInstance
        intro hizero
        have hzero : IsZero (F t) := IsZero.of_mono_eq_zero i hizero
        exact (S.fgObj_indecomposable (label t)).1 hzero
      obtain ⟨p, ⟨a, ha⟩, b, hb⟩ :=
        D.postcomp_projective P.augmentation.p i hi
      let O := S.directedLinearOrder H
      have hwy : O.le w y :=
        S.directedLinearOrder_le_of_hom_ne_zero H f hf
      have hyt : O.le y (S.rightTranslationLabel z) :=
        S.directedLinearOrder_le_of_hom_ne_zero H g hg
      have htu : O.lt (S.rightTranslationLabel z) z.1 :=
        S.rightTranslation_strictly_precedes H z
      have hup : O.le z.1 p :=
        S.directedLinearOrder_le_of_hom_ne_zero H a ha
      have hpw : O.le p w :=
        S.directedLinearOrder_le_of_hom_ne_zero H b hb
      have hww : O.lt w w :=
        @lt_of_le_of_lt (Fin S.n) O.toPreorder _ _ _
          (@le_trans (Fin S.n) O.toPreorder _ _ _ hwy hyt)
          (@lt_of_lt_of_le (Fin S.n) O.toPreorder _ _ _ htu
            (@le_trans (Fin S.n) O.toPreorder _ _ _ hup hpw))
      exact (@lt_irrefl (Fin S.n) O.toPreorder w) hww
  have hBiprod : HasProjectiveDimensionLE (⨁ F) 1 :=
    MagnitudeConjecture.CategoryTheory.hasProjectiveDimensionLT_biproduct
      F 2 hcomponent
  have hOmega : HasProjectiveDimensionLE Omega 1 := by
    letI : HasProjectiveDimensionLE (⨁ F) 1 := hBiprod
    exact hasProjectiveDimensionLT_of_iso e.symm 2
  let Q : ShortComplex (FGModuleCat.{u} Bᵐᵒᵖ) :=
    ShortComplex.mk (kernel.ι P.augmentation.f) P.augmentation.f
      (kernel.condition P.augmentation.f)
  have hQ : Q.ShortExact := by
    letI : Epi P.augmentation.f := inferInstance
    exact
      { exact := ShortComplex.exact_kernel P.augmentation.f
        mono_f := inferInstance
        epi_g := inferInstance }
  exact hQ.hasProjectiveDimensionLT_X₃ 2 hOmega inferInstance

/-- The selected bound extends to every finitely generated module by its
finite indecomposable decomposition. -/
theorem hasProjectiveDimensionLE_two_fgObj_of_sincereDetection
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (w : Fin S.n) (D : S.SincereDetectionData w)
    (M : FGModuleCat.{u} Bᵐᵒᵖ) :
    HasProjectiveDimensionLE M 2 := by
  classical
  letI : EnoughProjectives (FGModuleCat.{u} Bᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Bᵐᵒᵖ
  letI : HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  obtain ⟨n, label, ⟨e⟩⟩ := S.fgObj_decomposition M
  let F : Fin n → FGModuleCat.{u} Bᵐᵒᵖ :=
    fun t ↦ S.fgObj (label t)
  have hcomponent (t : Fin n) :
      HasProjectiveDimensionLE (F t) 2 :=
    S.hasProjectiveDimensionLE_two_of_sincereDetection H w D (label t)
  have hBiprod : HasProjectiveDimensionLE (⨁ F) 2 :=
    MagnitudeConjecture.CategoryTheory.hasProjectiveDimensionLT_biproduct
      F 3 hcomponent
  letI : HasProjectiveDimensionLE (⨁ F) 2 := hBiprod
  exact hasProjectiveDimensionLT_of_iso e.symm 3

set_option maxHeartbeats 800000 in
/-- The indecomposable summands of an endomorphism-minimal realization have
no degree-one extensions between them.  A nonzero extension would replace
two summands by its middle term without changing the coordinate vector, but
would strictly lower the endomorphism dimension. -/
theorem extOne_decomposition_eq_zero_of_minimal_end
    [IsAlgClosed k]
    [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {M : FGModuleCat.{u} Bᵐᵒᵖ}
    (hminimal : ∀ N : FGModuleCat.{u} Bᵐᵒᵖ,
      S.projectiveHomVectorFGObj N = S.projectiveHomVectorFGObj M →
        Module.finrank k (M ⟶ M) ≤ Module.finrank k (N ⟶ N))
    {n : ℕ} (label : Fin n → Fin S.n)
    (e : M ≅ ⨁ fun t ↦ S.fgObj (label t))
    (i j : Fin n) (xi : Ext.{u}
      (S.fgObj (label i)) (S.fgObj (label j)) 1) :
    xi = 0 := by
  classical
  by_contra hxi
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hxi (S.extOne_self_eq_zero H (label i) xi)
  obtain ⟨E, a, b, zero, hQ, hclass⟩ :=
    FGExtRealization.exists_shortExact_with_extClass_eq
      (S.fgObj (label i)) (S.fgObj (label j)) xi
  let R : FGModuleCat.{u} Bᵐᵒᵖ :=
    ⨁ fun t : {t : Fin n // t ≠ j ∧ t ≠ i} ↦
      S.fgObj (label t.1)
  let N : FGModuleCat.{u} Bᵐᵒᵖ := E ⊞ R
  let epair : (⨁ fun t ↦ S.fgObj (label t)) ≅
      ((S.fgObj (label j) ⊞ S.fgObj (label i)) ⊞ R) :=
    MagnitudeConjecture.CategoryTheory.biproductIsoPairComplement
      (fun t ↦ S.fgObj (label t)) j i hij.symm
  have hNvector : S.projectiveHomVectorFGObj N =
      S.projectiveHomVectorFGObj M := by
    calc
      S.projectiveHomVectorFGObj N =
          S.projectiveHomVectorFGObj E +
            S.projectiveHomVectorFGObj R :=
        S.projectiveHomVectorFGObj_biprod E R
      _ = (S.projectiveHomVectorFGObj (S.fgObj (label j)) +
            S.projectiveHomVectorFGObj (S.fgObj (label i))) +
            S.projectiveHomVectorFGObj R := by
        rw [S.projectiveHomVectorFGObj_middle_eq_add hQ]
      _ = S.projectiveHomVectorFGObj
          ((S.fgObj (label j) ⊞ S.fgObj (label i)) ⊞ R) := by
        rw [S.projectiveHomVectorFGObj_biprod,
          S.projectiveHomVectorFGObj_biprod]
      _ = S.projectiveHomVectorFGObj
          (⨁ fun t ↦ S.fgObj (label t)) :=
        (S.projectiveHomVectorFGObj_iso epair).symm
      _ = S.projectiveHomVectorFGObj M :=
        (S.projectiveHomVectorFGObj_iso e).symm
  have hle : Module.finrank k (M ⟶ M) ≤
      Module.finrank k (N ⟶ N) := hminimal N hNvector
  have hclassne : hQ.extClass ≠ 0 := by
    rw [hclass]
    exact hxi
  have hnonsplit : ¬ IsSplitMono
      (ShortComplex.mk a b zero).f :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.not_isSplitMono_of_extClass_ne_zero
      (Q := ShortComplex.mk a b zero) hQ hclassne
  have hdrop :=
    MagnitudeConjecture.CategoryTheory.ShortComplex.ShortExact.finrank_end_middle_biprod_lt
      (k := k) hQ hnonsplit R
  have hlt : Module.finrank k (N ⟶ N) <
      Module.finrank k (M ⟶ M) := by
    rw [finrank_end_eq_of_iso (k := k) (e.trans epair)]
    exact hdrop
  exact (Nat.not_lt_of_ge hle hlt)

/-- Every nonnegative projective-coordinate vector has a finite realization
with vanishing degree-one self-extensions. -/
theorem exists_projectiveVectorRealization_extOne_self_eq_zero
    [IsAlgClosed k]
    [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (v : S.ProjectiveLabel → ℕ) :
    ∃ M : FGModuleCat.{u} Bᵐᵒᵖ,
      S.projectiveHomVectorFGObj M = (fun p ↦ (v p : ℤ)) ∧
      ∀ xi : Ext.{u} M M 1, xi = 0 := by
  classical
  obtain ⟨M, hMvector, hminimal⟩ :=
    S.exists_projectiveVectorRealization_minimal_end H v
  obtain ⟨n, label, ⟨e⟩⟩ := S.fgObj_decomposition M
  let F : Fin n → FGModuleCat.{u} Bᵐᵒᵖ :=
    fun t ↦ S.fgObj (label t)
  have hBvector : S.projectiveHomVectorFGObj (⨁ F) =
      (fun p ↦ (v p : ℤ)) := by
    rw [← hMvector]
    exact (S.projectiveHomVectorFGObj_iso e).symm
  have hminimalM : ∀ N : FGModuleCat.{u} Bᵐᵒᵖ,
      S.projectiveHomVectorFGObj N = S.projectiveHomVectorFGObj M →
        Module.finrank k (M ⟶ M) ≤ Module.finrank k (N ⟶ N) := by
    intro N hN
    exact hminimal N (hN.trans hMvector)
  refine ⟨⨁ F, hBvector, ?_⟩
  apply MagnitudeConjecture.CategoryTheory.extOne_biproduct_eq_zero_of_pairwise F
  intro i j xi
  exact S.extOne_decomposition_eq_zero_of_minimal_end H hminimalM
    label e i j xi

end RightModule.FiniteIndecomposableSkeleton

namespace LinearMap

variable {k : Type u} [Field k]
variable {E V₀ V₁ V₂ : Type v}
  [AddCommGroup E] [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module k E] [Module k V₀] [Module k V₁] [Module k V₂]
  [FiniteDimensional k E] [FiniteDimensional k V₀]
  [FiniteDimensional k V₁] [FiniteDimensional k V₂]

omit [FiniteDimensional k E] in
/-- The Euler characteristic of an exact four-term cochain beginning with
an injection is at least the dimension of its first term. -/
theorem finrank_le_alternating_of_exact_of_exact_of_injective
    (a : E →ₗ[k] V₀) (b : V₀ →ₗ[k] V₁) (c : V₁ →ₗ[k] V₂)
    (hab : Function.Exact a b) (hbc : Function.Exact b c)
    (ha : Function.Injective a) :
    (Module.finrank k E : ℤ) ≤
      (Module.finrank k V₀ : ℤ) - (Module.finrank k V₁ : ℤ) +
        (Module.finrank k V₂ : ℤ) := by
  have hkerb : b.ker = a.range := hab.linearMap_ker_eq
  have hkerc : c.ker = b.range := hbc.linearMap_ker_eq
  have harange : Module.finrank k a.range = Module.finrank k E :=
    (LinearEquiv.ofInjective a ha).finrank_eq.symm
  have hV₀ : Module.finrank k V₀ =
      Module.finrank k b.range + Module.finrank k E := by
    calc
      Module.finrank k V₀ =
          Module.finrank k b.range + Module.finrank k b.ker :=
        (b.finrank_range_add_finrank_ker).symm
      _ = _ := by rw [hkerb, harange]
  have hV₁ : Module.finrank k V₁ =
      Module.finrank k c.range + Module.finrank k b.range := by
    calc
      Module.finrank k V₁ =
          Module.finrank k c.range + Module.finrank k c.ker :=
        (c.finrank_range_add_finrank_ker).symm
      _ = _ := by rw [hkerc]
  have hc : Module.finrank k c.range ≤ Module.finrank k V₂ :=
    Submodule.finrank_le c.range
  omega

end LinearMap

namespace TwoStepMinimalProjectivePresentation

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable {X : FGModuleCat.{u} Bᵐᵒᵖ}

/-- If the presented module has projective dimension at most two, the kernel
of the chosen projective cover of its first syzygy is projective. -/
theorem syzygyPresentation_kernel_projective
    (P : TwoStepMinimalProjectivePresentation X)
    (hX : HasProjectiveDimensionLE X 2) :
    Projective (kernel P.syzygyPresentation.f) := by
  letI : EnoughProjectives (FGModuleCat.{u} Bᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Bᵐᵒᵖ
  letI : HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  let Omega : FGModuleCat.{u} Bᵐᵒᵖ := kernel P.augmentation.f
  let S0 : ShortComplex (FGModuleCat.{u} Bᵐᵒᵖ) :=
    ShortComplex.mk (kernel.ι P.augmentation.f) P.augmentation.f
      (kernel.condition P.augmentation.f)
  have hS0 : S0.ShortExact := by
    letI : Epi P.augmentation.f := inferInstance
    exact
      { exact := ShortComplex.exact_kernel P.augmentation.f
        mono_f := inferInstance
        epi_g := inferInstance }
  have hOmega : HasProjectiveDimensionLE Omega 1 :=
    hS0.hasProjectiveDimensionLT_X₁ 2 inferInstance hX
  let S1 : ShortComplex (FGModuleCat.{u} Bᵐᵒᵖ) :=
    ShortComplex.mk (kernel.ι P.syzygyPresentation.f)
      P.syzygyPresentation.f
      (kernel.condition P.syzygyPresentation.f)
  have hS1 : S1.ShortExact := by
    letI : Epi P.syzygyPresentation.f := inferInstance
    exact
      { exact := ShortComplex.exact_kernel P.syzygyPresentation.f
        mono_f := inferInstance
        epi_g := inferInstance }
  have hkernel : HasProjectiveDimensionLT
      (kernel P.syzygyPresentation.f) 1 :=
    hS1.hasProjectiveDimensionLT_X₁ 1 inferInstance hOmega
  letI : HasProjectiveDimensionLT
      (kernel P.syzygyPresentation.f) 1 := hkernel
  exact projective_iff_hasProjectiveDimensionLT_one.mpr hkernel

/-- Restriction along the kernel of the projective cover of the first
syzygy. -/
def syzygyKernelPrecompLinear
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    (P.syzygyPresentation.p ⟶ Y) →ₗ[k]
      (kernel P.syzygyPresentation.f ⟶ Y) :=
  CategoryTheory.Linear.leftComp k Y
    (kernel.ι P.syzygyPresentation.f)

omit [FiniteDimensional k B] in
/-- If `Ext¹(X,X)` vanishes, applying `Hom(-,X)` to the first three
projectives of the chosen resolution is exact at `Hom(P₁,X)`. -/
theorem differentialPrecomp_syzygyKernelPrecomp_exact_of_extOne_self_eq_zero
    [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (P : TwoStepMinimalProjectivePresentation X)
    (hext : ∀ xi : Ext.{u} X X 1, xi = 0) :
    Function.Exact
      (P.differentialPrecompLinear (k := k) X)
      (P.syzygyKernelPrecompLinear (k := k) X) := by
  let Omega : FGModuleCat.{u} Bᵐᵒᵖ := kernel P.augmentation.f
  let K : FGModuleCat.{u} Bᵐᵒᵖ := kernel P.syzygyPresentation.f
  let S0 : ShortComplex (FGModuleCat.{u} Bᵐᵒᵖ) :=
    ShortComplex.mk (kernel.ι P.augmentation.f) P.augmentation.f
      (kernel.condition P.augmentation.f)
  have hS0 : S0.ShortExact := by
    letI : Epi P.augmentation.f := inferInstance
    exact
      { exact := ShortComplex.exact_kernel P.augmentation.f
        mono_f := inferInstance
        epi_g := inferInstance }
  let S1 : ShortComplex (FGModuleCat.{u} Bᵐᵒᵖ) :=
    ShortComplex.mk (kernel.ι P.syzygyPresentation.f)
      P.syzygyPresentation.f
      (kernel.condition P.syzygyPresentation.f)
  have hS1 : S1.ShortExact := by
    letI : Epi P.syzygyPresentation.f := inferInstance
    exact
      { exact := ShortComplex.exact_kernel P.syzygyPresentation.f
        mono_f := inferInstance
        epi_g := inferInstance }
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro h hh
    rw [LinearMap.mem_ker] at hh
    have hhExt : (Ext.mk₀ S1.f).comp (Ext.mk₀ h) (zero_add 0) = 0 := by
      rw [Ext.mk₀_comp_mk₀]
      simpa [syzygyKernelPrecompLinear] using congrArg Ext.mk₀ hh
    obtain ⟨xOmega, hxOmega⟩ :=
      Ext.contravariant_sequence_exact₂ hS1 X (Ext.mk₀ h) hhExt
    have hboundary : hS0.extClass.comp xOmega rfl = 0 :=
      hext _
    obtain ⟨xP0, hxP0⟩ :=
      Ext.contravariant_sequence_exact₁ hS0 X xOmega rfl hboundary
    let g : P.augmentation.p ⟶ X := Ext.addEquiv₀ xP0
    refine ⟨g, ?_⟩
    apply (Ext.mk₀_bijective P.syzygyPresentation.p X).injective
    change Ext.mk₀ (P.differential ≫ g) = Ext.mk₀ h
    rw [← Ext.mk₀_comp_mk₀]
    rw [TwoStepMinimalProjectivePresentation.differential,
      ← Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_addEquiv₀_apply,
      hxP0, hxOmega]
  · rintro h ⟨g, hg⟩
    rw [LinearMap.mem_ker]
    change kernel.ι P.syzygyPresentation.f ≫ h = 0
    rw [← hg]
    change kernel.ι P.syzygyPresentation.f ≫
      (P.differential ≫ g) = 0
    rw [← Category.assoc]
    simp [TwoStepMinimalProjectivePresentation.differential]

end TwoStepMinimalProjectivePresentation

namespace RightModule.FiniteIndecomposableSkeleton

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k B)

/-- For a module of projective dimension at most two with vanishing
`Ext¹(M,M)`, its inverse-Cartan quadratic value is at least the dimension of
its endomorphism space. -/
theorem finrank_end_le_quadraticForm_projectiveHomVectorFGObj
    [IsAlgClosed k]
    [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    {M : FGModuleCat.{u} Bᵐᵒᵖ}
    (P : TwoStepMinimalProjectivePresentation M)
    (hpd : HasProjectiveDimensionLE M 2)
    (hext : ∀ xi : Ext.{u} M M 1, xi = 0) :
    (Module.finrank k (M ⟶ M) : ℤ) ≤
      CartanCoordinate.quadraticForm S.projectiveCartanInverse
        (S.projectiveHomVectorFGObj M) := by
  let K : FGModuleCat.{u} Bᵐᵒᵖ :=
    kernel P.syzygyPresentation.f
  let Omega : FGModuleCat.{u} Bᵐᵒᵖ :=
    kernel P.augmentation.f
  letI : Projective K :=
    P.syzygyPresentation_kernel_projective hpd
  let S0 : ShortComplex (FGModuleCat.{u} Bᵐᵒᵖ) :=
    ShortComplex.mk (kernel.ι P.augmentation.f) P.augmentation.f
      (kernel.condition P.augmentation.f)
  have hS0 : S0.ShortExact := by
    letI : Epi P.augmentation.f := inferInstance
    exact
      { exact := ShortComplex.exact_kernel P.augmentation.f
        mono_f := inferInstance
        epi_g := inferInstance }
  let S1 : ShortComplex (FGModuleCat.{u} Bᵐᵒᵖ) :=
    ShortComplex.mk (kernel.ι P.syzygyPresentation.f)
      P.syzygyPresentation.f
      (kernel.condition P.syzygyPresentation.f)
  have hS1 : S1.ShortExact := by
    letI : Epi P.syzygyPresentation.f := inferInstance
    exact
      { exact := ShortComplex.exact_kernel P.syzygyPresentation.f
        mono_f := inferInstance
        epi_g := inferInstance }
  have hP0vector : S.projectiveHomVectorFGObj P.augmentation.p =
      S.projectiveHomVectorFGObj Omega +
        S.projectiveHomVectorFGObj M :=
    S.projectiveHomVectorFGObj_middle_eq_add hS0
  have hP1vector : S.projectiveHomVectorFGObj P.syzygyPresentation.p =
      S.projectiveHomVectorFGObj K +
        S.projectiveHomVectorFGObj Omega :=
    S.projectiveHomVectorFGObj_middle_eq_add hS1
  have hMvector : S.projectiveHomVectorFGObj M =
      S.projectiveHomVectorFGObj P.augmentation.p -
        S.projectiveHomVectorFGObj P.syzygyPresentation.p +
          S.projectiveHomVectorFGObj K := by
    rw [hP0vector, hP1vector]
    abel
  have hquadratic :
      CartanCoordinate.quadraticForm S.projectiveCartanInverse
          (S.projectiveHomVectorFGObj M) =
        (Module.finrank k (P.augmentation.p ⟶ M) : ℤ) -
          (Module.finrank k (P.syzygyPresentation.p ⟶ M) : ℤ) +
            (Module.finrank k (K ⟶ M) : ℤ) := by
    unfold CartanCoordinate.quadraticForm
    calc
      S.projectiveHomVectorFGObj M ⬝ᵥ
          S.projectiveCartanInverse.mulVec
            (S.projectiveHomVectorFGObj M) =
        S.projectiveHomVectorFGObj M ⬝ᵥ
          S.projectiveCartanInverse.mulVec
            (S.projectiveHomVectorFGObj P.augmentation.p -
              S.projectiveHomVectorFGObj P.syzygyPresentation.p +
                S.projectiveHomVectorFGObj K) :=
        congrArg (fun y ↦ S.projectiveHomVectorFGObj M ⬝ᵥ
          S.projectiveCartanInverse.mulVec y) hMvector
      _ = (S.projectiveHomVectorFGObj M ⬝ᵥ
              S.projectiveCartanInverse.mulVec
                (S.projectiveHomVectorFGObj P.augmentation.p)) -
            (S.projectiveHomVectorFGObj M ⬝ᵥ
              S.projectiveCartanInverse.mulVec
                (S.projectiveHomVectorFGObj P.syzygyPresentation.p)) +
            (S.projectiveHomVectorFGObj M ⬝ᵥ
              S.projectiveCartanInverse.mulVec
                (S.projectiveHomVectorFGObj K)) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_sub,
          dotProduct_add, dotProduct_sub]
      _ = _ := by
        rw [S.dotProduct_projectiveCartanInverse_mulVec_projectiveHomVectorFGObj
              H M P.augmentation.p,
          S.dotProduct_projectiveCartanInverse_mulVec_projectiveHomVectorFGObj
              H M P.syzygyPresentation.p,
          S.dotProduct_projectiveCartanInverse_mulVec_projectiveHomVectorFGObj
              H M K]
  let a := P.augmentationPrecompLinear (k := k) M
  let b := P.differentialPrecompLinear (k := k) M
  let c := P.syzygyKernelPrecompLinear (k := k) M
  have hab : Function.Exact a b := by
    rw [LinearMap.exact_iff]
    exact (P.range_augmentationPrecompLinear (k := k) M).symm
  have hbc : Function.Exact b c :=
    P.differentialPrecomp_syzygyKernelPrecomp_exact_of_extOne_self_eq_zero
      (k := k) hext
  have ha : Function.Injective a :=
    P.augmentationPrecompLinear_injective (k := k) M
  have hlinear :=
    MagnitudeConjecture.LinearMap.finrank_le_alternating_of_exact_of_exact_of_injective
      a b c hab hbc ha
  calc
    (Module.finrank k (M ⟶ M) : ℤ) ≤
        (Module.finrank k (P.augmentation.p ⟶ M) : ℤ) -
          (Module.finrank k (P.syzygyPresentation.p ⟶ M) : ℤ) +
            (Module.finrank k (K ⟶ M) : ℤ) := hlinear
    _ = _ := hquadratic.symm

/-- Ringel 2.4(9): the inverse-Cartan Euler quadratic form of a directed
finite module category with a sincere indecomposable is weakly positive. -/
theorem projectiveCartanInverse_weaklyPositive_of_sincereDetection
    [IsAlgClosed k]
    (H : S.HasAcyclicNonzeroNonisomorphisms)
    (w : Fin S.n) (D : S.SincereDetectionData w) :
    ∀ x,
      CartanCoordinate.IsPositive x →
        1 ≤ CartanCoordinate.quadraticForm
          S.projectiveCartanInverse x := by
  classical
  letI : EnoughProjectives (FGModuleCat.{u} Bᵐᵒᵖ) :=
    MagnitudeConjecture.fgModuleCat_enoughProjectives Bᵐᵒᵖ
  letI : HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ) :=
    CategoryTheory.hasExt_of_enoughProjectives _
  intro x hx
  let v : S.ProjectiveLabel → ℕ := fun p ↦ Int.toNat (x p)
  have hv (p : S.ProjectiveLabel) : (v p : ℤ) = x p := by
    exact Int.toNat_of_nonneg (hx.1 p)
  obtain ⟨M, hMvector, hext⟩ :=
    S.exists_projectiveVectorRealization_extOne_self_eq_zero H v
  have hvector : S.projectiveHomVectorFGObj M = x := by
    rw [hMvector]
    funext p
    exact hv p
  have hMnonzero : ¬ IsZero M := by
    intro hzero
    apply hx.2
    rw [← hvector]
    funext p
    change (Module.finrank k (S.fgObj p.label ⟶ M) : ℤ) = 0
    letI : Subsingleton (S.fgObj p.label ⟶ M) :=
      ⟨fun f g ↦ hzero.eq_of_tgt f g⟩
    exact_mod_cast Module.finrank_zero_of_subsingleton
  haveI : Nontrivial (M ⟶ M) :=
    ⟨⟨𝟙 M, 0, fun h ↦ hMnonzero ((IsZero.iff_id_eq_zero M).2 h)⟩⟩
  have hendpos : (1 : ℤ) ≤ (Module.finrank k (M ⟶ M) : ℤ) := by
    exact_mod_cast (Module.finrank_pos (R := k) (M := M ⟶ M))
  have hpd : HasProjectiveDimensionLE M 2 :=
    S.hasProjectiveDimensionLE_two_fgObj_of_sincereDetection H w D M
  obtain ⟨P⟩ := twoStepMinimalProjectivePresentation_nonempty k M
  have hbound :=
    S.finrank_end_le_quadraticForm_projectiveHomVectorFGObj H P hpd hext
  rw [hvector] at hbound
  exact hendpos.trans hbound

end RightModule.FiniteIndecomposableSkeleton

end MagnitudeConjecture
