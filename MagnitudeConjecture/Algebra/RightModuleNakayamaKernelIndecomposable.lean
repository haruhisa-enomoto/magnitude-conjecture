import MagnitudeConjecture.Algebra.RightModuleAuslanderTranspose
import MagnitudeConjecture.Algebra.RightModuleAlmostSplitSocle

/-!
# Indecomposability of the Nakayama kernel

For a minimal two-step projective presentation of a Schur object, every
endomorphism of the associated Nakayama kernel is scalar modulo a morphism
factoring through an injective.  Minimality rules out injective summands, so
idempotents of the kernel are trivial.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ] [IsAlgClosed k]

/-- A morphism of finite modules factors through an injective finite
module. -/
structure FactorsThroughInjective
    {U V : FGModuleCat.{u} Bᵐᵒᵖ} (f : U ⟶ V) where
  middle : FGModuleCat.{u} Bᵐᵒᵖ
  injective : Injective middle
  left : U ⟶ middle
  right : middle ⟶ V
  fac : left ≫ right = f

omit [IsNoetherianRing Bᵐᵒᵖ] in
/-- An idempotent which factors through an injective has injective image.
If every injective retract of its source is zero, the idempotent vanishes. -/
theorem idempotent_eq_zero_of_factorsThroughInjective
    {T : FGModuleCat.{u} Bᵐᵒᵖ} (a : T ⟶ T)
    (haa : a ≫ a = a)
    (hfac : Nonempty (FactorsThroughInjective a))
    (hzero : ∀ {I : FGModuleCat.{u} Bᵐᵒᵖ} [Injective I],
      Retract I T → IsZero I) :
    a = 0 := by
  let U : FGModuleCat.{u} Bᵐᵒᵖ :=
    FGModuleCat.of Bᵐᵒᵖ (LinearMap.range a.hom.hom)
  let inc : U ⟶ T := FGModuleCat.ofHom (LinearMap.range a.hom.hom).subtype
  let proj : T ⟶ U := FGModuleCat.ofHom a.hom.hom.rangeRestrict
  have hincproj : inc ≫ proj = 𝟙 U := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change a.hom.hom x.1 = x.1
    rw [← hy]
    have hpoint := congrArg (fun f : T ⟶ T ↦ f.hom.hom y) haa
    simpa [LinearMap.comp_apply] using hpoint
  have hinca : inc ≫ a = inc := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, hy⟩ := x.property
    change a.hom.hom x.1 = x.1
    rw [← hy]
    have hpoint := congrArg (fun f : T ⟶ T ↦ f.hom.hom y) haa
    simpa [LinearMap.comp_apply] using hpoint
  let rUT : Retract U T :=
    { i := inc
      r := proj
      retract := hincproj }
  obtain ⟨F⟩ := hfac
  letI : Injective F.middle := F.injective
  let rUI : Retract U F.middle :=
    { i := inc ≫ F.left
      r := F.right ≫ proj
      retract := by
        rw [Category.assoc, ← Category.assoc F.left F.right proj,
          F.fac, ← Category.assoc, hinca, hincproj] }
  letI : Injective U := rUI.injective
  have hU : IsZero U := hzero rUT
  have hinczero : inc = 0 := hU.eq_of_src _ _
  calc
    a = proj ≫ inc := by
      apply FGModuleCat.hom_ext
      rfl
    _ = 0 := by rw [hinczero, comp_zero]

namespace TwoStepMinimalProjectivePresentation

variable {X : FGModuleCat.{u} Bᵐᵒᵖ}

/-- At a scalar-endomorphism endpoint, every endomorphism of the Nakayama
kernel differs from a scalar by a map through an injective. -/
theorem nakayamaKernel_endomorphism_factorsThroughInjective_sub_smul_id
    (P : TwoStepMinimalProjectivePresentation X)
    (hscalar : ∀ r : X ⟶ X, ∃ c : k, c • 𝟙 X = r)
    (a : P.nakayamaKernel (k := k) ⟶
      P.nakayamaKernel (k := k)) :
    ∃ c : k, Nonempty (FactorsThroughInjective (a - c • 𝟙 _)) := by
  let I₁ := RightModule.projectiveNakayamaFGObj (k := k)
    P.syzygyPresentation.p
  let I₀ := RightModule.projectiveNakayamaFGObj (k := k)
    P.augmentation.p
  let j : P.nakayamaKernel (k := k) ⟶ I₁ :=
    kernel.ι (P.nakayamaDifferential (k := k))
  let h : I₁ ⟶ I₀ := P.nakayamaDifferential (k := k)
  letI : Injective I₁ :=
    RightModule.projectiveNakayamaFGObj_injective
      (k := k) P.syzygyPresentation.p
  letI : Injective I₀ :=
    RightModule.projectiveNakayamaFGObj_injective
      (k := k) P.augmentation.p
  let A : I₁ ⟶ I₁ := Injective.factorThru (a ≫ j) j
  have hjA : j ≫ A = a ≫ j :=
    Injective.comp_factorThru (a ≫ j) j
  have hjAh : j ≫ (A ≫ h) = 0 := by
    rw [← Category.assoc, hjA, Category.assoc]
    change a ≫ (kernel.ι (P.nakayamaDifferential (k := k)) ≫
      P.nakayamaDifferential (k := k)) = 0
    rw [kernel.condition, comp_zero]
  let Cmap : P.nakayamaCokernel (k := k) ⟶ I₀ :=
    cokernel.desc j (A ≫ h) hjAh
  let Bmap : I₀ ⟶ I₀ :=
    Injective.factorThru Cmap (P.nakayamaCokernelι (k := k))
  have hιB : P.nakayamaCokernelι (k := k) ≫ Bmap = Cmap :=
    Injective.comp_factorThru Cmap (P.nakayamaCokernelι (k := k))
  have hAB : A ≫ h = h ≫ Bmap := by
    symm
    calc
      h ≫ Bmap =
          (P.nakayamaCokernelπ (k := k) ≫
            P.nakayamaCokernelι (k := k)) ≫ Bmap := by
              rw [P.nakayamaCokernelπ_comp_ι (k := k)]
      _ = P.nakayamaCokernelπ (k := k) ≫
          (P.nakayamaCokernelι (k := k) ≫ Bmap) := by
            rw [Category.assoc]
      _ = P.nakayamaCokernelπ (k := k) ≫ Cmap := by rw [hιB]
      _ = A ≫ h := cokernel.π_desc j (A ≫ h) hjAh
  let e₁ : P.syzygyPresentation.p ⟶ P.syzygyPresentation.p :=
    RightModule.projectiveNakayamaMapPreimage (k := k)
      P.syzygyPresentation.p P.syzygyPresentation.p A
  let e₀ : P.augmentation.p ⟶ P.augmentation.p :=
    RightModule.projectiveNakayamaMapPreimage (k := k)
      P.augmentation.p P.augmentation.p Bmap
  have hνe₁ : RightModule.projectiveNakayamaMap (k := k) e₁ = A :=
    RightModule.projectiveNakayamaMap_preimage (k := k)
      P.syzygyPresentation.p P.syzygyPresentation.p A
  have hνe₀ : RightModule.projectiveNakayamaMap (k := k) e₀ = Bmap :=
    RightModule.projectiveNakayamaMap_preimage (k := k)
      P.augmentation.p P.augmentation.p Bmap
  have hecomm : e₁ ≫ P.differential = P.differential ≫ e₀ := by
    apply RightModule.projectiveNakayamaMap_injective (k := k)
      P.syzygyPresentation.p P.augmentation.p
    change RightModule.projectiveNakayamaMap (k := k)
        (e₁ ≫ P.differential) =
      RightModule.projectiveNakayamaMap (k := k)
        (P.differential ≫ e₀)
    rw [RightModule.projectiveNakayamaMap_comp,
      RightModule.projectiveNakayamaMap_comp, hνe₁, hνe₀]
    exact hAB
  have hezero : P.differential ≫ (e₀ ≫ P.augmentation.f) = 0 := by
    rw [← Category.assoc, ← hecomm, Category.assoc,
      P.differential_comp_augmentation, comp_zero]
  letI : Epi P.presentationComplex.g := by
    dsimp only [presentationComplex]
    infer_instance
  let descended := CokernelCofork.IsColimit.desc'
    P.presentationComplex_exact.gIsCokernel
    (e₀ ≫ P.augmentation.f) hezero
  let f : X ⟶ X := descended.1
  have hpf : P.augmentation.f ≫ f = e₀ ≫ P.augmentation.f :=
    descended.2
  obtain ⟨c, hc⟩ := hscalar f
  let e₀diff : P.augmentation.p ⟶ P.augmentation.p :=
    e₀ - c • 𝟙 _
  have he₀diffzero : e₀diff ≫ P.augmentation.f = 0 := by
    dsimp only [e₀diff]
    rw [Preadditive.sub_comp, ← hpf]
    have hscalarcomp :
        (c • 𝟙 P.augmentation.p) ≫ P.augmentation.f =
          P.augmentation.f ≫ f := by
      rw [← hc]
      simp
    rw [hscalarcomp, sub_self]
  let kernelLift := KernelFork.IsLimit.lift'
    (kernelIsKernel P.augmentation.f) e₀diff he₀diffzero
  let r : P.augmentation.p ⟶ kernel P.augmentation.f := kernelLift.1
  have hr : r ≫ kernel.ι P.augmentation.f = e₀diff := kernelLift.2
  letI : Projective P.augmentation.p := P.augmentation.projective
  obtain ⟨t, ht⟩ := Projective.factors r P.syzygyPresentation.f
  have htd : t ≫ P.differential = e₀diff := by
    dsimp only [differential]
    rw [← Category.assoc, ht, hr]
  let Aprime : I₁ ⟶ I₁ := A - c • 𝟙 _
  let Bprime : I₀ ⟶ I₀ := Bmap - c • 𝟙 _
  have hAprime : Aprime ≫ h = h ≫ Bprime := by
    dsimp only [Aprime, Bprime]
    rw [Preadditive.sub_comp, Preadditive.comp_sub, hAB]
    simp
  have hνe₀diff :
      RightModule.projectiveNakayamaMap (k := k) e₀diff = Bprime := by
    dsimp only [e₀diff, Bprime]
    rw [RightModule.projectiveNakayamaMap_sub, hνe₀,
      RightModule.projectiveNakayamaMap_smul,
      RightModule.projectiveNakayamaMap_id]
  have hνtd :
      RightModule.projectiveNakayamaMap (k := k) t ≫ h = Bprime := by
    change RightModule.projectiveNakayamaMap (k := k) t ≫
      RightModule.projectiveNakayamaMap (k := k) P.differential = Bprime
    rw [← RightModule.projectiveNakayamaMap_comp]
    rw [htd, hνe₀diff]
  let L : I₁ ⟶ I₁ :=
    Aprime - h ≫ RightModule.projectiveNakayamaMap (k := k) t
  have hLzero : L ≫ h = 0 := by
    dsimp only [L]
    rw [Preadditive.sub_comp, Category.assoc, hνtd, hAprime, sub_self]
  let b : I₁ ⟶ P.nakayamaKernel (k := k) :=
    kernel.lift h L hLzero
  refine ⟨c, ⟨
    { middle := I₁
      injective := inferInstance
      left := j
      right := b
      fac := ?_ }⟩⟩
  apply (cancel_mono j).1
  dsimp only [b]
  rw [Category.assoc, kernel.lift_ι]
  dsimp only [L, Aprime]
  rw [Preadditive.comp_sub, Preadditive.comp_sub, hjA]
  change a ≫ j - c • j -
      (j ≫ h) ≫ RightModule.projectiveNakayamaMap (k := k) t =
    (a - c • 𝟙 _) ≫ j
  rw [show j ≫ h = 0 by exact kernel.condition _]
  simp [Preadditive.sub_comp]

/-- The Nakayama kernel of a minimal presentation of a nonprojective
indecomposable object is nonzero. -/
theorem nakayamaKernel_nontrivial
    [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (P : TwoStepMinimalProjectivePresentation X)
    (hX : ¬ Projective X)
    (hXind : Indecomposable X) :
    Nontrivial (P.nakayamaKernel (k := k)) := by
  let T := P.nakayamaKernel (k := k)
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  letI : Subsingleton T := hsub
  have hTzero : IsZero T := by
    refine
      { unique_to := fun Y ↦ ⟨⟨⟨0⟩, ?_⟩⟩
        unique_from := fun Y ↦ ⟨⟨⟨0⟩, ?_⟩⟩ }
    · intro f
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx]
      simp
    · intro f
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      exact Subsingleton.elim _ _
  apply P.stableSocleClass_ne_zero (k := k) hX hXind
  letI : IsZero T := hTzero
  letI : Injective T := hTzero.injective
  exact Ext.eq_zero_of_injective _

/-- The Nakayama kernel of a minimal presentation of a nonprojective Schur
object is indecomposable. -/
theorem nakayamaKernel_isIndecomposableModule
    [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (P : TwoStepMinimalProjectivePresentation X)
    (hX : ¬ Projective X)
    (hXind : Indecomposable X)
    (hscalar : ∀ r : X ⟶ X, ∃ c : k, c • 𝟙 X = r) :
    QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
      Bᵐᵒᵖ (P.nakayamaKernel (k := k)) := by
  let T := P.nakayamaKernel (k := k)
  have hTnontrivial : Nontrivial T :=
    P.nakayamaKernel_nontrivial (k := k) hX hXind
  have hTnoninjective : ¬ Injective T := by
    intro hTin
    letI : Injective T := hTin
    have hTzero := P.nakayamaKernel_isZero_of_injective_retract
      (k := k) (Retract.refl T)
    apply (not_subsingleton_iff_nontrivial.mpr hTnontrivial)
    constructor
    intro x y
    have hid : (𝟙 T) = 0 := (IsZero.iff_id_eq_zero T).mp hTzero
    have hx := congrArg (fun f : T ⟶ T ↦ f.hom.hom x) hid
    have hy := congrArg (fun f : T ⟶ T ↦ f.hom.hom y) hid
    simpa using hx.trans hy.symm
  rw [Foundation.isIndecomposableModule_iff_nontrivial_and_forall_isIdempotentElem]
  refine ⟨hTnontrivial, ?_⟩
  intro p hp
  let a : T ⟶ T := FGModuleCat.ofHom p
  have haa : a ≫ a = a := by
    apply FGModuleCat.hom_ext
    exact hp
  obtain ⟨c, hfac⟩ :=
    P.nakayamaKernel_endomorphism_factorsThroughInjective_sub_smul_id
      (k := k) hscalar a
  obtain ⟨F⟩ := hfac
  let r : T ⟶ T := a - c • 𝟙 T
  have hFr : F.left ≫ F.right = r := F.fac
  have hscalarFac :
      Nonempty (FactorsThroughInjective
        ((c * c - c) • 𝟙 T)) := by
    refine ⟨
      { middle := F.middle
        injective := F.injective
        left := F.left
        right := (1 - c) • F.right - F.right ≫ a
        fac := ?_ }⟩
    rw [Preadditive.comp_sub, Linear.comp_smul, ← Category.assoc, hFr]
    dsimp only [r]
    rw [Preadditive.sub_comp, haa, Linear.smul_comp, Category.id_comp]
    simp only [smul_sub, smul_smul]
    module
  have hcc : c * c - c = 0 := by
    by_contra hne
    obtain ⟨G⟩ := hscalarFac
    let left' : T ⟶ G.middle := (c * c - c)⁻¹ • G.left
    have hleft' : left' ≫ G.right = 𝟙 T := by
      dsimp only [left']
      rw [Linear.smul_comp, G.fac]
      simp [hne]
    letI : Injective G.middle := G.injective
    let rTG : Retract T G.middle :=
      { i := left'
        r := G.right
        retract := hleft' }
    exact hTnoninjective rTG.injective
  have hc : c = 0 ∨ c = 1 := by
    have hmul : c * (c - 1) = 0 := by
      calc
        c * (c - 1) = c * c - c := by ring
        _ = 0 := hcc
    rcases mul_eq_zero.mp hmul with hc0 | hc1
    · exact Or.inl hc0
    · exact Or.inr (sub_eq_zero.mp hc1)
  rcases hc with rfl | rfl
  · have hafac : Nonempty (FactorsThroughInjective a) := by
      refine ⟨
        { middle := F.middle
          injective := F.injective
          left := F.left
          right := F.right
          fac := ?_ }⟩
      simpa only [zero_smul, sub_zero] using F.fac
    have hazero := idempotent_eq_zero_of_factorsThroughInjective
      (a := a) haa hafac (fun rI ↦
        P.nakayamaKernel_isZero_of_injective_retract (k := k) rI)
    exact Or.inl (by
      apply LinearMap.ext
      intro x
      have hx := congrArg (fun f : T ⟶ T ↦ f.hom.hom x) hazero
      exact hx)
  · let b : T ⟶ T := 𝟙 T - a
    have hbb : b ≫ b = b := by
      dsimp only [b]
      rw [Preadditive.sub_comp, Preadditive.comp_sub,
        Preadditive.comp_sub, haa, Category.id_comp, Category.comp_id]
      abel
    have hbfac : Nonempty (FactorsThroughInjective b) := by
      refine ⟨
        { middle := F.middle
          injective := F.injective
          left := -F.left
          right := F.right
          fac := ?_ }⟩
      rw [Preadditive.neg_comp, F.fac]
      dsimp only [b]
      change -(a - 1 • 𝟙 T) = 𝟙 T - a
      simp
    have hbzero := idempotent_eq_zero_of_factorsThroughInjective
      (a := b) hbb hbfac (fun rI ↦
        P.nakayamaKernel_isZero_of_injective_retract (k := k) rI)
    have haid : a = 𝟙 T := by
      apply sub_eq_zero.mp
      simpa [b] using congrArg Neg.neg hbzero
    exact Or.inr (by
      apply LinearMap.ext
      intro x
      have hx := congrArg (fun f : T ⟶ T ↦ f.hom.hom x) haid
      exact hx)

/-- A right almost-split realization with indecomposable Nakayama kernel is
already right minimal, by comparison with any minimal right almost-split map
to the same endpoint. -/
theorem stableSocleClass_realization_isRightMinimal
    [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (P : TwoStepMinimalProjectivePresentation X)
    (hTind :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Bᵐᵒᵖ (P.nakayamaKernel (k := k)))
    {E : FGModuleCat.{u} Bᵐᵒᵖ}
    (i : P.nakayamaKernel (k := k) ⟶ E) (q : E ⟶ X)
    (zero : i ≫ q = 0)
    (hS : (ShortComplex.mk i q zero).ShortExact)
    (hqAS : IsRightAlmostSplit q)
    {M : FGModuleCat.{u} Bᵐᵒᵖ} (m : M ⟶ X)
    (hmAS : IsRightAlmostSplit m) (hmMin : IsRightMinimal m) :
    IsRightMinimal q := by
  let T := P.nakayamaKernel (k := k)
  obtain ⟨r, hr⟩ := hmAS.factors q hqAS.not_isSplitEpi
  obtain ⟨s, hs⟩ := hqAS.factors m hmAS.not_isSplitEpi
  have hsr : (s ≫ r) ≫ m = m := by
    rw [Category.assoc, hr, hs]
  letI : IsIso (s ≫ r) := hmMin (s ≫ r) hsr
  have hinvm : inv (s ≫ r) ≫ m = m := by
    apply (cancel_epi (s ≫ r)).1
    rw [IsIso.hom_inv_id_assoc, hsr]
  let s' : M ⟶ E := inv (s ≫ r) ≫ s
  have hs'r : s' ≫ r = 𝟙 M := by
    dsimp only [s']
    rw [Category.assoc, IsIso.inv_hom_id]
  have hs'q : s' ≫ q = m := by
    dsimp only [s']
    rw [Category.assoc, hs, hinvm]
  let p : E ⟶ E := r ≫ s'
  have hpp : p ≫ p = p := by
    dsimp only [p]
    rw [Category.assoc, ← Category.assoc s' r s', hs'r,
      Category.id_comp]
  have hpq : p ≫ q = q := by
    dsimp only [p]
    rw [Category.assoc, hs'q, hr]
  let u : E ⟶ E := 𝟙 E - p
  have huu : u ≫ u = u := by
    dsimp only [u]
    rw [Preadditive.sub_comp, Preadditive.comp_sub,
      Preadditive.comp_sub, hpp, Category.id_comp, Category.comp_id]
    abel
  have huq : u ≫ q = 0 := by
    dsimp only [u]
    rw [Preadditive.sub_comp, Category.id_comp, hpq, sub_self]
  letI : Mono i := hS.mono_f
  let lifted := KernelFork.IsLimit.lift' hS.fIsKernel u huq
  let v : E ⟶ T := lifted.1
  have hv : v ≫ i = u := lifted.2
  have huv : u ≫ v = v := by
    apply (cancel_mono i).1
    rw [Category.assoc, hv, huu]
  let a : T ⟶ T := i ≫ v
  have haa : a ≫ a = a := by
    dsimp only [a]
    rw [Category.assoc, ← Category.assoc v i v, hv, huv]
  have haModule : IsIdempotentElem a.hom.hom := by
    exact congrArg (fun f : T ⟶ T ↦ f.hom.hom) haa
  rcases hTind.eq_zero_or_eq_one_of_isIdempotentElem haModule with
      ha0 | ha1
  · have hacat : a = 0 := by
      apply FGModuleCat.hom_ext
      exact ha0
    have hu2zero : u ≫ u = 0 := by
      rw [← hv, Category.assoc]
      change v ≫ a ≫ i = 0
      simp [hacat]
    have huzero : u = 0 := by rw [← huu, hu2zero]
    have hpid : p = 𝟙 E := by
      exact (sub_eq_zero.mp (show 𝟙 E - p = 0 from huzero)).symm
    let er : E ≅ M :=
      { hom := r
        inv := s'
        hom_inv_id := hpid
        inv_hom_id := hs'r }
    letI : IsSplitMono r := by
      exact IsSplitMono.mk' { retraction := s', id := hpid }
    rw [← hr]
    exact hmMin.precomp_splitMono r
  · have hacat : a = 𝟙 T := by
      apply FGModuleCat.hom_ext
      exact ha1
    have hiSplit : IsSplitMono i :=
      IsSplitMono.mk' { retraction := v, id := hacat }
    exfalso
    apply (hqAS.not_isSplitEpi)
    letI : IsSplitMono i := hiSplit
    letI : Epi q := hS.epi_g
    let splitting := ShortComplex.Splitting.ofExactOfRetraction
      (ShortComplex.mk i q zero) hS.exact v hacat inferInstance
    exact splitting.isSplitEpi_g

/-- The kernel of a stable-socle realization is the kernel of every minimal
right almost-split map to the same endpoint. -/
theorem nonempty_nakayamaKernelIso_kernel_of_minimalRightAlmostSplit
    [HasExt.{u} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (P : TwoStepMinimalProjectivePresentation X)
    (hTind :
      QuotientSubmoduleEquidistribution.Foundation.IsIndecomposableModule
        Bᵐᵒᵖ (P.nakayamaKernel (k := k)))
    {E : FGModuleCat.{u} Bᵐᵒᵖ}
    (i : P.nakayamaKernel (k := k) ⟶ E) (q : E ⟶ X)
    (zero : i ≫ q = 0)
    (hS : (ShortComplex.mk i q zero).ShortExact)
    (hqAS : IsRightAlmostSplit q)
    {M : FGModuleCat.{u} Bᵐᵒᵖ} (m : M ⟶ X)
    (hmAS : IsRightAlmostSplit m) (hmMin : IsRightMinimal m) :
    Nonempty (P.nakayamaKernel (k := k) ≅ kernel m) := by
  have hqMin := P.stableSocleClass_realization_isRightMinimal
    (k := k) hTind i q zero hS hqAS m hmAS hmMin
  obtain ⟨ek⟩ := nonempty_kernelIso_of_rightAlmostSplit
    hqAS hqMin hmAS hmMin
  let ei : P.nakayamaKernel (k := k) ≅ kernel q :=
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel q) hS.fIsKernel).symm
  exact ⟨ei.trans ek⟩

end TwoStepMinimalProjectivePresentation

end MagnitudeConjecture
