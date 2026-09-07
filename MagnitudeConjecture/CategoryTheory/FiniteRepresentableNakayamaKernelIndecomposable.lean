import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleIndecomposable
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableAlmostSplitSocle
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaKernelMinimal
import MagnitudeConjecture.CategoryTheory.InjectiveStableHom
import QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitUniqueness

/-!
# Indecomposability of the finite-representable Nakayama kernel

For a minimal two-step presentation of an indecomposable endpoint, an
idempotent of the associated Nakayama kernel or its complement factors through
an injective. Minimality rules out injective retracts, so the kernel has only
trivial idempotents and is indecomposable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MagnitudeConjecture.InjectiveStable

namespace MagnitudeConjecture.CoveringHom
namespace TwoStepMinimalFiniteRepresentablePresentation

universe u v w

variable {k : Type v} [Field k]
variable [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable
  {hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
    (linearCoyonedaLinearModule (k := k) X)}
  (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
    (dualLinearYonedaLinearModule (k := k) X))
variable
  {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}

omit [IsAlgClosed k] in
/-- For an idempotent of the Nakayama kernel, either it or its complementary
idempotent factors through an injective.  Only indecomposability of the
endpoint is needed: the induced endpoint endomorphism is idempotent modulo
maps through projectives, and its local endomorphism ring decides which of it
and its complement is stably zero. -/
theorem nakayamaKernel_idempotent_factorsThroughInjective_or_complement
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hMind : Indecomposable M)
    (a : P.nakayamaKernel hI ⟶ P.nakayamaKernel hI)
    (haa : a ≫ a = a) :
    Nonempty (FactorsThroughInjective a) ∨
      Nonempty (FactorsThroughInjective (𝟙 _ - a)) := by
  let Q₁ :=
    P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject
  let Q₀ :=
    P.augmentation.toFiniteRepresentablePresentation.matrixObject
  let I₁ := (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q₁
  let I₀ := (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q₀
  let d : (finiteProjectiveRepresentableSumFunctor hP).obj Q₁ ⟶
      (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ :=
    P.toTwoStepFiniteRepresentablePresentation.differential
  let p : (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ ⟶ M :=
    P.augmentation.f
  let j : P.nakayamaKernel hI ⟶ I₁ :=
    kernel.ι (P.nakayamaDifferential hI)
  let h : I₁ ⟶ I₀ := P.nakayamaDifferential hI
  letI : Injective I₁ := finiteNakayamaRepresentableSum_injective hI Q₁
  letI : Injective I₀ := finiteNakayamaRepresentableSum_injective hI Q₀
  let A : I₁ ⟶ I₁ := Injective.factorThru (a ≫ j) j
  have hjA : j ≫ A = a ≫ j := Injective.comp_factorThru (a ≫ j) j
  have hjAh : j ≫ (A ≫ h) = 0 := by
    rw [← Category.assoc, hjA, Category.assoc]
    change a ≫ (kernel.ι (P.nakayamaDifferential hI) ≫
      P.nakayamaDifferential hI) = 0
    rw [kernel.condition, comp_zero]
  let Cmap : P.nakayamaCokernel hI ⟶ I₀ :=
    cokernel.desc j (A ≫ h) hjAh
  let Bmap : I₀ ⟶ I₀ :=
    Injective.factorThru Cmap (P.nakayamaCokernelι hI)
  have hιB : P.nakayamaCokernelι hI ≫ Bmap = Cmap :=
    Injective.comp_factorThru Cmap (P.nakayamaCokernelι hI)
  have hAB : A ≫ h = h ≫ Bmap := by
    symm
    calc
      h ≫ Bmap =
          (P.nakayamaCokernelπ hI ≫ P.nakayamaCokernelι hI) ≫ Bmap := by
            rw [P.nakayamaCokernelπ_comp_ι hI]
      _ = P.nakayamaCokernelπ hI ≫
          (P.nakayamaCokernelι hI ≫ Bmap) := by rw [Category.assoc]
      _ = P.nakayamaCokernelπ hI ≫ Cmap := by rw [hιB]
      _ = A ≫ h := cokernel.π_desc j (A ≫ h) hjAh
  let e₁ : (finiteProjectiveRepresentableSumFunctor hP).obj Q₁ ⟶
      (finiteProjectiveRepresentableSumFunctor hP).obj Q₁ :=
    finiteRepresentableNakayamaMapPreimage hP hI Q₁ Q₁ A
  let e₀ : (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ ⟶
      (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ :=
    finiteRepresentableNakayamaMapPreimage hP hI Q₀ Q₀ Bmap
  have hνe₁ : finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁ e₁ = A :=
    finiteRepresentableNakayamaMap_preimage hP hI Q₁ Q₁ A
  have hνe₀ : finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₀ e₀ = Bmap :=
    finiteRepresentableNakayamaMap_preimage hP hI Q₀ Q₀ Bmap
  have hνd : finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₀ d = h :=
    P.finiteRepresentableNakayamaMapLinearEquiv_differential hI
  have hecomm : e₁ ≫ d = d ≫ e₀ := by
    apply (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₀).injective
    rw [finiteRepresentableNakayamaMapLinearEquiv_comp, hνe₁, hνd,
      finiteRepresentableNakayamaMapLinearEquiv_comp, hνd, hνe₀, hAB]
  have hdaug : d ≫ p = 0 := by
    change (P.syzygyPresentation.f ≫ kernel.ι P.augmentation.f) ≫
      P.augmentation.f = 0
    rw [Category.assoc, kernel.condition, comp_zero]
  have hezero : d ≫ (e₀ ≫ p) = 0 := by
    calc
      d ≫ (e₀ ≫ p) = (d ≫ e₀) ≫ p :=
        Category.assoc _ _ _ |>.symm
      _ = (e₁ ≫ d) ≫ p := by rw [hecomm]
      _ = e₁ ≫ (d ≫ p) := Category.assoc _ _ _
      _ = 0 := by rw [hdaug, comp_zero]
  letI : Epi
      P.toTwoStepFiniteRepresentablePresentation.presentationComplex.g := by
    dsimp only [TwoStepFiniteRepresentablePresentation.presentationComplex]
    infer_instance
  let descended := CokernelCofork.IsColimit.desc'
    P.presentationComplex_exact.gIsCokernel (e₀ ≫ p) hezero
  let f : M ⟶ M := descended.1
  have hpf : p ≫ f = e₀ ≫ p := descended.2

  have hjAA : j ≫ (A ≫ A - A) = 0 := by
    calc
      j ≫ (A ≫ A - A) = (j ≫ A) ≫ A - j ≫ A := by
        rw [Preadditive.comp_sub, ← Category.assoc]
      _ = (a ≫ j) ≫ A - a ≫ j := by rw [hjA]
      _ = a ≫ (j ≫ A) - a ≫ j := by rw [Category.assoc]
      _ = a ≫ (a ≫ j) - a ≫ j := by rw [hjA]
      _ = (a ≫ a) ≫ j - a ≫ j := by rw [← Category.assoc]
      _ = 0 := by rw [haa, sub_self]
  let Cidem : P.nakayamaCokernel hI ⟶ I₁ :=
    cokernel.desc j (A ≫ A - A) hjAA
  let Rmap : I₀ ⟶ I₁ :=
    Injective.factorThru Cidem (P.nakayamaCokernelι hI)
  have hιR : P.nakayamaCokernelι hI ≫ Rmap = Cidem :=
    Injective.comp_factorThru Cidem (P.nakayamaCokernelι hI)
  have hhR : h ≫ Rmap = A ≫ A - A := by
    calc
      h ≫ Rmap =
          (P.nakayamaCokernelπ hI ≫ P.nakayamaCokernelι hI) ≫ Rmap := by
            rw [P.nakayamaCokernelπ_comp_ι hI]
      _ = P.nakayamaCokernelπ hI ≫
          (P.nakayamaCokernelι hI ≫ Rmap) := by rw [Category.assoc]
      _ = P.nakayamaCokernelπ hI ≫ Cidem := by rw [hιR]
      _ = A ≫ A - A := cokernel.π_desc j (A ≫ A - A) hjAA
  let t₀ : (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ ⟶
      (finiteProjectiveRepresentableSumFunctor hP).obj Q₁ :=
    finiteRepresentableNakayamaMapPreimage hP hI Q₀ Q₁ Rmap
  have hνt₀ : finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ t₀ =
      Rmap := finiteRepresentableNakayamaMap_preimage hP hI Q₀ Q₁ Rmap
  have he₁idem : e₁ ≫ e₁ - e₁ = d ≫ t₀ := by
    apply (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁).injective
    calc
      finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁
          (e₁ ≫ e₁ - e₁) =
          finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁ (e₁ ≫ e₁) -
            finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁ e₁ :=
        map_sub _ _ _
      _ =
          finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁ e₁ ≫
              finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁ e₁ -
            finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁ e₁ := by
        rw [finiteRepresentableNakayamaMapLinearEquiv_comp]
      _ = A ≫ A - A := by rw [hνe₁]
      _ = h ≫ Rmap := hhR.symm
      _ = finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₀ d ≫
          finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ t₀ := by
        rw [hνd, hνt₀]
      _ = finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁
          (d ≫ t₀) :=
        (finiteRepresentableNakayamaMapLinearEquiv_comp
          hP hI Q₁ Q₀ Q₁ d t₀).symm
  let r₀ : (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ ⟶
      (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ :=
    e₀ ≫ e₀ - e₀ - t₀ ≫ d
  have hd_e₀_sq : d ≫ (e₀ ≫ e₀) = (e₁ ≫ e₁) ≫ d := by
    calc
      d ≫ (e₀ ≫ e₀) = (d ≫ e₀) ≫ e₀ :=
        (Category.assoc d e₀ e₀).symm
      _ = (e₁ ≫ d) ≫ e₀ := by rw [hecomm]
      _ = e₁ ≫ (d ≫ e₀) := Category.assoc e₁ d e₀
      _ = e₁ ≫ (e₁ ≫ d) := by rw [← hecomm]
      _ = (e₁ ≫ e₁) ≫ d := (Category.assoc e₁ e₁ d).symm
  have hdr₀ : d ≫ r₀ = 0 := by
    dsimp only [r₀]
    rw [Preadditive.comp_sub, Preadditive.comp_sub, hd_e₀_sq, ← hecomm,
      ← Category.assoc d t₀ d, ← Preadditive.sub_comp, he₁idem, sub_self]
  let descendedR := CokernelCofork.IsColimit.desc'
    P.presentationComplex_exact.gIsCokernel r₀ hdr₀
  let s₀ : M ⟶ P.augmentation.source := descendedR.1
  have hps₀ : p ≫ s₀ = r₀ := descendedR.2
  have hr₀p : r₀ ≫ p = (e₀ ≫ e₀ - e₀) ≫ p := by
    have ht₀dp : (t₀ ≫ d) ≫ p = 0 := by
      rw [Category.assoc, hdaug, comp_zero]
    dsimp only [r₀]
    rw [Preadditive.sub_comp, ht₀dp, sub_zero]
  have hfidem : f ≫ f - f = s₀ ≫ p := by
    apply (cancel_epi p).1
    calc
      p ≫ (f ≫ f - f) =
          p ≫ (f ≫ f) - p ≫ f := by rw [Preadditive.comp_sub]
      _ = (p ≫ f) ≫ f - p ≫ f := by rw [← Category.assoc]
      _ = (e₀ ≫ p) ≫ f - e₀ ≫ p := by rw [hpf]
      _ = e₀ ≫ (p ≫ f) - e₀ ≫ p := by rw [Category.assoc]
      _ = e₀ ≫ (e₀ ≫ p) - e₀ ≫ p := by rw [hpf]
      _ = (e₀ ≫ e₀ - e₀) ≫ p := by
        rw [Preadditive.sub_comp, Category.assoc]
      _ = r₀ ≫ p := hr₀p.symm
      _ = p ≫ (s₀ ≫ p) := by rw [← Category.assoc, hps₀]
  let Fidem : ProjectiveStable.FactorsThroughProjective (f ≫ f - f) :=
    { middle := P.augmentation.source
      projective := inferInstance
      left := s₀
      right := p
      fac := hfidem.symm }

  have factorKernelOfFactorEndpoint (c : k)
      (Ff : Nonempty
        (ProjectiveStable.FactorsThroughProjective (f - c • 𝟙 M))) :
      Nonempty (FactorsThroughInjective (a - c • 𝟙 _)) := by
    obtain ⟨Ff⟩ := Ff
    letI : Projective Ff.middle := Ff.projective
    obtain ⟨sP, hsP⟩ := Projective.factors Ff.right p
    let pmap : (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ ⟶
        (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ :=
      p ≫ Ff.left ≫ sP
    have hpmap : pmap ≫ p = p ≫ (f - c • 𝟙 M) := by
      dsimp only [pmap]
      rw [Category.assoc, Category.assoc, hsP, Ff.fac]
    let e₀diff : (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ ⟶
        (finiteProjectiveRepresentableSumFunctor hP).obj Q₀ :=
      e₀ - c • 𝟙 _ - pmap
    have he₀diffzero : e₀diff ≫ p = 0 := by
      dsimp only [e₀diff]
      rw [Preadditive.sub_comp, Preadditive.sub_comp, hpmap, ← hpf,
        Linear.smul_comp, Category.id_comp, Preadditive.comp_sub,
        Linear.comp_smul, Category.comp_id]
      module
    let kernelLift := KernelFork.IsLimit.lift'
      (kernelIsKernel p) e₀diff he₀diffzero
    let r : P.augmentation.source ⟶ kernel p := kernelLift.1
    have hr : r ≫ kernel.ι p = e₀diff := kernelLift.2
    obtain ⟨t, ht⟩ := Projective.factors r P.syzygyPresentation.f
    have htd : t ≫ d = e₀diff := by
      change t ≫ (P.syzygyPresentation.f ≫ kernel.ι p) = e₀diff
      rw [← Category.assoc, ht, hr]
    let Aprime : I₁ ⟶ I₁ := A - c • 𝟙 _
    let Bprime : I₀ ⟶ I₀ := Bmap - c • 𝟙 _
    have hAprime : Aprime ≫ h = h ≫ Bprime := by
      dsimp only [Aprime, Bprime]
      rw [Preadditive.sub_comp, Preadditive.comp_sub, hAB]
      simp
    have hνid₀ : finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₀
        (𝟙 ((finiteProjectiveRepresentableSumFunctor hP).obj Q₀)) = 𝟙 I₀ :=
      finiteRepresentableNakayamaMapLinearEquiv_id hP hI Q₀
    have hνe₀diff :
        finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₀ e₀diff =
          Bprime - finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₀
            pmap := by
      dsimp only [e₀diff, Bprime]
      rw [map_sub, map_sub, hνe₀, map_smul, hνid₀]
    have hνtd : finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ t ≫
        h = Bprime - finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₀
          pmap := by
      rw [← hνd, ← finiteRepresentableNakayamaMapLinearEquiv_comp,
        htd, hνe₀diff]
    have hdpmap : d ≫ pmap = 0 := by
      dsimp only [pmap]
      rw [← Category.assoc, hdaug, zero_comp]
    have hνpzero : h ≫
        finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₀ pmap = 0 := by
      rw [← hνd, ← finiteRepresentableNakayamaMapLinearEquiv_comp,
        hdpmap, map_zero]
    let L : I₁ ⟶ I₁ :=
      Aprime - h ≫ finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ t
    have hLzero : L ≫ h = 0 := by
      calc
        L ≫ h = Aprime ≫ h -
            (h ≫ finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ t) ≫ h := by
          dsimp only [L]
          rw [Preadditive.sub_comp]
        _ = h ≫ Bprime - h ≫
            (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ t ≫ h) := by
          rw [hAprime, Category.assoc]
        _ = h ≫ Bprime - h ≫
            (Bprime - finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₀ pmap) := by
          rw [hνtd]
        _ = 0 := by
          have hcompBprime : h ≫
              (Bprime - finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₀ pmap) =
                h ≫ Bprime - h ≫
                  finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₀ pmap :=
            Preadditive.comp_sub _ _ _
          rw [hcompBprime, hνpzero, sub_zero, sub_self]
    let b : I₁ ⟶ P.nakayamaKernel hI := kernel.lift h L hLzero
    refine ⟨
      { middle := I₁
        injective := inferInstance
        left := j
        right := b
        fac := ?_ }⟩
    apply (cancel_mono j).1
    dsimp only [b]
    rw [Category.assoc, kernel.lift_ι]
    dsimp only [L, Aprime]
    rw [Preadditive.comp_sub, Preadditive.comp_sub, hjA]
    change a ≫ j - c • j -
        (j ≫ h) ≫ finiteRepresentableNakayamaMapLinearEquiv hP hI Q₀ Q₁ t =
      (a - c • 𝟙 _) ≫ j
    rw [show j ≫ h = 0 by exact kernel.condition _]
    simp [Preadditive.sub_comp]

  letI : IsLocalRing (End M) :=
    finiteDimensionalModule_end_isLocalRing k M hMind
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one
      (R := End M) (a := End.of f) (b := 1 - End.of f)
      (add_sub_cancel (End.of f) 1) with hfunit | hcompunit
  · right
    letI : IsIso f := (isUnit_iff_isIso f).1 hfunit
    have hfactor : Nonempty
        (ProjectiveStable.FactorsThroughProjective (𝟙 M - f)) := by
      refine ⟨
        { middle := Fidem.middle
          projective := Fidem.projective
          left := -Fidem.left
          right := Fidem.right ≫ inv f
          fac := ?_ }⟩
      calc
        (-Fidem.left) ≫ (Fidem.right ≫ inv f) =
            (-(Fidem.left ≫ Fidem.right)) ≫ inv f := by
          rw [← Category.assoc, Preadditive.neg_comp]
        _ = (-(f ≫ f - f)) ≫ inv f := by rw [Fidem.fac]
        _ = (f - f ≫ f) ≫ inv f := by
          congr 1
          abel
        _ = 𝟙 M - f := by
          have hdiff : f - f ≫ f = (𝟙 M - f) ≫ f := by
            rw [Preadditive.sub_comp, Category.id_comp]
          rw [hdiff]
          simp [Category.assoc]
    have hfactor' : Nonempty
        (ProjectiveStable.FactorsThroughProjective (f - (1 : k) • 𝟙 M)) := by
      obtain ⟨F⟩ := hfactor
      exact ⟨by simpa using F.smul (-1 : k)⟩
    obtain ⟨F⟩ := factorKernelOfFactorEndpoint (1 : k) hfactor'
    refine ⟨
      { middle := F.middle
        injective := F.injective
        left := -F.left
        right := F.right
        fac := ?_ }⟩
    rw [Preadditive.neg_comp, F.fac]
    simp
  · left
    have hcompunit' : IsUnit (End.of (𝟙 M - f)) := by
      simpa using hcompunit
    letI : IsIso (𝟙 M - f) :=
      (isUnit_iff_isIso (𝟙 M - f)).1 hcompunit'
    have hfactor : Nonempty
        (ProjectiveStable.FactorsThroughProjective f) := by
      refine ⟨
        { middle := Fidem.middle
          projective := Fidem.projective
          left := -Fidem.left
          right := Fidem.right ≫ inv (𝟙 M - f)
          fac := ?_ }⟩
      calc
        (-Fidem.left) ≫ (Fidem.right ≫ inv (𝟙 M - f)) =
            (-(Fidem.left ≫ Fidem.right)) ≫ inv (𝟙 M - f) := by
          rw [← Category.assoc, Preadditive.neg_comp]
        _ = (-(f ≫ f - f)) ≫ inv (𝟙 M - f) := by rw [Fidem.fac]
        _ = (f - f ≫ f) ≫ inv (𝟙 M - f) := by
          congr 1
          abel
        _ = f := by
          have hinvDiff : inv (𝟙 M - f) - f ≫ inv (𝟙 M - f) =
              (𝟙 M - f) ≫ inv (𝟙 M - f) := by
            rw [Preadditive.sub_comp, Category.id_comp]
          rw [Preadditive.sub_comp, Category.assoc f f (inv (𝟙 M - f)),
            ← Preadditive.comp_sub, hinvDiff]
          simp
    have hfactor' : Nonempty
        (ProjectiveStable.FactorsThroughProjective (f - (0 : k) • 𝟙 M)) := by
      simpa using hfactor
    simpa using factorKernelOfFactorEndpoint (0 : k) hfactor'

/-- The distinguished stable socle class prevents the Nakayama kernel from
being zero. -/
theorem nakayamaKernel_not_isZero
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M) :
    ¬ IsZero (P.nakayamaKernel hI) := by
  intro hzero
  apply P.stableSocleClass_ne_zero hI hM hMind
  letI : IsZero (P.nakayamaKernel hI) := hzero
  letI : Injective (P.nakayamaKernel hI) := hzero.injective
  exact Ext.eq_zero_of_injective _

omit [IsAlgClosed k] in
/-- Every idempotent endomorphism of the Nakayama kernel is zero or the
identity. -/
theorem nakayamaKernel_idempotent_eq_zero_or_one
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hMind : Indecomposable M)
    (a : P.nakayamaKernel hI ⟶ P.nakayamaKernel hI)
    (haa : a ≫ a = a) : a = 0 ∨ a = 𝟙 _ := by
  rcases P.nakayamaKernel_idempotent_factorsThroughInjective_or_complement
      hI hMind a haa with hafac | hbfac
  · left
    exact idempotent_eq_zero_of_factorsThroughInjective
      a haa hafac (fun rI ↦
        P.nakayamaKernel_isZero_of_injective_retract hI rI)
  · right
    let b : P.nakayamaKernel hI ⟶ P.nakayamaKernel hI := 𝟙 _ - a
    have hbb : b ≫ b = b := by
      dsimp only [b]
      rw [Preadditive.sub_comp, Preadditive.comp_sub,
        Preadditive.comp_sub, haa, Category.id_comp, Category.comp_id]
      abel
    have hbzero := idempotent_eq_zero_of_factorsThroughInjective
      b hbb hbfac (fun rI ↦
        P.nakayamaKernel_isZero_of_injective_retract hI rI)
    exact (sub_eq_zero.mp hbzero).symm

/-- The Nakayama kernel of a minimal presentation of a nonprojective
indecomposable object is categorically indecomposable. -/
theorem nakayamaKernel_indecomposable
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M) :
    Indecomposable (P.nakayamaKernel hI) := by
  let T := P.nakayamaKernel hI
  refine ⟨P.nakayamaKernel_not_isZero hI hM hMind, ?_⟩
  intro Y Z e
  let rY : T ⟶ Y := e.hom ≫ biprod.fst
  let iY : Y ⟶ T := biprod.inl ≫ e.inv
  let p : T ⟶ T := rY ≫ iY
  have hiYrY : iY ≫ rY = 𝟙 Y := by
    dsimp only [iY, rY]
    simp [Category.assoc]
  have hpp : p ≫ p = p := by
    dsimp only [p]
    rw [Category.assoc, ← Category.assoc iY rY iY,
      hiYrY, Category.id_comp]
  rcases P.nakayamaKernel_idempotent_eq_zero_or_one
      hI hMind p hpp with hpzero | hpone
  · left
    letI : IsSplitEpi rY := IsSplitEpi.mk'
      { section_ := iY
        id := hiYrY }
    have hiYzero : iY = 0 := by
      apply (cancel_epi rY).1
      change p = rY ≫ 0
      rw [hpzero, comp_zero]
    apply (IsZero.iff_id_eq_zero Y).2
    rw [← hiYrY, hiYzero, zero_comp]
  · right
    let iZ : Z ⟶ T := biprod.inr ≫ e.inv
    let rZ : T ⟶ Z := e.hom ≫ biprod.snd
    have hiZrZ : iZ ≫ rZ = 𝟙 Z := by
      dsimp only [iZ, rZ]
      simp [Category.assoc]
    have hiZp : iZ ≫ p = 0 := by
      dsimp only [p, rY, iY, iZ]
      simp [Category.assoc]
    have hiZzero : iZ = 0 := by
      calc
        iZ = iZ ≫ 𝟙 T := (Category.comp_id iZ).symm
        _ = iZ ≫ p := by rw [hpone]
        _ = 0 := hiZp
    apply (IsZero.iff_id_eq_zero Z).2
    rw [← hiZrZ, hiZzero, zero_comp]

/-- A right almost-split realization with indecomposable Nakayama kernel is
already right minimal, by comparison with any minimal right almost-split map
to the same endpoint. -/
theorem stableSocleClass_realization_isRightMinimal
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M)
    {E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (i : P.nakayamaKernel hI ⟶ E) (q : E ⟶ M)
    (zero : i ≫ q = 0)
    (hS : (ShortComplex.mk i q zero).ShortExact)
    (hqAS : QuotientSubmoduleEquidistribution.IsRightAlmostSplit q)
    {N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (m : N ⟶ M)
    (hmAS : QuotientSubmoduleEquidistribution.IsRightAlmostSplit m)
    (hmMin : QuotientSubmoduleEquidistribution.IsRightMinimal m) :
    QuotientSubmoduleEquidistribution.IsRightMinimal q := by
  let T := P.nakayamaKernel hI
  obtain ⟨r, hr⟩ := hmAS.factors q hqAS.not_isSplitEpi
  obtain ⟨s, hs⟩ := hqAS.factors m hmAS.not_isSplitEpi
  have hsr : (s ≫ r) ≫ m = m := by
    rw [Category.assoc, hr, hs]
  letI : IsIso (s ≫ r) := hmMin (s ≫ r) hsr
  have hinvm : inv (s ≫ r) ≫ m = m := by
    apply (cancel_epi (s ≫ r)).1
    rw [IsIso.hom_inv_id_assoc, hsr]
  let s' : N ⟶ E := inv (s ≫ r) ≫ s
  have hs'r : s' ≫ r = 𝟙 N := by
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
  let v' : E ⟶ T := lifted.1
  have hv : v' ≫ i = u := lifted.2
  have huv : u ≫ v' = v' := by
    apply (cancel_mono i).1
    rw [Category.assoc, hv, huu]
  let a : T ⟶ T := i ≫ v'
  have haa : a ≫ a = a := by
    dsimp only [a]
    rw [Category.assoc, ← Category.assoc v' i v', hv, huv]
  rcases MagnitudeConjecture.CategoryTheory.indecomposable_idempotent_eq_zero_or_one
      T (P.nakayamaKernel_indecomposable hI hM hMind) a haa with
      hazero | haone
  · have hu2zero : u ≫ u = 0 := by
      rw [← hv, Category.assoc]
      change v' ≫ a ≫ i = 0
      simp [hazero]
    have huzero : u = 0 := by rw [← huu, hu2zero]
    have hpid : p = 𝟙 E := by
      exact (sub_eq_zero.mp (show 𝟙 E - p = 0 from huzero)).symm
    let er : E ≅ N :=
      { hom := r
        inv := s'
        hom_inv_id := hpid
        inv_hom_id := hs'r }
    letI : IsSplitMono r := by
      exact IsSplitMono.mk' { retraction := s', id := hpid }
    rw [← hr]
    exact hmMin.precomp_splitMono r
  · have hiSplit : IsSplitMono i :=
      IsSplitMono.mk' { retraction := v', id := haone }
    exfalso
    apply hqAS.not_isSplitEpi
    letI : IsSplitMono i := hiSplit
    letI : Epi q := hS.epi_g
    let splitting := ShortComplex.Splitting.ofExactOfRetraction
      (ShortComplex.mk i q zero) hS.exact v' haone inferInstance
    exact splitting.isSplitEpi_g

/-- The Nakayama kernel is the kernel of every minimal right almost-split map
to the same endpoint. -/
theorem nonempty_nakayamaKernelIso_kernel_of_minimalRightAlmostSplit
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M)
    {E : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (i : P.nakayamaKernel hI ⟶ E) (q : E ⟶ M)
    (zero : i ≫ q = 0)
    (hS : (ShortComplex.mk i q zero).ShortExact)
    (hqAS : QuotientSubmoduleEquidistribution.IsRightAlmostSplit q)
    {N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (m : N ⟶ M)
    (hmAS : QuotientSubmoduleEquidistribution.IsRightAlmostSplit m)
    (hmMin : QuotientSubmoduleEquidistribution.IsRightMinimal m) :
    Nonempty (P.nakayamaKernel hI ≅ kernel m) := by
  have hqMin := P.stableSocleClass_realization_isRightMinimal
    hI hM hMind i q zero hS hqAS m hmAS hmMin
  obtain ⟨ek⟩ :=
    QuotientSubmoduleEquidistribution.nonempty_kernelIso_of_rightAlmostSplit
      hqAS hqMin hmAS hmMin
  let ei : P.nakayamaKernel hI ≅ kernel q :=
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel q) hS.fIsKernel).symm
  exact ⟨ei.trans ek⟩

/-- The Nakayama kernel is the kernel of a chosen minimal right almost-split
map, without retaining the auxiliary realization of the distinguished stable
socle class in the statement. -/
theorem nonempty_nakayamaKernelIso_kernel
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (hM : ¬ Projective M) (hMind : Indecomposable M)
    {N : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (m : N ⟶ M)
    (hmAS : QuotientSubmoduleEquidistribution.IsRightAlmostSplit m)
    (hmMin : QuotientSubmoduleEquidistribution.IsRightMinimal m) :
    Nonempty (P.nakayamaKernel hI ≅ kernel m) := by
  obtain ⟨E, i, q, zero, hS, _, hqAS⟩ :=
    P.exists_stableSocleClass_realization_rightAlmostSplit
      hI hM hMind
  exact P.nonempty_nakayamaKernelIso_kernel_of_minimalRightAlmostSplit
    hI hM hMind i q zero hS hqAS m hmAS hmMin

end TwoStepMinimalFiniteRepresentablePresentation
end MagnitudeConjecture.CoveringHom
