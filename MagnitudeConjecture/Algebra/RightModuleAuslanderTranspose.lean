import MagnitudeConjecture.Algebra.RightModuleNakayamaHom
import MagnitudeConjecture.CategoryTheory.InjectivePresentationExt
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# The concrete right-module Auslander transpose copresentation

For a two-step minimal projective presentation `P₁ ⟶ P₀ ⟶ X`, the
Nakayama kernel `ker(nu P₁ ⟶ nu P₀)` embeds in the injective module
`nu P₁`.  This file packages the resulting short injective presentation
and its pullback-natural quotient description of degree-one Ext.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.TwoStepMinimalProjectivePresentation

universe u w

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable {X : FGModuleCat.{u} Bᵐᵒᵖ}

/-- The inclusion of the Nakayama kernel in `nu P₁`, packaged as an
injective presentation. -/
def nakayamaInjectivePresentation
    (P : TwoStepMinimalProjectivePresentation X) :
    InjectivePresentation (P.nakayamaKernel (k := k)) where
  J := RightModule.projectiveNakayamaFGObj (k := k)
    P.syzygyPresentation.p
  injective := RightModule.projectiveNakayamaFGObj_injective
    (k := k) P.syzygyPresentation.p
  f := kernel.ι (P.nakayamaDifferential (k := k))
  mono := inferInstance

/-- The actual quotient of `nu P₁` by the Nakayama kernel. -/
abbrev nakayamaCokernel (P : TwoStepMinimalProjectivePresentation X) :
    FGModuleCat.{u} Bᵐᵒᵖ :=
  cokernel (kernel.ι (P.nakayamaDifferential (k := k)))

/-- The quotient map `nu P₁ ⟶ C_P`. -/
abbrev nakayamaCokernelπ (P : TwoStepMinimalProjectivePresentation X) :
    RightModule.projectiveNakayamaFGObj (k := k)
        P.syzygyPresentation.p ⟶ P.nakayamaCokernel (k := k) :=
  cokernel.π (kernel.ι (P.nakayamaDifferential (k := k)))

/-- The Nakayama differential descends to an embedding `C_P ⟶ nu P₀`. -/
def nakayamaCokernelι (P : TwoStepMinimalProjectivePresentation X) :
    P.nakayamaCokernel (k := k) ⟶
      RightModule.projectiveNakayamaFGObj (k := k) P.augmentation.p :=
  cokernel.desc (kernel.ι (P.nakayamaDifferential (k := k)))
    (P.nakayamaDifferential (k := k))
    (kernel.condition (P.nakayamaDifferential (k := k)))

@[simp]
theorem nakayamaCokernelπ_comp_ι
    (P : TwoStepMinimalProjectivePresentation X) :
    P.nakayamaCokernelπ (k := k) ≫ P.nakayamaCokernelι (k := k) =
      P.nakayamaDifferential (k := k) := by
  exact cokernel.π_desc _ _ _

instance nakayamaCokernelι_mono
    (P : TwoStepMinimalProjectivePresentation X) :
    Mono (P.nakayamaCokernelι (k := k)) := by
  exact (ShortComplex.exact_kernel
    (P.nakayamaDifferential (k := k))).mono_cokernelDesc

/-- Minimality of the projective presentation rules out nonzero injective
retracts of its Nakayama kernel. -/
theorem nakayamaKernel_isZero_of_injective_retract
    (P : TwoStepMinimalProjectivePresentation X)
    {I : FGModuleCat.{u} Bᵐᵒᵖ} [Injective I]
    (r : Retract I (P.nakayamaKernel (k := k))) : IsZero I := by
  letI : IsSplitMono r.i := IsSplitMono.mk'
    { retraction := r.r
      id := r.retract }
  let j : I ⟶ RightModule.projectiveNakayamaFGObj (k := k)
      P.syzygyPresentation.p :=
    r.i ≫ kernel.ι (P.nakayamaDifferential (k := k))
  letI : Mono j := by
    dsimp only [j]
    infer_instance
  let s : RightModule.projectiveNakayamaFGObj (k := k)
      P.syzygyPresentation.p ⟶ I :=
    Injective.factorThru (𝟙 I) j
  have hjs : j ≫ s = 𝟙 I :=
    Injective.comp_factorThru (𝟙 I) j
  let a : RightModule.projectiveNakayamaFGObj (k := k)
        P.syzygyPresentation.p ⟶
      RightModule.projectiveNakayamaFGObj (k := k)
        P.syzygyPresentation.p := s ≫ j
  let e : P.syzygyPresentation.p ⟶ P.syzygyPresentation.p :=
    RightModule.projectiveNakayamaMapPreimage (k := k)
      P.syzygyPresentation.p P.syzygyPresentation.p a
  have hnue : RightModule.projectiveNakayamaMap (k := k) e = a :=
    RightModule.projectiveNakayamaMap_preimage (k := k)
      P.syzygyPresentation.p P.syzygyPresentation.p a
  have haj : a ≫ P.nakayamaDifferential (k := k) = 0 := by
    dsimp only [a]
    rw [Category.assoc]
    have hjzero : j ≫ P.nakayamaDifferential (k := k) = 0 := by
      dsimp only [j]
      rw [Category.assoc, kernel.condition, comp_zero]
    rw [hjzero, comp_zero]
  have hed : e ≫ P.differential = 0 := by
    apply RightModule.projectiveNakayamaMap_injective (k := k)
      P.syzygyPresentation.p P.augmentation.p
    change RightModule.projectiveNakayamaMap (k := k)
        (e ≫ P.differential) =
      RightModule.projectiveNakayamaMap (k := k) 0
    rw [RightModule.projectiveNakayamaMap_comp, hnue]
    change a ≫ P.nakayamaDifferential (k := k) =
      RightModule.projectiveNakayamaMap (k := k) 0
    rw [haj, RightModule.projectiveNakayamaMap_zero]
  have haa : a ≫ a = a := by
    dsimp only [a]
    rw [Category.assoc, ← Category.assoc j s j, hjs,
      Category.id_comp]
  have hee : e ≫ e = e := by
    apply RightModule.projectiveNakayamaMap_injective (k := k)
      P.syzygyPresentation.p P.syzygyPresentation.p
    change RightModule.projectiveNakayamaMap (k := k) (e ≫ e) =
      RightModule.projectiveNakayamaMap (k := k) e
    rw [RightModule.projectiveNakayamaMap_comp, hnue]
    exact haa
  let h : P.syzygyPresentation.p ⟶ P.syzygyPresentation.p := 𝟙 _ - e
  have hhcover : h ≫ P.syzygyPresentation.f = P.syzygyPresentation.f := by
    apply (cancel_mono (kernel.ι P.augmentation.f)).1
    change h ≫ P.differential = P.differential
    dsimp only [h]
    rw [Preadditive.sub_comp, Category.id_comp, hed, sub_zero]
  haveI : IsIso h := P.syzygyPresentation.rightMinimal h hhcover
  have heh : e ≫ h = 0 := by
    dsimp only [h]
    rw [Preadditive.comp_sub, Category.comp_id, hee, sub_self]
  have hezero : e = 0 := by
    apply (cancel_mono h).1
    rw [heh, zero_comp]
  have hazero : a = 0 := by
    rw [← hnue, hezero, RightModule.projectiveNakayamaMap_zero]
  have hja : j ≫ a = j := by
    dsimp only [a]
    rw [← Category.assoc, hjs, Category.id_comp]
  have hjzero : j = 0 := by
    calc
      j = j ≫ a := hja.symm
      _ = 0 := by rw [hazero, comp_zero]
  exact IsZero.of_mono_eq_zero j hjzero

/-- The short exact sequence computing `Ext¹(-,ker(nu d))`. -/
abbrev nakayamaExtShortComplex
    (P : TwoStepMinimalProjectivePresentation X) :
    ShortComplex (FGModuleCat.{u} Bᵐᵒᵖ) :=
  (P.nakayamaInjectivePresentation (k := k)).shortComplex

/-- Coboundaries in the short injective presentation. -/
abbrev nakayamaExtPresentationRange
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    Submodule k (Y ⟶ P.nakayamaCokernel (k := k)) :=
  InjectivePresentationExt.presentationRange (k := k)
    (P.nakayamaExtShortComplex (k := k)) Y

@[simp]
theorem mem_nakayamaExtPresentationRange_iff
    [HasExt.{w} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (f : Y ⟶ P.nakayamaCokernel (k := k)) :
    f ∈ P.nakayamaExtPresentationRange (k := k) Y ↔
      ∃ a : Y ⟶ RightModule.projectiveNakayamaFGObj (k := k)
          P.syzygyPresentation.p,
        a ≫ P.nakayamaCokernelπ (k := k) = f := by
  exact InjectivePresentationExt.mem_presentationRange_iff
    (k := k) (P.nakayamaExtShortComplex (k := k)) Y f

variable [HasExt.{w} (FGModuleCat.{u} Bᵐᵒᵖ)]

/-- The sound presentation quotient for `Ext¹(Y,ker(nu d))`. -/
def nakayamaExtOneQuotientLinearEquiv
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    ((Y ⟶ P.nakayamaCokernel (k := k)) ⧸
        P.nakayamaExtPresentationRange (k := k) Y) ≃ₗ[k]
      Ext.{w} Y (P.nakayamaKernel (k := k)) 1 :=
  InjectivePresentationExt.quotientLinearEquivExtOne (k := k)
    (P.nakayamaInjectivePresentation (k := k)).shortExact_shortComplex Y

/-- Pullback on the Nakayama presentation quotient. -/
abbrev nakayamaPrecompQuotient
    (P : TwoStepMinimalProjectivePresentation X)
    {Y Z : FGModuleCat.{u} Bᵐᵒᵖ} (g : Y ⟶ Z) :
    ((Z ⟶ P.nakayamaCokernel (k := k)) ⧸
        P.nakayamaExtPresentationRange (k := k) Z) →ₗ[k]
      ((Y ⟶ P.nakayamaCokernel (k := k)) ⧸
        P.nakayamaExtPresentationRange (k := k) Y) :=
  InjectivePresentationExt.precompQuotient (k := k)
    (P.nakayamaExtShortComplex (k := k)) g

/-- Inverse-form pullback naturality of the Ext quotient. -/
theorem nakayamaExtOneQuotientLinearEquiv_symm_pullback
    (P : TwoStepMinimalProjectivePresentation X)
    {Y Z : FGModuleCat.{u} Bᵐᵒᵖ} (g : Y ⟶ Z)
    (xi : Ext.{w} Z (P.nakayamaKernel (k := k)) 1) :
    (P.nakayamaExtOneQuotientLinearEquiv (k := k) Y).symm
        ((Ext.mk₀ g).comp xi (zero_add 1)) =
      P.nakayamaPrecompQuotient (k := k) g
        ((P.nakayamaExtOneQuotientLinearEquiv (k := k) Z).symm xi) := by
  apply (P.nakayamaExtOneQuotientLinearEquiv (k := k) Y).injective
  rw [LinearEquiv.apply_symm_apply]
  symm
  have h :
      P.nakayamaExtOneQuotientLinearEquiv (k := k) Y
          (P.nakayamaPrecompQuotient (k := k) g
            ((P.nakayamaExtOneQuotientLinearEquiv (k := k) Z).symm xi)) =
        InjectivePresentationExt.pullbackLinear (k := k)
          (P.nakayamaExtShortComplex (k := k)) g
          (P.nakayamaExtOneQuotientLinearEquiv (k := k) Z
            ((P.nakayamaExtOneQuotientLinearEquiv (k := k) Z).symm xi)) :=
    InjectivePresentationExt.quotientLinearEquivExtOne_precompQuotient
      (k := k)
      (P.nakayamaInjectivePresentation (k := k)).shortExact_shortComplex g
      ((P.nakayamaExtOneQuotientLinearEquiv (k := k) Z).symm xi)
  rw [LinearEquiv.apply_symm_apply] at h
  simpa [InjectivePresentationExt.pullbackLinear] using h

end MagnitudeConjecture.TwoStepMinimalProjectivePresentation
