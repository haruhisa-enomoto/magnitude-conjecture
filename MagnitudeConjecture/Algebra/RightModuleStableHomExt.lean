import MagnitudeConjecture.Algebra.CoefficientDual
import MagnitudeConjecture.Algebra.RightModuleProjectivePresentationHom
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-!
# Stable Hom--Ext duality for the Nakayama kernel

For a chosen two-step minimal projective presentation

`P₁ ⟶ P₀ ⟶ X`,

this file proves the presentation-dependent Auslander--Reiten formula

`Ext¹(Y, ker(νP₁ ⟶ νP₀)) ≃ Dₖ stableHom(X,Y)`.

The proof uses the concrete finite-projective Nakayama--Hom equivalence and
only the one-sided stable Hom quotient needed here.
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

local instance : Module.Injective k k :=
  Module.injective_of_isSemisimpleRing k k

/-- The Nakayama boundary pairing before either variable is quotiented. -/
def ordinaryBoundaryLinear
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    (Y ⟶ P.nakayamaCokernel (k := k)) →ₗ[k]
      ((X ⟶ Y) →ₗ[k] k) :=
  (LinearMap.lcomp k k (P.augmentationPrecompLinear (k := k) Y)).comp
    ((RightModule.fieldNakayamaHomEquiv (k := k)
      P.augmentation.p Y).toLinearMap.comp
      (CategoryTheory.Linear.rightComp k Y
        (P.nakayamaCokernelι (k := k))))

@[simp]
theorem ordinaryBoundaryLinear_apply
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (c : Y ⟶ P.nakayamaCokernel (k := k)) (f : X ⟶ Y) :
    P.ordinaryBoundaryLinear (k := k) Y c f =
      RightModule.fieldNakayamaHomEquiv (k := k)
        P.augmentation.p Y
        (c ≫ P.nakayamaCokernelι (k := k))
        (P.augmentation.f ≫ f) :=
  rfl

/-- The Nakayama--Hom comparison intertwines the presentation differential. -/
theorem fieldNakayamaHomEquiv_differential
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (a : Y ⟶ RightModule.projectiveNakayamaFGObj (k := k)
      P.syzygyPresentation.p)
    (f : P.augmentation.p ⟶ Y) :
    RightModule.fieldNakayamaHomEquiv (k := k)
        P.augmentation.p Y
        (a ≫ P.nakayamaDifferential (k := k)) f =
      RightModule.fieldNakayamaHomEquiv (k := k)
        P.syzygyPresentation.p Y a (P.differential ≫ f) := by
  exact RightModule.fieldNakayamaHomEquiv_projectiveNaturality
    (k := k) P.differential Y a f

/-- Naturality of the unquotiented pairing in its variable module. -/
theorem ordinaryBoundaryLinear_naturality
    (P : TwoStepMinimalProjectivePresentation X)
    {Y Z : FGModuleCat.{u} Bᵐᵒᵖ} (g : Y ⟶ Z)
    (c : Z ⟶ P.nakayamaCokernel (k := k)) (f : X ⟶ Y) :
    P.ordinaryBoundaryLinear (k := k) Y (g ≫ c) f =
      P.ordinaryBoundaryLinear (k := k) Z c (f ≫ g) := by
  exact RightModule.fieldNakayamaHomEquiv_naturality
    (k := k) P.augmentation.p g
    (c ≫ P.nakayamaCokernelι (k := k))
    (P.augmentation.f ≫ f)

/-- The pairing kills the displayed injective-presentation coboundaries. -/
theorem ordinaryBoundaryLinear_eq_zero_of_mem_presentationRange
    [HasExt.{w} (FGModuleCat.{u} Bᵐᵒᵖ)]
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (c : Y ⟶ P.nakayamaCokernel (k := k))
    (hc : c ∈ P.nakayamaExtPresentationRange (k := k) Y) :
    P.ordinaryBoundaryLinear (k := k) Y c = 0 := by
  obtain ⟨a, rfl⟩ :=
    (P.mem_nakayamaExtPresentationRange_iff (k := k) Y c).mp hc
  apply LinearMap.ext
  intro f
  rw [ordinaryBoundaryLinear_apply, Category.assoc,
    P.nakayamaCokernelπ_comp_ι]
  rw [P.fieldNakayamaHomEquiv_differential (k := k)]
  rw [← Category.assoc, P.differential_comp_augmentation]
  simp

/-- The pairing kills maps from `X` which factor through a projective. -/
theorem ordinaryBoundaryLinear_apply_eq_zero_of_factorsThroughProjective
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (c : Y ⟶ P.nakayamaCokernel (k := k))
    {f : X ⟶ Y} (hf : RightModule.FactorsThroughProjective f) :
    P.ordinaryBoundaryLinear (k := k) Y c f = 0 := by
  letI : Projective hf.middle := hf.projective
  let a : hf.middle ⟶ RightModule.projectiveNakayamaFGObj (k := k)
      P.syzygyPresentation.p :=
    Projective.factorThru (hf.right ≫ c) (P.nakayamaCokernelπ (k := k))
  have ha : a ≫ P.nakayamaCokernelπ (k := k) = hf.right ≫ c :=
    Projective.factorThru_comp _ _
  rw [ordinaryBoundaryLinear_apply, ← hf.fac, ← Category.assoc]
  rw [← RightModule.fieldNakayamaHomEquiv_naturality
    (k := k) P.augmentation.p hf.right
    (c ≫ P.nakayamaCokernelι (k := k))
    (P.augmentation.f ≫ hf.left)]
  rw [← Category.assoc, ← ha, Category.assoc,
    P.nakayamaCokernelπ_comp_ι]
  rw [P.fieldNakayamaHomEquiv_differential (k := k)]
  rw [← Category.assoc, P.differential_comp_augmentation]
  simp

/-- The boundary functional descended to projective-stable Hom. -/
def stableBoundary
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (c : Y ⟶ P.nakayamaCokernel (k := k)) :
    RightModule.projectiveStableHom (k := k) X Y →ₗ[k] k :=
  (RightModule.projectiveFactorSubmodule (k := k) X Y).liftQ
    (P.ordinaryBoundaryLinear (k := k) Y c) (by
      intro f hf
      rw [LinearMap.mem_ker]
      obtain ⟨hfactor⟩ := hf
      exact P.ordinaryBoundaryLinear_apply_eq_zero_of_factorsThroughProjective
        (k := k) Y c hfactor)

@[simp]
theorem stableBoundary_mk
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (c : Y ⟶ P.nakayamaCokernel (k := k)) (f : X ⟶ Y) :
    P.stableBoundary (k := k) Y c
        (RightModule.projectiveStableClass (k := k) f) =
      P.ordinaryBoundaryLinear (k := k) Y c f :=
  rfl

/-- The stable boundary, linear in its presentation representative. -/
def stableBoundaryLinear
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    (Y ⟶ P.nakayamaCokernel (k := k)) →ₗ[k]
      (RightModule.projectiveStableHom (k := k) X Y →ₗ[k] k) where
  toFun := P.stableBoundary (k := k) Y
  map_add' c c' := by
    apply LinearMap.ext
    intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change P.ordinaryBoundaryLinear (k := k) Y (c + c') f =
      P.ordinaryBoundaryLinear (k := k) Y c f +
        P.ordinaryBoundaryLinear (k := k) Y c' f
    simp
  map_smul' a c := by
    apply LinearMap.ext
    intro q
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change P.ordinaryBoundaryLinear (k := k) Y (a • c) f =
      a * P.ordinaryBoundaryLinear (k := k) Y c f
    simp

variable [HasExt.{w} (FGModuleCat.{u} Bᵐᵒᵖ)]

/-- The pairing after quotienting its presentation variable. -/
def boundaryQuotientLinear
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    ((Y ⟶ P.nakayamaCokernel (k := k)) ⧸
        P.nakayamaExtPresentationRange (k := k) Y) →ₗ[k]
      (RightModule.projectiveStableHom (k := k) X Y →ₗ[k] k) :=
  (P.nakayamaExtPresentationRange (k := k) Y).liftQ
    (P.stableBoundaryLinear (k := k) Y) (by
      intro c hc
      rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro q
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact LinearMap.congr_fun
        (P.ordinaryBoundaryLinear_eq_zero_of_mem_presentationRange
          (k := k) Y c hc) f)

@[simp]
theorem boundaryQuotientLinear_mk_mk
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ)
    (c : Y ⟶ P.nakayamaCokernel (k := k)) (f : X ⟶ Y) :
    P.boundaryQuotientLinear (k := k) Y (Submodule.Quotient.mk c)
        (RightModule.projectiveStableClass (k := k) f) =
      P.ordinaryBoundaryLinear (k := k) Y c f :=
  rfl

/-- The kernel of the unquotiented boundary is precisely the displayed
injective-presentation range. -/
theorem ker_ordinaryBoundaryLinear
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    LinearMap.ker (P.ordinaryBoundaryLinear (k := k) Y) =
      P.nakayamaExtPresentationRange (k := k) Y := by
  apply le_antisymm
  · intro c hc
    let phi : (P.augmentation.p ⟶ Y) →ₗ[k] k :=
      RightModule.fieldNakayamaHomEquiv (k := k)
        P.augmentation.p Y
        (c ≫ P.nakayamaCokernelι (k := k))
    have hphi : phi ∈ CoefficientDual.annihilator
        (E := k) (LinearMap.ker
          (P.differentialPrecompLinear (k := k) Y)) := by
      rw [← P.range_augmentationPrecompLinear (k := k) Y]
      rw [CoefficientDual.mem_annihilator_iff]
      intro f hf
      obtain ⟨g, rfl⟩ := hf
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp hc) g
    have hphiRange : phi ∈ LinearMap.range
        (LinearMap.lcomp k k
          (P.differentialPrecompLinear (k := k) Y)) := by
      rw [CoefficientDual.range_lcomp_eq_annihilator_ker]
      exact hphi
    obtain ⟨psi, hpsi⟩ := hphiRange
    let a : Y ⟶ RightModule.projectiveNakayamaFGObj (k := k)
        P.syzygyPresentation.p :=
      (RightModule.fieldNakayamaHomEquiv (k := k)
        P.syzygyPresentation.p Y).symm psi
    have ha : a ≫ P.nakayamaDifferential (k := k) =
        c ≫ P.nakayamaCokernelι (k := k) := by
      apply (RightModule.fieldNakayamaHomEquiv (k := k)
        P.augmentation.p Y).injective
      apply LinearMap.ext
      intro f
      rw [P.fieldNakayamaHomEquiv_differential (k := k)]
      have hvalue := LinearMap.congr_fun hpsi f
      simpa [a, phi, differentialPrecompLinear,
        LinearMap.lcomp_apply] using hvalue
    rw [P.mem_nakayamaExtPresentationRange_iff (k := k) Y]
    refine ⟨a, ?_⟩
    apply (cancel_mono (P.nakayamaCokernelι (k := k))).1
    rw [Category.assoc, P.nakayamaCokernelπ_comp_ι]
    exact ha
  · intro c hc
    rw [LinearMap.mem_ker]
    exact P.ordinaryBoundaryLinear_eq_zero_of_mem_presentationRange
      (k := k) Y c hc

/-- The descended boundary is injective. -/
theorem boundaryQuotientLinear_injective
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    Function.Injective (P.boundaryQuotientLinear (k := k) Y) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Submodule.Quotient.mk_eq_zero]
  rw [← P.ker_ordinaryBoundaryLinear (k := k) Y]
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro f
  have hvalue := LinearMap.congr_fun hq
    (RightModule.projectiveStableClass (k := k) f)
  exact hvalue

/-- Every functional on projective-stable Hom is a boundary functional. -/
theorem boundaryQuotientLinear_surjective
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    Function.Surjective (P.boundaryQuotientLinear (k := k) Y) := by
  intro lambda
  let phiX : (X ⟶ Y) →ₗ[k] k :=
    lambda.comp (RightModule.projectiveStableClass (k := k))
  obtain ⟨phi₀, hphi₀⟩ := Module.Injective.extension_property k k
    (X ⟶ Y) (P.augmentation.p ⟶ Y)
    (P.augmentationPrecompLinear (k := k) Y)
    (P.augmentationPrecompLinear_injective (k := k) Y) phiX
  let a₀ : Y ⟶ RightModule.projectiveNakayamaFGObj (k := k)
      P.augmentation.p :=
    (RightModule.fieldNakayamaHomEquiv (k := k)
      P.augmentation.p Y).symm phi₀
  let Q : MinimalProjectivePresentation Y :=
    Classical.choice (minimalProjectivePresentation_nonempty k Y)
  let psi₀ : (P.augmentation.p ⟶ Q.p) →ₗ[k] k :=
    RightModule.fieldNakayamaHomEquiv (k := k)
      P.augmentation.p Q.p (Q.f ≫ a₀)
  have hpsi₀ : psi₀ ∈ CoefficientDual.annihilator
      (E := k) (LinearMap.ker
        (P.differentialPrecompLinear (k := k) Q.p)) := by
    rw [← P.range_augmentationPrecompLinear (k := k) Q.p]
    rw [CoefficientDual.mem_annihilator_iff]
    intro b hb
    obtain ⟨f, rfl⟩ := hb
    have hstable : RightModule.projectiveStableClass (k := k)
        (f ≫ Q.f) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero
        (RightModule.projectiveFactorSubmodule (k := k) X Y)).2
      exact ⟨{
        middle := Q.p
        projective := Q.projective
        left := f
        right := Q.f
        fac := rfl }⟩
    calc
      psi₀ (P.augmentationPrecompLinear (k := k) Q.p f) =
          RightModule.fieldNakayamaHomEquiv (k := k)
            P.augmentation.p Y a₀
              ((P.augmentation.f ≫ f) ≫ Q.f) := by
        exact RightModule.fieldNakayamaHomEquiv_naturality
          (k := k) P.augmentation.p Q.f a₀
          (P.augmentation.f ≫ f)
      _ = phi₀ (P.augmentationPrecompLinear (k := k) Y
          (f ≫ Q.f)) := by
        simp only [a₀, LinearEquiv.apply_symm_apply,
          augmentationPrecompLinear_apply, Category.assoc]
      _ = phiX (f ≫ Q.f) := LinearMap.congr_fun hphi₀ (f ≫ Q.f)
      _ = lambda (RightModule.projectiveStableClass (k := k)
          (f ≫ Q.f)) := rfl
      _ = 0 := by rw [hstable, map_zero]
  have hpsi₀Range : psi₀ ∈ LinearMap.range
      (LinearMap.lcomp k k
        (P.differentialPrecompLinear (k := k) Q.p)) := by
    rw [CoefficientDual.range_lcomp_eq_annihilator_ker]
    exact hpsi₀
  obtain ⟨psi₁, hpsi₁⟩ := hpsi₀Range
  let a₁ : Q.p ⟶ RightModule.projectiveNakayamaFGObj (k := k)
      P.syzygyPresentation.p :=
    (RightModule.fieldNakayamaHomEquiv (k := k)
      P.syzygyPresentation.p Q.p).symm psi₁
  have ha₁ : a₁ ≫ P.nakayamaDifferential (k := k) = Q.f ≫ a₀ := by
    apply (RightModule.fieldNakayamaHomEquiv (k := k)
      P.augmentation.p Q.p).injective
    apply LinearMap.ext
    intro f
    rw [P.fieldNakayamaHomEquiv_differential (k := k)]
    have hvalue := LinearMap.congr_fun hpsi₁ f
    simpa [a₁, psi₀, differentialPrecompLinear,
      LinearMap.lcomp_apply] using hvalue
  have ha₀zero : a₀ ≫ cokernel.π
      (P.nakayamaCokernelι (k := k)) = 0 := by
    apply (cancel_epi Q.f).1
    simp only [comp_zero]
    calc
      Q.f ≫ a₀ ≫ cokernel.π (P.nakayamaCokernelι (k := k)) =
          (Q.f ≫ a₀) ≫
            cokernel.π (P.nakayamaCokernelι (k := k)) :=
        (Category.assoc _ _ _).symm
      _ = (a₁ ≫ P.nakayamaDifferential (k := k)) ≫
          cokernel.π (P.nakayamaCokernelι (k := k)) := by rw [ha₁]
      _ = 0 := by
        rw [← P.nakayamaCokernelπ_comp_ι]
        simp only [Category.assoc, cokernel.condition, comp_zero]
  let c : Y ⟶ P.nakayamaCokernel (k := k) :=
    Abelian.monoLift (P.nakayamaCokernelι (k := k)) a₀ ha₀zero
  refine ⟨Submodule.Quotient.mk c, ?_⟩
  apply LinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change P.ordinaryBoundaryLinear (k := k) Y c f =
    lambda (RightModule.projectiveStableClass (k := k) f)
  rw [ordinaryBoundaryLinear_apply]
  rw [show c ≫ P.nakayamaCokernelι (k := k) = a₀ by
    exact Abelian.monoLift_comp _ _ _]
  rw [show RightModule.fieldNakayamaHomEquiv (k := k)
      P.augmentation.p Y a₀ = phi₀ by simp [a₀]]
  exact LinearMap.congr_fun hphi₀ f

/-- The presentation quotient is the coefficient dual of stable Hom. -/
def boundaryQuotientLinearEquiv
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    ((Y ⟶ P.nakayamaCokernel (k := k)) ⧸
        P.nakayamaExtPresentationRange (k := k) Y) ≃ₗ[k]
      (RightModule.projectiveStableHom (k := k) X Y →ₗ[k] k) :=
  LinearEquiv.ofBijective (P.boundaryQuotientLinear (k := k) Y)
    ⟨P.boundaryQuotientLinear_injective (k := k) Y,
      P.boundaryQuotientLinear_surjective (k := k) Y⟩

/-- The fixed-presentation stable Auslander--Reiten formula. -/
def stableHomExtLinearEquiv
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    Ext.{w} Y (P.nakayamaKernel (k := k)) 1 ≃ₗ[k]
      (RightModule.projectiveStableHom (k := k) X Y →ₗ[k] k) :=
  (P.nakayamaExtOneQuotientLinearEquiv (k := k) Y).symm.trans
    (P.boundaryQuotientLinearEquiv (k := k) Y)

/-- Naturality of the stable Auslander--Reiten formula under pullback. -/
theorem stableHomExtLinearEquiv_naturality
    (P : TwoStepMinimalProjectivePresentation X)
    {Y Z : FGModuleCat.{u} Bᵐᵒᵖ} (g : Y ⟶ Z)
    (xi : Ext.{w} Z (P.nakayamaKernel (k := k)) 1)
    (a : RightModule.projectiveStableHom (k := k) X Y) :
    P.stableHomExtLinearEquiv (k := k) Y
        ((Ext.mk₀ g).comp xi (zero_add 1)) a =
      P.stableHomExtLinearEquiv (k := k) Z xi
        (RightModule.projectiveStablePostcomp (k := k) X g a) := by
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
    ((P.nakayamaExtOneQuotientLinearEquiv (k := k) Z).symm xi)
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  rw [stableHomExtLinearEquiv, LinearEquiv.trans_apply,
    P.nakayamaExtOneQuotientLinearEquiv_symm_pullback (k := k)]
  rw [← hc]
  change P.boundaryQuotientLinearEquiv (k := k) Y
      (Submodule.Quotient.mk (g ≫ c))
        (RightModule.projectiveStableClass (k := k) f) = _
  rw [show P.stableHomExtLinearEquiv (k := k) Z xi =
      P.boundaryQuotientLinearEquiv (k := k) Z
        (Submodule.Quotient.mk c) by
    simp [stableHomExtLinearEquiv, ← hc]]
  change P.boundaryQuotientLinear (k := k) Y
      (Submodule.Quotient.mk (g ≫ c))
        (RightModule.projectiveStableClass (k := k) f) =
    P.boundaryQuotientLinear (k := k) Z
      (Submodule.Quotient.mk c)
        (RightModule.projectiveStableClass (k := k) (f ≫ g))
  rw [boundaryQuotientLinear_mk_mk, boundaryQuotientLinear_mk_mk]
  exact P.ordinaryBoundaryLinear_naturality (k := k) g c f

end MagnitudeConjecture.TwoStepMinimalProjectivePresentation
