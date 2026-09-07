import MagnitudeConjecture.Algebra.RightModuleStableHom
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Hom exactness for the chosen right-module presentation

This file packages precomposition by the two arrows of a two-step minimal
projective presentation as linear maps.  Exactness of the presentation gives
the exact Hom sequence used in the stable Hom--Ext pairing.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.TwoStepMinimalProjectivePresentation

universe u

variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
  [FiniteDimensional k B] [IsNoetherianRing Bᵐᵒᵖ]
variable {X : FGModuleCat.{u} Bᵐᵒᵖ}

/-- Precomposition with the augmentation `P₀ ⟶ X`. -/
def augmentationPrecompLinear
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    (X ⟶ Y) →ₗ[k] (P.augmentation.p ⟶ Y) :=
  CategoryTheory.Linear.leftComp k Y P.augmentation.f

/-- Precomposition with the differential `P₁ ⟶ P₀`. -/
def differentialPrecompLinear
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    (P.augmentation.p ⟶ Y) →ₗ[k] (P.syzygyPresentation.p ⟶ Y) :=
  CategoryTheory.Linear.leftComp k Y P.differential

@[simp]
theorem augmentationPrecompLinear_apply
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) (f : X ⟶ Y) :
    P.augmentationPrecompLinear (k := k) Y f = P.augmentation.f ≫ f :=
  rfl

@[simp]
theorem differentialPrecompLinear_apply
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) (f : P.augmentation.p ⟶ Y) :
    P.differentialPrecompLinear (k := k) Y f = P.differential ≫ f :=
  rfl

/-- Precomposition with the epimorphic augmentation is injective. -/
theorem augmentationPrecompLinear_injective
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    Function.Injective (P.augmentationPrecompLinear (k := k) Y) := by
  intro f g h
  apply (cancel_epi P.augmentation.f).1
  exact h

/-- Applying `Hom(-,Y)` to the presentation is exact at `Hom(P₀,Y)`. -/
theorem range_augmentationPrecompLinear
    (P : TwoStepMinimalProjectivePresentation X)
    (Y : FGModuleCat.{u} Bᵐᵒᵖ) :
    LinearMap.range (P.augmentationPrecompLinear (k := k) Y) =
      LinearMap.ker (P.differentialPrecompLinear (k := k) Y) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    change P.differential ≫ P.augmentation.f ≫ f = 0
    rw [← Category.assoc, P.differential_comp_augmentation, zero_comp]
  · intro f hf
    rw [LinearMap.mem_ker] at hf
    letI : Epi P.presentationComplex.g := by
      dsimp [presentationComplex]
      infer_instance
    obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc'
      (P.presentationComplex_exact.gIsCokernel) f hf
    exact ⟨g, hg⟩

end MagnitudeConjecture.TwoStepMinimalProjectivePresentation
