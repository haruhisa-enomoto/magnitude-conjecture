import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleDuality
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCover
import MagnitudeConjecture.CategoryTheory.InjectiveEnvelope

/-!
# Minimal injective envelopes of finite modules

Coefficient duality turns a finite module into a finite module over the
opposite category.  A minimal projective cover there dualizes back to a
minimal injective envelope.  Applying the construction to the first
cosyzygy gives a two-step minimal injective presentation.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture.CoveringHom

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]

/-- A minimal projective cover of the coefficient dual of `M` dualizes to a
minimal injective envelope of `M`. -/
noncomputable def minimalInjectivePresentationOfDualProjective
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (P : MinimalProjectivePresentation
      ((finiteCoefficientDualityEquivalence (k := k) (C := C)).functor.obj
        (Opposite.op M))) :
    MinimalInjectivePresentation M := by
  let E := finiteCoefficientDualityEquivalence (k := k) (C := C)
  let DM := E.functor.obj (Opposite.op M)
  letI : Projective (E.inverse.obj P.p) :=
    (E.symm.map_projective_iff P.p).2 inferInstance
  let J := (E.inverse.obj P.p).unop
  let g : (E.inverse.obj DM).unop ⟶ J :=
    (E.inverse.map P.f).unop
  haveI : Mono g := by
    dsimp only [g]
    infer_instance
  have hgmin : IsLeftMinimal g := by
    apply leftMinimal_unop
    apply rightMinimal_map_of_full_faithful
    exact P.rightMinimal
  let I : MinimalInjectivePresentation (E.inverse.obj DM).unop :=
    { J := J
      f := g
      leftMinimal := hgmin }
  let eM : (E.inverse.obj DM).unop ≅ M :=
    (E.unitIso.app (Opposite.op M)).unop
  exact I.preIso eM.symm

/-- Finite representables over the opposite category supply a minimal
injective envelope for every finite module. -/
theorem finiteDimensionalModule_minimalInjectivePresentation_nonempty
    (hP : ∀ X : Cᵒᵖ, IsFiniteDimensionalModule (C := Cᵒᵖ) k
      (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Nonempty (MinimalInjectivePresentation M) := by
  let E := finiteCoefficientDualityEquivalence (k := k) (C := C)
  let DM := E.functor.obj (Opposite.op M)
  obtain ⟨P⟩ :=
    finiteDimensionalModule_minimalProjectivePresentation_nonempty hP DM
  exact ⟨minimalInjectivePresentationOfDualProjective M P⟩

/-- Finite representables over the opposite category supply a two-step
minimal injective presentation for every finite module. -/
theorem finiteDimensionalModule_twoStepMinimalInjectivePresentation_nonempty
    (hP : ∀ X : Cᵒᵖ, IsFiniteDimensionalModule (C := Cᵒᵖ) k
      (linearCoyonedaLinearModule (k := k) X))
    (M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Nonempty (TwoStepMinimalInjectivePresentation M) := by
  obtain ⟨I₀⟩ :=
    finiteDimensionalModule_minimalInjectivePresentation_nonempty hP M
  obtain ⟨I₁⟩ :=
    finiteDimensionalModule_minimalInjectivePresentation_nonempty hP
      (cokernel I₀.f)
  exact ⟨{ augmentation := I₀, cosyzygyPresentation := I₁ }⟩

/-- For finite modules, essential injective monomorphisms and left-minimal
injective monomorphisms are equivalent. -/
theorem finiteDimensionalModule_isEssentialMono_iff_isLeftMinimal
    {M I : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    [Injective I] (f : M ⟶ I) [Mono f] :
    IsEssentialMono f ↔ IsLeftMinimal f :=
  isEssentialMono_iff_isLeftMinimal f fun e hmono ↦ by
    letI : Mono e := hmono
    exact isIso_of_mono_finiteDimensionalModule_endo I e

end MagnitudeConjecture.CoveringHom
