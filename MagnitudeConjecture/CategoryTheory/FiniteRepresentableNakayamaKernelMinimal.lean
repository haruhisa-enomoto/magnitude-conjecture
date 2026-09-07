import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaFull
import MagnitudeConjecture.CategoryTheory.FiniteRepresentableStableHomExt

/-!
# Minimality of the finite-representable Nakayama kernel

Minimality of the first projective syzygy presentation rules out nonzero
injective retracts of the kernel of its Nakayama differential.  This is the
categorical finite-functor analogue of the classical transpose argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.CoveringHom
namespace TwoStepMinimalFiniteRepresentablePresentation

universe u v

variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [CategoryTheory.Linear k C]
variable
  {hP : ∀ X : C, IsFiniteDimensionalModule (C := C) k
    (linearCoyonedaLinearModule (k := k) X)}
  (hI : ∀ X : C, IsFiniteDimensionalModule (C := C) k
    (dualLinearYonedaLinearModule (k := k) X))
variable
  {M : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}

/-- The abstract finite-projective Nakayama equivalence sends the actual
first differential to the displayed Nakayama differential. -/
theorem finiteRepresentableNakayamaMapLinearEquiv_differential
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    finiteRepresentableNakayamaMapLinearEquiv hP hI
        P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject
        P.augmentation.toFiniteRepresentablePresentation.matrixObject
        P.toTwoStepFiniteRepresentablePresentation.differential =
      P.nakayamaDifferential hI := by
  rw [← P.map_representingDifferential,
    finiteRepresentableNakayamaMapLinearEquiv_map]

/-- Minimality of the projective presentation rules out nonzero injective
retracts of its Nakayama kernel. -/
theorem nakayamaKernel_isZero_of_injective_retract
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    {I : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    [Injective I]
    (r : Retract I (P.nakayamaKernel hI)) : IsZero I := by
  let Q₁ :=
    P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject
  let Q₀ :=
    P.augmentation.toFiniteRepresentablePresentation.matrixObject
  let I₁ := (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj Q₁
  letI : IsSplitMono r.i := IsSplitMono.mk'
    { retraction := r.r
      id := r.retract }
  let j : I ⟶ I₁ := r.i ≫ kernel.ι (P.nakayamaDifferential hI)
  letI : Mono j := by
    dsimp only [j]
    infer_instance
  let s : I₁ ⟶ I := Injective.factorThru (𝟙 I) j
  have hjs : j ≫ s = 𝟙 I := Injective.comp_factorThru (𝟙 I) j
  let a : I₁ ⟶ I₁ := s ≫ j
  let e : P.syzygyPresentation.source ⟶ P.syzygyPresentation.source :=
    finiteRepresentableNakayamaMapPreimage hP hI Q₁ Q₁ a
  have hnue : finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁ e = a :=
    finiteRepresentableNakayamaMap_preimage hP hI Q₁ Q₁ a
  have haj : a ≫ P.nakayamaDifferential hI = 0 := by
    dsimp only [a]
    rw [Category.assoc]
    have hjzero : j ≫ P.nakayamaDifferential hI = 0 := by
      dsimp only [j]
      rw [Category.assoc, kernel.condition, comp_zero]
    rw [hjzero, comp_zero]
  have hed : e ≫ P.toTwoStepFiniteRepresentablePresentation.differential = 0 := by
    apply (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₀).injective
    rw [finiteRepresentableNakayamaMapLinearEquiv_comp, hnue,
      P.finiteRepresentableNakayamaMapLinearEquiv_differential hI,
      haj, map_zero]
  have haa : a ≫ a = a := by
    dsimp only [a]
    rw [Category.assoc, ← Category.assoc j s j, hjs,
      Category.id_comp]
  have hee : e ≫ e = e := by
    apply (finiteRepresentableNakayamaMapLinearEquiv hP hI Q₁ Q₁).injective
    rw [finiteRepresentableNakayamaMapLinearEquiv_comp, hnue]
    exact haa
  let h : P.syzygyPresentation.source ⟶
      P.syzygyPresentation.source := 𝟙 _ - e
  have hhcover : h ≫ P.syzygyPresentation.f = P.syzygyPresentation.f := by
    apply (cancel_mono (kernel.ι P.augmentation.f)).1
    change h ≫ P.toTwoStepFiniteRepresentablePresentation.differential =
      P.toTwoStepFiniteRepresentablePresentation.differential
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
    rw [← hnue, hezero, map_zero]
  have hja : j ≫ a = j := by
    dsimp only [a]
    rw [← Category.assoc, hjs, Category.id_comp]
  have hjzero : j = 0 := by
    calc
      j = j ≫ a := hja.symm
      _ = 0 := by rw [hazero, comp_zero]
  exact IsZero.of_mono_eq_zero j hjzero

end TwoStepMinimalFiniteRepresentablePresentation
end MagnitudeConjecture.CoveringHom
