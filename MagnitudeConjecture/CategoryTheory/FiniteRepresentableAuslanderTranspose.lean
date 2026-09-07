import MagnitudeConjecture.CategoryTheory.FiniteRepresentableNakayamaInjective
import MagnitudeConjecture.CategoryTheory.FiniteDimensionalModuleProjectiveCoordinates
import MagnitudeConjecture.CategoryTheory.InjectivePresentationExt
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# The finite-functor-category Auslander transpose copresentation

For a literal two-step finite-representable presentation, applying the
finite-matrix Nakayama functor produces a map between injectives.  Its kernel
therefore has a concrete short injective presentation, and degree-one Ext is
the corresponding quotient of a Hom space.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.CoveringHom
namespace TwoStepMinimalFiniteRepresentablePresentation

universe u v w

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

/-- The literal representing-object matrix of the first differential. -/
abbrev representingDifferential
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject ⟶
      P.augmentation.toFiniteRepresentablePresentation.matrixObject :=
  P.toTwoStepFiniteRepresentablePresentation.matrixDifferential

/-- The first differential after applying the finite-matrix Nakayama functor. -/
abbrev nakayamaDifferential
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
        P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject ⟶
      (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
        P.augmentation.toFiniteRepresentablePresentation.matrixObject :=
  (finiteNakayamaRepresentableSumFunctor (k := k) hI).map
    (P.representingDifferential)

/-- The presentation-dependent Auslander--Reiten translate object. -/
abbrev nakayamaKernel
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
  kernel (P.nakayamaDifferential hI)

/-- The inclusion of the Nakayama kernel in the first Nakayama projective,
packaged as an injective presentation. -/
def nakayamaInjectivePresentation
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    InjectivePresentation (P.nakayamaKernel hI) where
  J := (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
    P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject
  injective := finiteNakayamaRepresentableSum_injective hI _
  f := kernel.ι (P.nakayamaDifferential hI)
  mono := inferInstance

/-- The quotient of the first Nakayama projective by the Nakayama kernel. -/
abbrev nakayamaCokernel
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k :=
  cokernel (kernel.ι (P.nakayamaDifferential hI))

/-- The quotient map from the first Nakayama projective. -/
abbrev nakayamaCokernelπ
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
        P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject ⟶
      P.nakayamaCokernel hI :=
  cokernel.π (kernel.ι (P.nakayamaDifferential hI))

/-- The Nakayama differential descends to the quotient by its kernel. -/
def nakayamaCokernelι
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    P.nakayamaCokernel hI ⟶
      (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
        P.augmentation.toFiniteRepresentablePresentation.matrixObject :=
  cokernel.desc (kernel.ι (P.nakayamaDifferential hI))
    (P.nakayamaDifferential hI)
    (kernel.condition (P.nakayamaDifferential hI))

@[simp]
theorem nakayamaCokernelπ_comp_ι
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    P.nakayamaCokernelπ hI ≫ P.nakayamaCokernelι hI =
      P.nakayamaDifferential hI := by
  exact cokernel.π_desc _ _ _

instance nakayamaCokernelι_mono
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    Mono (P.nakayamaCokernelι hI) := by
  exact (ShortComplex.exact_kernel
    (P.nakayamaDifferential hI)).mono_cokernelDesc

/-- The short exact sequence computing Ext from the Nakayama kernel. -/
abbrev nakayamaExtShortComplex
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M) :
    ShortComplex
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :=
  (P.nakayamaInjectivePresentation hI).shortComplex

/-- Coboundaries in the concrete injective presentation. -/
abbrev nakayamaExtPresentationRange
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    Submodule k (Y ⟶ P.nakayamaCokernel hI) :=
  InjectivePresentationExt.presentationRange (k := k)
    (P.nakayamaExtShortComplex hI) Y

@[simp]
theorem mem_nakayamaExtPresentationRange_iff
    [HasExt.{w}
      (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)
    (f : Y ⟶ P.nakayamaCokernel hI) :
    f ∈ P.nakayamaExtPresentationRange hI Y ↔
      ∃ a : Y ⟶
          (finiteNakayamaRepresentableSumFunctor (k := k) hI).obj
            P.syzygyPresentation.toFiniteRepresentablePresentation.matrixObject,
        a ≫ P.nakayamaCokernelπ hI = f := by
  exact InjectivePresentationExt.mem_presentationRange_iff
    (k := k) (P.nakayamaExtShortComplex hI) Y f

variable [HasExt.{w}
  (FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k)]

/-- The concrete quotient presentation of degree-one Ext. -/
def nakayamaExtOneQuotientLinearEquiv
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    (Y : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k) :
    ((Y ⟶ P.nakayamaCokernel hI) ⧸
        P.nakayamaExtPresentationRange hI Y) ≃ₗ[k]
      Ext.{w} Y (P.nakayamaKernel hI) 1 :=
  InjectivePresentationExt.quotientLinearEquivExtOne (k := k)
    (P.nakayamaInjectivePresentation hI).shortExact_shortComplex Y

/-- Pullback on the concrete Ext presentation quotient. -/
abbrev nakayamaPrecompQuotient
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    {Y Z : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (g : Y ⟶ Z) :
    ((Z ⟶ P.nakayamaCokernel hI) ⧸
        P.nakayamaExtPresentationRange hI Z) →ₗ[k]
      ((Y ⟶ P.nakayamaCokernel hI) ⧸
        P.nakayamaExtPresentationRange hI Y) :=
  InjectivePresentationExt.precompQuotient (k := k)
    (P.nakayamaExtShortComplex hI) g

/-- Inverse-form pullback naturality of the Ext quotient. -/
theorem nakayamaExtOneQuotientLinearEquiv_symm_pullback
    (P : TwoStepMinimalFiniteRepresentablePresentation hP M)
    {Y Z : FiniteDimensionalModuleCategory.{u, v, v, v} (C := C) k}
    (g : Y ⟶ Z) (xi : Ext.{w} Z (P.nakayamaKernel hI) 1) :
    (P.nakayamaExtOneQuotientLinearEquiv hI Y).symm
        ((Ext.mk₀ g).comp xi (zero_add 1)) =
      P.nakayamaPrecompQuotient hI g
        ((P.nakayamaExtOneQuotientLinearEquiv hI Z).symm xi) := by
  apply (P.nakayamaExtOneQuotientLinearEquiv hI Y).injective
  rw [LinearEquiv.apply_symm_apply]
  symm
  have h :
      P.nakayamaExtOneQuotientLinearEquiv hI Y
          (P.nakayamaPrecompQuotient hI g
            ((P.nakayamaExtOneQuotientLinearEquiv hI Z).symm xi)) =
        InjectivePresentationExt.pullbackLinear (k := k)
          (P.nakayamaExtShortComplex hI) g
          (P.nakayamaExtOneQuotientLinearEquiv hI Z
            ((P.nakayamaExtOneQuotientLinearEquiv hI Z).symm xi)) :=
    InjectivePresentationExt.quotientLinearEquivExtOne_precompQuotient
      (k := k)
      (P.nakayamaInjectivePresentation hI).shortExact_shortComplex g
      ((P.nakayamaExtOneQuotientLinearEquiv hI Z).symm xi)
  rw [LinearEquiv.apply_symm_apply] at h
  simpa [InjectivePresentationExt.pullbackLinear] using h

end TwoStepMinimalFiniteRepresentablePresentation
end MagnitudeConjecture.CoveringHom
