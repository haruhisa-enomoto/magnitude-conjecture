import MagnitudeConjecture.Algebra.RightModuleCoherentDefectComparisonEquiv

/-!
# The coherent dual of an exact contravariant defect

The descended comparison is pointwise bijective, hence a natural
isomorphism.  Composing with preservation of the cokernel by the finite
functor-category inclusion identifies the coherent dual of an exact
contravariant defect with its covariant defect.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open QuotientSubmoduleEquidistribution
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)
variable [HasExt.{u} (FG (A := A))]
variable [HasExt.{u} (S.FiniteContravariantFunctor)]

private abbrev comparisonSourceMap
    (K : ShortComplex (FG (A := A))) :=
  S.finiteCovariantFunctorInclusion.map
    (S.finiteRestrictedCovariantRepresentableMap K.f)

/-- The descended comparison agrees with the quotient equivalence after
the cokernel projection. -/
theorem finiteCovariantCokernelToCoherentDual_π_app_apply
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) (f : K.X₁.obj ⟶ (S.fgObj X).obj) :
    (S.finiteCovariantCokernelToCoherentDual hK).app X
        ((cokernel.π (comparisonSourceMap S K)).app X f) =
      S.finiteCovariantRepresentableToCoherentDualLinear hK X f := by
  have h := congrArg (fun t ↦ t.app X)
    (cokernel.π_desc (comparisonSourceMap S K)
      (S.finiteCovariantRepresentableToCoherentDual hK)
      (S.finiteCovariantRepresentableToCoherentDual_comp_eq_zero hK))
  exact ConcreteCategory.congr_hom h f

/-- Every component of the descended comparison is surjective. -/
theorem finiteCovariantCokernelToCoherentDual_app_surjective
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) :
    Function.Surjective
      ((S.finiteCovariantCokernelToCoherentDual hK).app X) := by
  intro z
  let e := S.finiteCovariantPresentationToCoherentDualLinearEquiv hK X
  obtain ⟨q, hq⟩ := e.surjective z
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨(cokernel.π (comparisonSourceMap S K)).app X f, ?_⟩
  rw [S.finiteCovariantCokernelToCoherentDual_π_app_apply]
  exact (S.finiteCovariantPresentationToCoherentDualLinearEquiv_mk
    hK X f).symm.trans hq

/-- Every component of the descended comparison is injective. -/
theorem finiteCovariantCokernelToCoherentDual_app_injective
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) :
    Function.Injective
      ((S.finiteCovariantCokernelToCoherentDual hK).app X) := by
  let p := cokernel.π (comparisonSourceMap S K)
  have hpSurjective : Function.Surjective (p.app X) := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  intro y z hyz
  obtain ⟨f, rfl⟩ := hpSurjective y
  obtain ⟨g, rfl⟩ := hpSurjective z
  change (K.X₁.obj ⟶ (S.fgObj X).obj) at f g
  let e := S.finiteCovariantPresentationToCoherentDualLinearEquiv hK X
  have he : e (Submodule.Quotient.mk f) =
      e (Submodule.Quotient.mk g) := by
    dsimp only [e]
    rw [S.finiteCovariantPresentationToCoherentDualLinearEquiv_mk,
      S.finiteCovariantPresentationToCoherentDualLinearEquiv_mk,
      ← S.finiteCovariantCokernelToCoherentDual_π_app_apply,
      ← S.finiteCovariantCokernelToCoherentDual_π_app_apply]
    exact hyz
  have hq : (Submodule.Quotient.mk f :
      (K.X₁.obj ⟶ (S.fgObj X).obj) ⧸
        S.finiteCovariantPresentationRange K X) =
      Submodule.Quotient.mk g := e.injective he
  rw [Submodule.Quotient.eq] at hq
  obtain ⟨b, hb⟩ := hq
  let pX : (K.X₁.obj ⟶ (S.fgObj X).obj) →ₗ[k]
      ((cokernel (comparisonSourceMap S K)).obj X) := by
    exact (p.app X).hom
  change pX f = pX g
  rw [← sub_eq_zero, ← pX.map_sub]
  have hcondition := congrArg (fun t ↦ t.app X)
    (cokernel.condition (comparisonSourceMap S K))
  have hbzero := ConcreteCategory.congr_hom hcondition b
  change pX (f - g) = 0
  rw [← hb]
  exact hbzero

/-- Each component of the descended comparison is an isomorphism. -/
noncomputable instance finiteCovariantCokernelToCoherentDual_app_isIso
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) :
    IsIso ((S.finiteCovariantCokernelToCoherentDual hK).app X) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact ⟨S.finiteCovariantCokernelToCoherentDual_app_injective hK X,
    S.finiteCovariantCokernelToCoherentDual_app_surjective hK X⟩

/-- The ambient cokernel of the covariant presentation is the coherent
dual. -/
def finiteCovariantCokernelCoherentDualIso
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    cokernel (comparisonSourceMap S K) ≅
      S.coherentDualObj (S.finiteContravariantDefect K) :=
  NatIso.ofComponents
    (fun X ↦ asIso ((S.finiteCovariantCokernelToCoherentDual hK).app X))
    (fun a ↦ (S.finiteCovariantCokernelToCoherentDual hK).naturality a)

/-- Auslander's pointwise coherent dual of an exact contravariant defect is
naturally isomorphic to the corresponding covariant defect. -/
def finiteCovariantDefectCoherentDualIso
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    S.finiteCovariantFunctorInclusion.obj (S.finiteCovariantDefect K) ≅
      S.coherentDualObj (S.finiteContravariantDefect K) :=
  (PreservesCokernel.iso S.finiteCovariantFunctorInclusion
    (S.finiteRestrictedCovariantRepresentableMap K.f)).trans
      (S.finiteCovariantCokernelCoherentDualIso hK)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
