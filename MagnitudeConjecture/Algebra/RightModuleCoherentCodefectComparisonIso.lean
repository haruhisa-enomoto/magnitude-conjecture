import MagnitudeConjecture.Algebra.RightModuleCoherentCodefectComparisonEquiv

/-!
# The reverse coherent dual of an exact covariant defect

The descended reverse comparison is pointwise bijective.  Thus the reverse
coherent dual of an exact covariant defect is naturally isomorphic to the
corresponding contravariant defect.
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
variable [HasExt.{u} (S.FiniteCovariantFunctor)]

private abbrev reverseComparisonSourceMap
    (K : ShortComplex (FG (A := A))) :=
  S.finiteContravariantFunctorInclusion.map
    (S.finiteRestrictedContravariantRepresentableMap K.g)

/-- The descended reverse comparison agrees with the quotient equivalence
after the cokernel projection. -/
theorem finiteContravariantCokernelToCoherentCodual_π_app_apply
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategory) (f : (S.fgObj X).obj ⟶ K.X₃.obj) :
    (S.finiteContravariantCokernelToCoherentCodual hK).app (Opposite.op X)
        ((cokernel.π (reverseComparisonSourceMap S K)).app
          (Opposite.op X) f) =
      S.finiteContravariantRepresentableToCoherentCodualLinear hK X f := by
  have h := congrArg (fun t ↦ t.app (Opposite.op X))
    (cokernel.π_desc (reverseComparisonSourceMap S K)
      (S.finiteContravariantRepresentableToCoherentCodual hK)
      (S.finiteContravariantRepresentableToCoherentCodual_comp_eq_zero hK))
  exact ConcreteCategory.congr_hom h f

/-- Every component of the descended reverse comparison is surjective. -/
theorem finiteContravariantCokernelToCoherentCodual_app_surjective
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategoryᵒᵖ) :
    Function.Surjective
      ((S.finiteContravariantCokernelToCoherentCodual hK).app X) := by
  intro z
  let e := S.finiteContravariantPresentationToCoherentCodualLinearEquiv
    hK X.unop
  obtain ⟨q, hq⟩ := e.surjective z
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨(cokernel.π (reverseComparisonSourceMap S K)).app X f, ?_⟩
  rw [S.finiteContravariantCokernelToCoherentCodual_π_app_apply]
  exact (S.finiteContravariantPresentationToCoherentCodualLinearEquiv_mk
    hK X.unop f).symm.trans hq

/-- Every component of the descended reverse comparison is injective. -/
theorem finiteContravariantCokernelToCoherentCodual_app_injective
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategoryᵒᵖ) :
    Function.Injective
      ((S.finiteContravariantCokernelToCoherentCodual hK).app X) := by
  let p := cokernel.π (reverseComparisonSourceMap S K)
  have hpSurjective : Function.Surjective (p.app X) := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  intro y z hyz
  obtain ⟨f, rfl⟩ := hpSurjective y
  obtain ⟨g, rfl⟩ := hpSurjective z
  change ((S.fgObj X.unop).obj ⟶ K.X₃.obj) at f g
  let e := S.finiteContravariantPresentationToCoherentCodualLinearEquiv
    hK X.unop
  have he : e (Submodule.Quotient.mk f) =
      e (Submodule.Quotient.mk g) := by
    dsimp only [e]
    rw [S.finiteContravariantPresentationToCoherentCodualLinearEquiv_mk,
      S.finiteContravariantPresentationToCoherentCodualLinearEquiv_mk,
      ← S.finiteContravariantCokernelToCoherentCodual_π_app_apply,
      ← S.finiteContravariantCokernelToCoherentCodual_π_app_apply]
    exact hyz
  have hq : (Submodule.Quotient.mk f :
      ((S.fgObj X.unop).obj ⟶ K.X₃.obj) ⧸
        S.finiteContravariantPresentationRange K X.unop) =
      Submodule.Quotient.mk g := e.injective he
  rw [Submodule.Quotient.eq] at hq
  obtain ⟨b, hb⟩ := hq
  let pX : ((S.fgObj X.unop).obj ⟶ K.X₃.obj) →ₗ[k]
      ((cokernel (reverseComparisonSourceMap S K)).obj X) := by
    exact (p.app X).hom
  change pX f = pX g
  rw [← sub_eq_zero, ← pX.map_sub]
  have hcondition := congrArg (fun t ↦ t.app X)
    (cokernel.condition (reverseComparisonSourceMap S K))
  have hbzero := ConcreteCategory.congr_hom hcondition b
  change pX (f - g) = 0
  rw [← hb]
  exact hbzero

/-- Each component of the descended reverse comparison is an isomorphism. -/
noncomputable instance finiteContravariantCokernelToCoherentCodual_app_isIso
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact)
    (X : S.IndecCategoryᵒᵖ) :
    IsIso ((S.finiteContravariantCokernelToCoherentCodual hK).app X) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  exact ⟨S.finiteContravariantCokernelToCoherentCodual_app_injective hK X,
    S.finiteContravariantCokernelToCoherentCodual_app_surjective hK X⟩

/-- The ambient cokernel of the contravariant presentation is the reverse
coherent dual. -/
def finiteContravariantCokernelCoherentCodualIso
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    cokernel (reverseComparisonSourceMap S K) ≅
      S.coherentCodualObj (S.finiteCovariantDefect K) :=
  NatIso.ofComponents
    (fun X ↦ asIso
      ((S.finiteContravariantCokernelToCoherentCodual hK).app X))
    (fun a ↦ (S.finiteContravariantCokernelToCoherentCodual hK).naturality a)

/-- The reverse coherent dual of an exact covariant defect is naturally
isomorphic to the corresponding contravariant defect. -/
def finiteContravariantDefectCoherentCodualIso
    {K : ShortComplex (FG (A := A))} (hK : K.ShortExact) :
    S.finiteContravariantFunctorInclusion.obj
        (S.finiteContravariantDefect K) ≅
      S.coherentCodualObj (S.finiteCovariantDefect K) :=
  (PreservesCokernel.iso S.finiteContravariantFunctorInclusion
    (S.finiteRestrictedContravariantRepresentableMap K.g)).trans
      (S.finiteContravariantCokernelCoherentCodualIso hK)

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
