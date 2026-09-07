import MagnitudeConjecture.Algebra.BiserialFiberKernelStructure
import MagnitudeConjecture.Algebra.BiserialModule

/-!
# Quotient branches in the biserial fiber-kernel obstruction

The first Pogorzały--Skowroński obstruction starts with two disjoint simple
submodules `S,T ⊆ X`, forms the branches `X/S` and `X/T`, and maps both to a
common quotient `X/J`.  This file identifies their first two socle layers and
packages the resulting fiber kernel without adding abstract branch data.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.RightModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
variable [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ]

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- A simple submodule disjoint from the denominator remains simple in the
quotient. -/
theorem isSimpleModule_map_quotientMk_of_inf_eq_bot
    (X : FinitelyGeneratedCategory A)
    (S T : Submodule Aᵐᵒᵖ X) (hinf : S ⊓ T = ⊥)
    (hT : IsSimpleModule Aᵐᵒᵖ T) :
    IsSimpleModule Aᵐᵒᵖ (T.map S.mkQ) := by
  let f : T →ₗ[Aᵐᵒᵖ] quotientFGObj X S :=
    IsBiserialModule.submoduleToQuotientLinearMap T S
  have hf : Function.Injective f :=
    IsBiserialModule.submoduleToQuotientLinearMap_injective_of_inf_eq_bot
      T S (by simpa [inf_comm] using hinf)
  have hrange : LinearMap.range f = T.map S.mkQ := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  rw [← hrange]
  letI : IsSimpleModule Aᵐᵒᵖ T := hT
  exact IsSimpleModule.congr (LinearEquiv.ofInjective f hf).symm

omit [IsNoetherianRing Aᵐᵒᵖ] in
/-- In a uniserial quotient `X/S`, the image of a disjoint simple submodule
`T` is the whole socle. -/
theorem moduleSocle_quotient_eq_sup_map
    (X : FinitelyGeneratedCategory A)
    (S T : Submodule Aᵐᵒᵖ X) (hinf : S ⊓ T = ⊥)
    (hT : IsSimpleModule Aᵐᵒᵖ T)
    (hquot : IsUniserialModule Aᵐᵒᵖ (quotientFGObj X S)) :
    moduleSocle Aᵐᵒᵖ (quotientFGObj X S) =
      (S ⊔ T).map S.mkQ := by
  rw [Submodule.map_sup, S.mkQ_map_self, bot_sup_eq]
  exact hquot.moduleSocle_eq_of_simple_submodule (T.map S.mkQ)
    (isSimpleModule_map_quotientMk_of_inf_eq_bot X S T hinf hT)

/-- The disjoint simple submodule is canonically equivalent to the socle of
the corresponding uniserial quotient branch. -/
def quotientBranchSocleLinearEquiv
    (X : FinitelyGeneratedCategory A)
    (S T : Submodule Aᵐᵒᵖ X) (hinf : S ⊓ T = ⊥)
    (hT : IsSimpleModule Aᵐᵒᵖ T)
    (hquot : IsUniserialModule Aᵐᵒᵖ (quotientFGObj X S)) :
    T ≃ₗ[Aᵐᵒᵖ] moduleSocle Aᵐᵒᵖ (quotientFGObj X S) := by
  let f : T →ₗ[Aᵐᵒᵖ] quotientFGObj X S :=
    IsBiserialModule.submoduleToQuotientLinearMap T S
  have hf : Function.Injective f :=
    IsBiserialModule.submoduleToQuotientLinearMap_injective_of_inf_eq_bot
      T S (by simpa [inf_comm] using hinf)
  have hrange : LinearMap.range f = T.map S.mkQ := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have heq : LinearMap.range f =
      moduleSocle Aᵐᵒᵖ (quotientFGObj X S) := by
    rw [hrange, moduleSocle_quotient_eq_sup_map X S T hinf hT hquot,
      Submodule.map_sup, S.mkQ_map_self, bot_sup_eq]
  exact (LinearEquiv.ofInjective f hf).trans
    (LinearEquiv.ofEq _ _ heq)

/-- Quotienting `X/S` by the image of a larger layer `R` is canonically
equivalent to `X/R`. -/
def nestedQuotientBySocleLinearEquiv
    (X : FinitelyGeneratedCategory A)
    (S R : Submodule Aᵐᵒᵖ X) (hSR : S ≤ R)
    (hsocle : moduleSocle Aᵐᵒᵖ (quotientFGObj X S) =
      R.map S.mkQ) :
    quotientFGObj (quotientFGObj X S)
        (moduleSocle Aᵐᵒᵖ (quotientFGObj X S)) ≃ₗ[Aᵐᵒᵖ]
      quotientFGObj X R :=
  (Submodule.quotEquivOfEq _ _ hsocle).trans
    (Submodule.quotientQuotientEquivQuotient S R hSR)

/-- The common middle layer of the two quotient branches. -/
def quotientBranchCommonNextSocleFGObj
    (X : FinitelyGeneratedCategory A) (R : Submodule Aᵐᵒᵖ X) :
    FinitelyGeneratedCategory A :=
  submoduleFGObj (quotientFGObj X R)
    (moduleSocle Aᵐᵒᵖ (quotientFGObj X R))

/-- The next socle layer of `X/S` is canonically the socle of `X/R` when
the first socle of `X/S` is the image of `R`. -/
def quotientBranchNextSocleLinearEquiv
    (X : FinitelyGeneratedCategory A)
    (S R : Submodule Aᵐᵒᵖ X) (hSR : S ≤ R)
    (hsocle : moduleSocle Aᵐᵒᵖ (quotientFGObj X S) =
      R.map S.mkQ) :
    moduleSocle Aᵐᵒᵖ
        (quotientFGObj (quotientFGObj X S)
          (moduleSocle Aᵐᵒᵖ (quotientFGObj X S))) ≃ₗ[Aᵐᵒᵖ]
      quotientBranchCommonNextSocleFGObj X R :=
  let q := nestedQuotientBySocleLinearEquiv X S R hSR hsocle
  (q.submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (map_moduleSocle_eq_of_linearEquiv q))

/-- The literal fiber-kernel module on the two quotient branches `X/S` and
`X/T` over `X/J`. -/
def quotientBranchFiberKernelFGObj
    (X : FinitelyGeneratedCategory A)
    (S T J : Submodule Aᵐᵒᵖ X) (hSTJ : S ⊔ T ≤ J) :
    FinitelyGeneratedCategory A :=
  fiberKernelFGObj
    (quotientFGObj X S) (quotientFGObj X T) (quotientFGObj X J)
    (quotientFGMapQ X S J (le_sup_left.trans hSTJ))
    (quotientFGMapQ X T J (le_sup_right.trans hSTJ))

/-- The preimage of the product of the two branch radicals in the literal
quotient-branch fiber kernel. -/
def quotientBranchFiberKernelRadicalPreimage
    (X : FinitelyGeneratedCategory A)
    (S T J : Submodule Aᵐᵒᵖ X) (hSTJ : S ⊔ T ≤ J) :
    Submodule Aᵐᵒᵖ (quotientBranchFiberKernelFGObj X S T J hSTJ) :=
  fiberKernelRadicalPreimage
    (quotientFGObj X S) (quotientFGObj X T) (quotientFGObj X J)
    (quotientFGMapQ X S J (le_sup_left.trans hSTJ))
    (quotientFGMapQ X T J (le_sup_right.trans hSTJ))

end MagnitudeConjecture.RightModule
