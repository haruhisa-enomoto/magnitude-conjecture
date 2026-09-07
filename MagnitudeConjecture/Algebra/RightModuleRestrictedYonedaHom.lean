import MagnitudeConjecture.Algebra.RightModuleStableRepresentableSocleInduction

/-!
# Full faithfulness of restricted Yoneda on a finite module skeleton

For a finitely generated module `B` and a chosen indecomposable `X`, this
file packages the already proved fullness and faithfulness statements as the
linear equivalence

`Hom(B, X) ≃ Nat(Hom(-, B), Hom(-, X))`.

This is the Yoneda comparison needed to turn Auslander's presentation
quotient in the functor category into the ordinary module presentation
quotient.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k] [IsAlgClosed k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Forgetting and rebundling finite generation does not change a Hom
space. -/
def fgHomLinearEquiv (B C : RightModule.FinitelyGeneratedCategory A) :
    (B.obj ⟶ C.obj) ≃ₗ[k] (B ⟶ C) where
  toFun f := ObjectProperty.homMk f
  invFun f := f.hom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The map on Hom spaces induced by restricted contravariant Yoneda. -/
def finiteRestrictedContravariantRepresentableHomLinear
    (B C : RightModule.FinitelyGeneratedCategory A) :
    (B ⟶ C) →ₗ[k]
      (S.finiteRestrictedContravariantRepresentable B ⟶
        S.finiteRestrictedContravariantRepresentable C) where
  toFun := S.finiteRestrictedContravariantRepresentableMap
  map_add' := S.finiteRestrictedContravariantRepresentableMap_add
  map_smul' := by
    intro r f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    rfl

/-- Restricted contravariant Yoneda is a linear equivalence on maps from an
arbitrary finitely generated module to a chosen indecomposable. -/
def finiteRestrictedContravariantRepresentableHomLinearEquiv
    (B : RightModule.FinitelyGeneratedCategory A) (X : S.IndecCategory) :
    (B ⟶ S.fgObj X) ≃ₗ[k]
      (S.finiteRestrictedContravariantRepresentable B ⟶
        S.finiteRestrictedContravariantRepresentable (S.fgObj X)) :=
  LinearEquiv.ofBijective
    (S.finiteRestrictedContravariantRepresentableHomLinear B (S.fgObj X))
    ⟨S.finiteRestrictedContravariantRepresentableMap_injective B (S.fgObj X),
      fun p ↦ S.exists_eq_finiteRestrictedContravariantRepresentableMap_to_fgObj
        B X p⟩

/-- Ambient module maps to a chosen indecomposable are likewise identified
with maps between the corresponding restricted representables. -/
def ambientFiniteRestrictedContravariantRepresentableHomLinearEquiv
    (B : RightModule.FinitelyGeneratedCategory A) (X : S.IndecCategory) :
    (B.obj ⟶ (S.fgObj X).obj) ≃ₗ[k]
      (S.finiteRestrictedContravariantRepresentable B ⟶
        S.finiteRestrictedContravariantRepresentable (S.fgObj X)) :=
  (fgHomLinearEquiv (k := k) B (S.fgObj X)).trans
    (S.finiteRestrictedContravariantRepresentableHomLinearEquiv B X)

@[simp]
theorem ambientFiniteRestrictedContravariantRepresentableHomLinearEquiv_apply
    (B : RightModule.FinitelyGeneratedCategory A) (X : S.IndecCategory)
    (f : B.obj ⟶ (S.fgObj X).obj) :
    S.ambientFiniteRestrictedContravariantRepresentableHomLinearEquiv B X f =
      S.finiteRestrictedContravariantRepresentableMap
        (ObjectProperty.homMk f) :=
  rfl

@[simp]
theorem finiteRestrictedContravariantRepresentableHomLinearEquiv_apply
    (B : RightModule.FinitelyGeneratedCategory A) (X : S.IndecCategory)
    (f : B ⟶ S.fgObj X) :
    S.finiteRestrictedContravariantRepresentableHomLinearEquiv B X f =
      S.finiteRestrictedContravariantRepresentableMap f :=
  rfl

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
