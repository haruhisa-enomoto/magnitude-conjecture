import MagnitudeConjecture.Algebra.RightModuleProjectiveStableCovariantUniserial

/-!
# Full faithfulness of restricted covariant Yoneda

This packages the finite-density Yoneda results as the linear equivalence

`Hom(X,B) ≃ Nat(Hom(B,-), Hom(X,-))`

when `X` is a chosen indecomposable and `B` is any finitely generated module.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton

universe u

variable {k A : Type u} [Field k]
variable [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ]
variable (S : RightModule.FiniteIndecomposableSkeleton k A)

/-- Restricted covariant Yoneda is faithful on all finitely generated
modules. -/
theorem finiteRestrictedCovariantRepresentableFunctor_faithful :
    S.finiteRestrictedCovariantRepresentableFunctor.Faithful := by
  let F := S.finiteRestrictedCovariantRepresentableFunctor
  refine MagnitudeConjecture.CategoryTheory.functor_faithful_of_finite_coordinates
    (C := (RightModule.FinitelyGeneratedCategory A)ᵒᵖ)
    (D := CoveringHom.FiniteDimensionalModuleCategory
      (C := S.IndecCategory) k)
    (P := S.IndecCategory) (fun i ↦ Opposite.op (S.fgObj i)) F ?_ ?_
  · intro X
    letI : Module.Finite k X.unop :=
      RightModule.finite_over_field_of_finitelyGenerated k A X.unop
    obtain ⟨d⟩ := finiteIndecomposableDecomposition_fgModule_exists
      (k := k) X.unop
    have hdense (j : Fin d.n) :
        ∃ i : S.IndecCategory, Nonempty (d.summand j ≅ S.fgObj i) :=
      S.fgObj_complete (d.summand j) (d.indecomposable j)
    choose i e using hdense
    let chosen : Fin d.n → RightModule.FinitelyGeneratedCategory A :=
      fun j ↦ S.fgObj (i j)
    let eModule : X.unop ≅ ⨁ chosen :=
      d.isoBiproduct ≪≫ biproduct.mapIso (fun j ↦ Classical.choice (e j))
    let eOpposite : X ≅ ⨁ fun j ↦ Opposite.op (chosen j) :=
      eModule.op.symm ≪≫
        (biproduct.isoCoproduct chosen).op.symm ≪≫
        opCoproductIsoProduct chosen ≪≫
        (biproduct.isoProduct (fun j ↦ Opposite.op (chosen j))).symm
    exact ⟨d.n, i, ⟨eOpposite.symm⟩⟩
  · intro i j f g hfg
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    have happ := congrArg
      (fun q ↦ q.hom.hom.app i (𝟙 (S.inclusion.obj i))) hfg
    exact happ

/-- The map on Hom spaces induced by restricted covariant Yoneda. -/
def finiteRestrictedCovariantRepresentableHomLinear
    (B C : RightModule.FinitelyGeneratedCategory A) :
    (C ⟶ B) →ₗ[k]
      (S.finiteRestrictedCovariantRepresentable B ⟶
        S.finiteRestrictedCovariantRepresentable C) where
  toFun := S.finiteRestrictedCovariantRepresentableMap
  map_add' := S.finiteRestrictedCovariantRepresentableMap_add
  map_smul' := by
    intro r f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    let h' : B.obj ⟶ S.inclusion.obj X := h
    change (r • f.hom) ≫ h' = r • (f.hom ≫ h')
    rw [CategoryTheory.Linear.smul_comp]

/-- Restricted covariant Yoneda is a linear equivalence from maps out of a
chosen indecomposable to maps between the corresponding representables. -/
def finiteRestrictedCovariantRepresentableHomLinearEquiv
    (B : RightModule.FinitelyGeneratedCategory A) (X : S.IndecCategory) :
    (S.fgObj X ⟶ B) ≃ₗ[k]
      (S.finiteRestrictedCovariantRepresentable B ⟶
        S.finiteRestrictedCovariantRepresentable (S.fgObj X)) :=
  LinearEquiv.ofBijective
    (S.finiteRestrictedCovariantRepresentableHomLinear B (S.fgObj X))
    ⟨by
        intro f g hfg
        let F := S.finiteRestrictedCovariantRepresentableFunctor
        letI : F.Faithful := S.finiteRestrictedCovariantRepresentableFunctor_faithful
        have hop : f.op = g.op := F.map_injective hfg
        exact Quiver.Hom.op_inj hop,
      fun p ↦ S.exists_eq_finiteRestrictedCovariantRepresentableMap
        B (S.fgObj X) p⟩

@[simp]
theorem finiteRestrictedCovariantRepresentableHomLinearEquiv_apply
    (B : RightModule.FinitelyGeneratedCategory A) (X : S.IndecCategory)
    (f : S.fgObj X ⟶ B) :
    S.finiteRestrictedCovariantRepresentableHomLinearEquiv B X f =
      S.finiteRestrictedCovariantRepresentableMap f :=
  rfl

/-- Ambient and finitely generated Hom spaces agree linearly. -/
def covariantFgHomLinearEquiv
    (B C : RightModule.FinitelyGeneratedCategory A) :
    (B.obj ⟶ C.obj) ≃ₗ[k] (B ⟶ C) where
  toFun f := ObjectProperty.homMk f
  invFun f := f.hom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Ambient form of the restricted covariant-Yoneda Hom equivalence. -/
def ambientFiniteRestrictedCovariantRepresentableHomLinearEquiv
    (B : RightModule.FinitelyGeneratedCategory A) (X : S.IndecCategory) :
    ((S.fgObj X).obj ⟶ B.obj) ≃ₗ[k]
      (S.finiteRestrictedCovariantRepresentable B ⟶
        S.finiteRestrictedCovariantRepresentable (S.fgObj X)) :=
  (covariantFgHomLinearEquiv (k := k) (S.fgObj X) B).trans
    (S.finiteRestrictedCovariantRepresentableHomLinearEquiv B X)

@[simp]
theorem ambientFiniteRestrictedCovariantRepresentableHomLinearEquiv_apply
    (B : RightModule.FinitelyGeneratedCategory A) (X : S.IndecCategory)
    (f : (S.fgObj X).obj ⟶ B.obj) :
    S.ambientFiniteRestrictedCovariantRepresentableHomLinearEquiv B X f =
      S.finiteRestrictedCovariantRepresentableMap
        (ObjectProperty.homMk f) :=
  rfl

end MagnitudeConjecture.RightModule.FiniteIndecomposableSkeleton
